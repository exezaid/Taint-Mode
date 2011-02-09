{-# OPTIONS -fallow-undecidable-instances -fglasgow-exts -farrows #-}

module FlowArrowRef
( FlowArrowRef
, ArrowRef
, Privilege
, tagRef
, declassifyRef
, certifyRef
, certifyRefL
, equalA
, lowerA
, iterateA
, createRefA
, readRefA
, writeRefA
, forkRef
, atomicA
, runArrowRef
, fstPair
, sndPair 
, skipRef
, randomRRef
, idRef
, nullRef
, pairRight
, pairLeft
)
where

import Data.List as List
import Unification
import Lattice
import RLattice
import Control.Arrow
import Data.IORef
import SecureFlow
import RefOp 
import Control.Concurrent
import Control.Concurrent.STM
import Control.Monad.Fix
import Control.Monad.State
import System.Random
import Priv
import Control.Exception

data Constraint l = 
    LEQ l l | USERGEQ l | IS l l | GUARD l l | GSLEQL l l | GLLEQS l l
    deriving (Eq, Show)

data Flow l = Trans l l  
       deriving (Eq,Show)

-- Flow definition of (>>>)
flow_seq::Lattice l => Flow (SecType l) -> Flow (SecType l) 
                       -> ( Flow (SecType l)
                          , [Constraint (SecType l)]
                          , [(U (SecType l),U (SecType l))])
flow_seq (Trans s1 s2) (Trans s3 s4)= (Trans s1 s4, c,u)
  where
  (c,u) = seqFlow s2 s3

seqFlow s2 s3 =
  case (s2,s3) of
    (t1@(SecVar _), t2) -> if (hasVarSecType t2) 
                             then ([],[(Id t1,Id t2)])
                             else ([LEQ t1 t2], [])
    (SecHigh, t2) -> if (hasVarSecType t2)
                       then ([],[(Id SecHigh,Id t2)])
                       else ([LEQ SecHigh t2], [])
    (t1, t2@(SecVar _)) -> ([],[(Id t1, Id t2)])
    (SecLabel l1, SecLabel l2) -> seqFlowLabel l1 l2
    (SecRef t1 l1, SecRef t2 l2) -> let (cl,ul) = seqFlowLabel l1 l2 in
                                    if (hasVarSecType t2)
                                      then (cl, (Id t1,Id t2):ul)
                                      else ([LEQ t1 t2,LEQ t2 t1]++cl,ul)
    (SecPair t1 r1, SecPair t2 r2) -> let (ct,ut) = seqFlow t1 t2
                                          (cr,ur) = seqFlow r1 r2
                                      in (ct++cr,ut++ur)
    (SecEither t1 r1 l1, SecEither t2 r2 l2) -> let (cl,ul) = seqFlowLabel l1 l2
                                                    (ct,ut) = seqFlow t1 t2
                                                    (cr,ur) = seqFlow r1 r2
                                                in (cl++ct++cr,ul++ut++ur)
    (t1, SecHigh) -> ([LEQ t1 SecHigh], [])

seqFlowLabel l1 l2 =
  case (l1,l2) of
    (t1, t2@(LVar _)) -> ([],[(Id (SecLabel t1),Id (SecLabel t2))])
    (t1, t2@(Lab _)) -> ([LEQ (SecLabel t1) (SecLabel t2)], [])

-- Flow definition of first, second, and (***). 
flow_pair :: Lattice l => Flow (SecType l) -> Flow (SecType l) -> Flow (SecType l)
flow_pair (Trans s1 s2) (Trans s3 s4) = Trans (SecPair s1 s3) (SecPair s2 s4) 

-- Flow definition of (&&&). 
flow_diverge :: Lattice l => Flow (SecType l) -> Flow (SecType l) 
                             -> ( Flow (SecType l)
                                , [Constraint (SecType l)]
                                , [(U (SecType l), U (SecType l))])
flow_diverge (Trans s1 s2) (Trans s1' s2') =
  let (in_flow, cons, us) = meetInFlow s1 s1' in
  (Trans in_flow out_flow, cons, us)
  where
  out_flow = (SecPair s2 s2')

meetInFlow s1 s2 =
  case (s1,s2) of
    (t1@(SecVar _), t2@(SecVar _)) -> (t1, [], [(Id t1,Id t2)])
    (t1@(SecVar _), t2) -> if hasVarSecType t2
                             then (t1, [], [(Id t1,Id t2)])
                             else (t1, [LEQ t1 t2], [])
    (t1, t2@(SecVar _)) -> if hasVarSecType t1
                             then (t2, [], [(Id t1,Id t2)])
                             else (t2, [LEQ t2 t1], [])
    (SecHigh, t2) -> (t2, [], [])
    (t1, SecHigh) -> (t1, [], [])
    ((SecLabel l1), (SecLabel l2)) -> let (l' , cons, us) = meetInFlowLabel l1 l2 
                                      in (SecLabel l', cons, us)
    ((SecRef s1 l1), (SecRef s2 l2)) -> let (l', lcons, lus) = meetInFlowLabel l1 l2 
                                        in (SecRef s1 l', lcons, (Id s1,Id s2):lus)
    ((SecPair s1 t1), (SecPair s2 t2)) -> let (s', scons, sus) = meetInFlow s1 s2 
                                              (t', tcons, tus) = meetInFlow t1 t2 
                                          in (SecPair s' t', scons++tcons, sus++tus)
    ((SecEither s1 t1 l1), (SecEither s2 t2 l2)) -> let (s', scons, sus) = meetInFlow s1 s2
                                                        (t', tcons, tus) = meetInFlow t1 t2
                                                        (l', lcons, lus) = meetInFlowLabel l1 l2
                                                    in (SecEither s' t' l', scons++tcons++lcons, sus++tus++lus)

meetInFlowLabel k1 k2 =
  case (k1,k2) of
    (l1@(LVar _), l2@(LVar _)) -> (l1, [], [(Id (SecLabel l1),Id (SecLabel l2))])
    (l1@(LVar _), l2) -> (l1, [LEQ (SecLabel l1) (SecLabel l2)], [])
    (l1, l2@(LVar _)) -> (l2, [LEQ (SecLabel l2) (SecLabel l1)], [])
    ((Lab l1), (Lab l2)) -> (Lab (label_meet l1 l2), [], [])

-- Flow definition of left, right, and (+++). 
flow_either :: Lattice l => Flow (SecType l) -> Flow (SecType l) -> Flow (SecType l)
flow_either (Trans s1 s2) (Trans s3 s4) = Trans (SecEither s1 s3 (LVar "x0")) (SecEither s2 s4 (LVar "x0"))

-- Flow definition of (|||). 
flow_converge :: Lattice l => Flow (SecType l) -> Flow (SecType l) 
                              -> ( Flow (SecType l)
                                 , [(U (SecType l),U (SecType l))])
flow_converge (Trans s1 s2) (Trans s1' s2') =
  let l = (LVar "x0") in
  let s_out = (SecVar "x1") in 
  (Trans (SecEither s1 s1' l) s_out
  ,[(Id s_out, Tag (Join (Id s2) (Id s2')) (Id (SecLabel l)))])  

-- Make substitution pair for arrow computations. 
make_sub :: (Lattice l) => FlowArrowRef l a b c -> FlowArrowRef l a b' c' -> [SecType l]
              -> ([((SecType l),(SecType l))],[((SecType l), (SecType l))],[((SecType l), (SecType l))])
make_sub fa1 fa2 nvars = (r1,r2,r3)
 where
  t1 = extract_arrow fa1
  t2 = extract_arrow fa2
  len1 = length t1
  len2 = length t2
  result = zipWith renameVar (t1 ++ t2 ++ nvars) [0..]
  (r1,rt) = splitAt len1 result
  (r2,r3) = splitAt len2 rt
  
renameVar v n = case v of
                 (SecVar _) -> (v,(SecVar ('a':show n)))
                 (SecLabel (LVar _)) -> (v,(SecLabel (LVar ('a':show n))))

make_sub_partial fa idf nvars = (r1,r2,r3)
  where
  t1 = extract_arrow fa
  t2 = extract_flow idf
  len1 = length t1
  len2 = length t2
  result = zipWith renameVar (t1 ++ t2 ++ nvars) [0..]
  (r1,rt) = splitAt len1 result
  (r2,r3) = splitAt len2 rt
  
-- Gather all variables in a FlowArrowRef computation. 
extract_arrow :: Lattice l => FlowArrowRef l a b c -> [SecType l]
extract_arrow (FARef _ f _ _ u ) = total
 where
  fs = extract_flow f
  us = extract_uniset u
  total = (List.union us fs) 

extract_flow :: Lattice l => Flow (SecType l) -> [(SecType l)]
extract_flow (Trans s1 s2) = (extractSecVar s1) `List.union` (extractSecVar s2)

extract_uniset :: Lattice l => [(U (SecType l),U (SecType l))] -> [(SecType l)]
extract_uniset u = foldl List.union [] (map (\(u1,u2) -> (extractUVar u1) `List.union` (extractUVar u2)) u)

extractUVar :: Lattice l => U (SecType l) -> [SecType l]
extractUVar = propLeafU extractSecVar List.union

extractSecVar :: Lattice l => SecType l -> [SecType l]
extractSecVar v@(SecVar _) = [v]
extractSecVar (SecHigh) = []
extractSecVar (SecLabel (Lab _)) = []
extractSecVar v@(SecLabel (LVar _)) = [v]
extractSecVar s = propLeaf extractSecVar List.union s

-- Variable Replacement functions.
replaceSecType :: Lattice l => [(SecType l, SecType l)] -> SecType l -> SecType l
replaceSecType s v@(SecVar _) = findReplace v s 
replaceSecType s v@(SecLabel (LVar _)) = findReplace v s
replaceSecType s t@(SecLabel l) = t
replaceSecType s (SecRef t l@(LVar _)) = SecRef (replaceSecType s t) (unSecLabel (findReplace (SecLabel l) s))
replaceSecType s (SecRef t l) = SecRef (replaceSecType s t) l
replaceSecType s (SecPair t1 t2) = SecPair (replaceSecType s t1) (replaceSecType s t2)
replaceSecType s (SecEither t1 t2 l@(LVar _)) = 
               SecEither (replaceSecType s t1) (replaceSecType s t2) (unSecLabel (findReplace (SecLabel l) s))
replaceSecType s (SecEither t1 t2 l) = 
               SecEither (replaceSecType s t1) (replaceSecType s t2) l
replaceSecType s (SecHigh) = SecHigh

findReplace v2 [] = v2
findReplace v2 (x:xs) = if ((fst x) == v2) then snd x else findReplace v2 xs

replace_flow sub (Trans s1 s2) = Trans (replaceSecType sub s1) (replaceSecType sub s2) 

replace_cons :: Lattice l => [(SecType l, SecType l)] -> [Constraint (SecType l)] -> [Constraint (SecType l)]
replace_cons sub = map (replace_con sub)

replace_con sub (LEQ s1 s2)    = LEQ (replaceSecType sub s1) (replaceSecType sub s2)
replace_con sub (USERGEQ s)    = USERGEQ (replaceSecType sub s)
replace_con sub (IS s1 s2)     = IS (replaceSecType sub s1) (replaceSecType sub s2)
replace_con sub (GUARD t1 t2)  = GUARD (replaceSecType sub t1) (replaceSecType sub t2)
replace_con sub (GSLEQL t1 t2) = GSLEQL (replaceSecType sub t1) (replaceSecType sub t2)
replace_con sub (GLLEQS t1 t2) = GLLEQS (replaceSecType sub t1) (replaceSecType sub t2)

replace_uniset sub [] = []
replace_uniset sub ((u1,u2):cs) = (replaceUType sub u1,replaceUType sub u2):replace_uniset sub cs

replace_pc :: Lattice l => [(SecType l, SecType l)] -> (SecType l) -> (SecType l)
replace_pc = replaceSecType

replaceUType :: Lattice l => [(SecType l, SecType l)] -> U (SecType l) -> U (SecType l)
replaceUType sub u = mapUType (replaceSecType sub) u

idflow = Trans (SecVar "id0") (SecVar "id0")

-- FlowArrowRef
data FlowArrowRef l a b c = FARef { computation  :: ((SecType l) -> (SecType l)) -> a b c
                                  , flow         :: Flow (SecType l)
                                  , constraints  :: [Constraint (SecType l)]
                                  , pc           :: (SecType l)
                                  , uniset       :: [(U (SecType l), U (SecType l))]
                                  }

instance (Lattice l, Arrow a) => 
          Arrow (FlowArrowRef l a) where
  pure f = FARef { computation = (\upd -> pure f)
                 , flow = Trans (SecVar "x0") SecHigh
                 , constraints = []
                 , pc = (SecLabel (Lab label_top))
                 , uniset = []
                 }
  fa1@(FARef c1 f1 t1 pc1 u1) >>> fa2@(FARef c2 f2 t2 pc2 u2) =
     let pc' = (SecLabel (LVar "x0")) in
     let (sub1,sub2,[(_,pc'')]) = make_sub fa1 fa2 [pc'] in
     let (f,c,u) = flow_seq (replace_flow sub1 f1) (replace_flow sub2 f2) in
     FARef { computation = (\upd -> c1 (upd.(replaceSecType sub1)) >>> c2 (upd.(replaceSecType sub2)))
           , flow = f
           , constraints = c ++ (replace_cons sub1 t1) ++ (replace_cons sub2 t2) 
           , pc = pc''
           , uniset = u ++ [(Id pc'',Meet (Id (replace_pc sub1 pc1)) (Id (replace_pc sub2 pc2)))] ++ 
                      (replace_uniset sub1 u1) ++ (replace_uniset sub2 u2)  
           }
  first fa@(FARef c f t pc u) = 
      let (sub1,sub2,_) = make_sub_partial fa idflow [] in
      let f' = flow_pair (replace_flow sub1 f) (replace_flow sub2 idflow) in 
      FARef { computation = (\upd -> first (c (upd.(replaceSecType sub1))))
            , flow = f'
            , constraints = (replace_cons sub1 t)
            , pc = (replace_pc sub1 pc)            
            , uniset = (replace_uniset sub1 u)
            }
  second fa@(FARef c f t pc u) = 
      let (sub1,sub2,_) = make_sub_partial fa idflow [] in
      let f' = flow_pair (replace_flow sub2 idflow) (replace_flow sub1 f) in
      FARef { computation = (\upd -> second (c (upd.(replaceSecType sub1))))
            , flow = f'
            , constraints = (replace_cons sub1 t)
            , pc = (replace_pc sub1 pc) 
            , uniset = (replace_uniset sub1 u)
            }
  fa1@(FARef c1 f1 t1 pc1 u1) *** fa2@(FARef c2 f2 t2 pc2 u2) =
      let pc' = (SecLabel (LVar "x0")) in
      let (sub1,sub2,[(_,pc'')]) = make_sub fa1 fa2 [pc'] in
      FARef { computation = (\upd -> c1 (upd.(replaceSecType sub1)) *** c2 (upd.(replaceSecType sub2)))
            , flow = flow_pair (replace_flow sub1 f1) (replace_flow sub2 f2)
            , constraints = (replace_cons sub1 t1)++(replace_cons sub2 t2)
            , pc = pc''
            , uniset = ([(Id pc'',Meet (Id (replace_pc sub1 pc1)) (Id (replace_pc sub2 pc2)))] ++
                       replace_uniset sub1 u1) ++ (replace_uniset sub2 u2)
            }
  fa1@(FARef c1 f1 t1 pc1 u1) &&& fa2@(FARef c2 f2 t2 pc2 u2) =
      let pc' = (SecLabel (LVar "x0")) in
      let (sub1, sub2,[(_,pc'')]) = make_sub fa1 fa2 [pc'] in
      let (f,c,u) = flow_diverge (replace_flow sub1 f1) (replace_flow sub2 f2) in
      FARef { computation = (\upd -> c1 (upd.(replaceSecType sub1)) &&& c2 (upd.(replaceSecType sub2)))
            , flow = f
            , constraints = c++(replace_cons sub1 t1)++(replace_cons sub2 t2)
            , pc = pc''
            , uniset = u ++ [(Id pc'',Meet (Id (replace_pc sub1 pc1)) (Id (replace_pc sub2 pc2)))]
                       ++(replace_uniset sub1 u1) ++ (replace_uniset sub2 u2)
            }

instance (Lattice l, ArrowChoice a, ArrowAtomic a) => 
    ArrowChoice (FlowArrowRef l a) where
  left fa@(FARef c f t pc u) = 
      let (sub1,sub2,_) = make_sub_partial fa idflow [] in
      let f' = flow_either (replace_flow sub1 f) (replace_flow sub2 idflow) in
      let (Trans s_in s_out) = f' in
      FARef { computation = (\upd -> if (mext_join (upd s_in)) `label_leq` label_bottom
                                       then left (c (upd.(replaceSecType sub1)))
                                       else beginAtomic >>> left (c (upd.(replaceSecType sub1))) >>> endAtomic )
            , flow = f'
            , constraints = (replace_cons sub1 t)
            , pc = (replace_pc sub1 pc)
            , uniset = (replace_uniset sub1 u)
            }
  right fa@(FARef c f t pc u) = 
      let (sub1,sub2,_) = make_sub_partial fa idflow [] in
      let f' = flow_either (replace_flow sub2 idflow) (replace_flow sub1 f) in
      let (Trans s_in s_out) = f' in
      FARef { computation = (\upd -> if (mext_join (upd s_in)) `label_leq` label_bottom
                                       then right (c (upd.(replaceSecType sub1)))
                                       else beginAtomic >>> right (c (upd.(replaceSecType sub1))) >>> endAtomic )
            , flow = f'
            , constraints = (replace_cons sub1 t)
            , pc = (replace_pc sub1 pc)
            , uniset = (replace_uniset sub1 u)
            }
  fa1@(FARef c1 f1 t1 pc1 u1) +++ fa2@(FARef c2 f2 t2 pc2 u2) =
    let pc' = (SecLabel (LVar "x0")) in
    let (sub1,sub2,[(_,pc'')]) = make_sub fa1 fa2 [pc'] in
    let f' = flow_either (replace_flow sub1 f1) (replace_flow sub2 f2) in
    let (Trans s_in s_out ) = f'  in
      FARef { computation = (\upd -> if (mext_join (upd s_in)) `label_leq` label_bottom
                                       then (c1 (upd.(replaceSecType sub1)) +++ c2 (upd.(replaceSecType sub2)))
                                       else beginAtomic >>> 
                                            (c1 (upd.(replaceSecType sub1)) +++ c2 (upd.(replaceSecType sub2))) 
                                            >>> endAtomic)
            , flow = f'
            , constraints = [GSLEQL s_in pc''] ++ (replace_cons sub1 t1)++(replace_cons sub2 t2)
            , pc = pc''
            , uniset = [(Id pc'',Meet (Id (replace_pc sub1 pc1)) (Id (replace_pc sub2 pc2)))]
                       ++ (replace_uniset sub1 u1) ++ (replace_uniset sub2 u2)
            }
  fa1@(FARef c1 f1 t1 pc1 u1) ||| fa2@(FARef c2 f2 t2 pc2 u2) =
    let pc' = (SecLabel (LVar "x0")) in
    let l_out' = (SecLabel (LVar "x1")) in
    let (sub1,sub2,[(_,pc''),(_,l_out'')]) = make_sub fa1 fa2 [pc',l_out'] in
    let (f',u) = flow_converge (replace_flow sub1 f1) (replace_flow sub2 f2) in
    let (Trans s_in s_out ) = f'  in
      FARef { computation = (\upd -> if (mext_join (upd s_in)) `label_leq` label_bottom
                                       then (c1 (upd.(replaceSecType sub1)) ||| c2 (upd.(replaceSecType sub2)))
                                       else beginAtomic >>> 
                                            (c1 (upd.(replaceSecType sub1)) ||| c2 (upd.(replaceSecType sub2))) 
                                            >>> endAtomic)
	        , flow = f'
            , constraints = [GSLEQL s_in pc'', GSLEQL s_in l_out''] ++ 
                            (replace_cons sub1 t1)++(replace_cons sub2 t2)
            , pc = pc''
            , uniset = u ++ [(Id pc'',Meet (Id (replace_pc sub1 pc1)) (Id (replace_pc sub2 pc2)))
                       ,(Id l_out'',LExtr (Id s_out))] ++ (replace_uniset sub1 u1) ++ (replace_uniset sub2 u2)
            }

-- Non-standard combinators of FlowHaskellRef

-- Push up security types to level l. 
tagRef :: (Lattice l, Arrow a) 
          => l -> FlowArrowRef l a b b
tagRef l = 
    let s_in = (SecVar "x0") in
    let s_out = (SecVar "x1") in
    FARef { computation = (\upd -> pure id)
          , flow = Trans s_in s_out
          , constraints = [LEQ s_in s_out]
          , pc = (SecLabel (Lab label_top)) 
          , uniset = [(Id s_out, Tag (Id s_in) (Id (SecLabel (Lab l))))]
          }

-- Declassify a computation.
declassifyRef :: ( Lattice l, Arrow a
                 , BuildSecType l b)
                 => l -> FlowArrowRef l a b b
declassifyRef l = declassifyRef' l (pure id)

declassifyRef' :: (Lattice l, Arrow a
                  ,BuildSecType l b
                  ,TakeOutputType l (FlowArrowRef l a) b b) 
                  => l -> FlowArrowRef l a b b -> FlowArrowRef l a b b
declassifyRef' l fa@(FARef c (Trans s_in _) t pc u) =
   let s_out = (deriveSecType l fa) in
   let s_out' = (SecVar "x1") in
   FARef { computation = (\upd -> c upd )
         , flow = Trans s_in s_out'
         , constraints = [USERGEQ s_in]
         , pc = (SecLabel (Lab label_top))
         , uniset = [(Id s_out', Decl (Id s_in) (Id s_out) (Id (SecLabel (Lab l))))]
         }

-- Help functions for checking constraints in certifyRef. 
check_levels label_in label_out (Trans s1 s2) = 
  (label_in <= s1) && (s2 <= label_out)

check_levelsL label_in label_out (Trans s1 s2) = 
  (label_in <= s1) && (s2 <= (ml_label label_out s2))

check_constraint p (LEQ s1 s2)= if s1 <= s2 
                                  then True 
                                  else error $ "LEQ\n" ++ (show s1) ++ "\n" ++ (show s2) 
check_constraint p (USERGEQ s)= if label_leq (mext_join s) p 
                                  then True 
                                  else error $ "USERGEQ\n" ++ (show s)
check_constraint p (IS s1 s2) = if ml_eqstruct s1 s2 
                                  then True 
                                  else error $ "IS\n" ++ (show s1) ++ "\n" ++ (show s2)
check_constraint p (GUARD l s) = if label_guard l s 
                                   then True 
                                   else error $ "GUARD " ++ (show l) ++ "\n " ++ (show s)
check_constraint p (GSLEQL s l) = if label_gsleql s l 
                                    then True 
                                    else error $ "GSLEQL " ++ (show s) ++ "\n " ++ (show l)
check_constraint p (GLLEQS l s) = if label_glleqs l s 
                                    then True 
                                    else error $ "GLLEQS " ++ (show l) ++ "\n " ++ (show s)
check_constraints p t = all (check_constraint p) t

-- Help functions for resolving variables in (SecType l) .
resolve_flow :: (Lattice l, Show l) => [(SecType l,SecType l)] -> Flow (SecType l) -> Flow (SecType l)
resolve_flow = replace_flow

resolve_cons :: (Lattice l, Show l) => [(SecType l,SecType l)] -> [Constraint (SecType l)] -> [Constraint (SecType l)]
resolve_cons = replace_cons

resolve_pc :: Lattice l => [(SecType l, SecType l)] -> (SecType l) -> l
resolve_pc sym s = (unLabel.unSecLabel) (replace_pc sym s)

-- Check and run FlowArrowRef computation. 
certifyRef :: (Lattice l, Show (Constraint l)) 
              => (SecType l) -> (SecType l) -> Privilege l -> FlowArrowRef l a b c -> a b c
certifyRef l_in l_out priv@(PR user_label) fa@(FARef c f t pc u) =
      let u' = (varIn f)++u in
      let sym = unify u' in
      let (f', t', pc') = (resolve_flow sym f, resolve_cons sym t, resolve_pc sym pc) in
      if not $ check_levels l_in l_out f' then
        error $ "security level mismatch :\n" ++ "input: " ++ (show l_in) ++ "\nflow: " 
               ++ (show f') ++ "\noutput: " ++ (show l_out)
      else if not $ label_leq (mext_join l_in) pc' then
        error $ "pc level mismatch : " ++ (show pc') 
      else if not $ (check_constraints user_label t') then
        error $ "Ref constraints cannot be met : " ++ (show t')
      else
        c (replaceSecType sym)   
  where
  varIn (Trans s1 s2) = if hasVarSecType s1 then [(Id l_in, Id s1)] else [] 

certifyRefL :: (Lattice l, Show (Constraint l)) 
              => (SecType l) -> l -> Privilege l -> FlowArrowRef l a b c -> a b c
certifyRefL l_in l_out priv@(PR user_label) fa@(FARef c f t pc u) =
      let u' = (varIn f)++u in
      let sym = unify u' in
      let (f', t', pc') = (resolve_flow sym f, resolve_cons sym t, resolve_pc sym pc) in
      if not $ check_levelsL l_in l_out f' then
        error $ "security level mismatch :\n" ++ "input: " ++ (show l_in) ++ "\nflow: " 
               ++ (show f') ++ "\noutput: " ++ (show l_out)
      else if not $ label_leq (mext_join l_in) pc' then
        error $ "pc level mismatch : " ++ (show pc') 
      else if not $ (check_constraints user_label t') then
        error $ "Ref constraints cannot be met : " ++ (show t')
      else
        c (replaceSecType sym)  
  where
  varIn (Trans s1 s2) = if hasVarSecType s1 then [(Id l_in, Id s1)] else [] 

equalA :: (Lattice l, Arrow ar,
           BuildSecType l b, 
           TakeOutputType l (FlowArrowRef l ar) a b)
          =>
           l -> FlowArrowRef l ar a b -> FlowArrowRef l ar a b
equalA level fa@(FARef com' (Trans s_in' _) cons' pc' uniset') =
   let flow_out = (deriveSecType level fa) in
   FARef { computation = (\upd -> com' upd)
         , flow = Trans s_in' flow_out
         , constraints = [GLLEQS (SecLabel (Lab level)) s_in', 
                          GSLEQL s_in' (SecLabel (Lab level)), 
                          LEQ (SecLabel (Lab label_top)) pc'] ++ cons'
         , pc = (SecLabel (Lab label_top))
         , uniset = uniset'
         }

lowerA :: (Lattice l, Arrow ar,
          BuildSecType l b,
          FilterData l a,
          ResetProject b,
          TakeOutputType l (FlowArrowRef l ar) a b) 
         => 
          l -> FlowArrowRef l ar a b -> FlowArrowRef l ar a b
lowerA level fa@(FARef com' (Trans s_in' _) cons' pc' uniset') =
   let flow_out = (deriveSecType level fa) in
   let inputFilter upd = pure (\i -> (removeData level (upd s_in') i)) in
   let removeRead = pure (\i -> resetProject i) in
   FARef { computation = (\upd -> (inputFilter upd) >>> (com' upd) >>> removeRead)
         , flow = Trans s_in' flow_out
         , constraints = [LEQ (SecLabel (Lab label_top)) pc'] ++ cons' 
         , pc = (SecLabel (Lab label_top))
         , uniset = uniset'
         }

iterateA :: Lattice l => 
            FlowArrowRef l ArrowRef a (a,Bool) -> FlowArrowRef l ArrowRef a a
iterateA (FARef com' (Trans fin fout) cons' pc' uniset') =
    let vout = (SecVar "x0") in
    let vbool = (SecVar "x1") in
    FARef { computation = (\upd -> iterateArrowRef (com' upd))
          , flow = Trans fin vout
          , constraints = [LEQ vout fin, GUARD vbool vout] ++ cons'
          , pc = pc'
          , uniset = (Id vbool,LExtr (Snd (Id fout))):(Id vout,Fst (Id fout)):uniset'
          }

-- Reference manipulation
createRefA :: (Lattice l, STSecType st l,
              BuildSecType l b) =>
             st -> l -> FlowArrowRef l ArrowRef b (SRef st b)
createRefA = createRefA' (pure id)

createRefA' :: (Lattice l, STSecType st l, 
               BuildSecType l b,
               TakeOutputType l (FlowArrowRef l ArrowRef) b b) => 
              FlowArrowRef l ArrowRef b b -> st -> l -> 
              FlowArrowRef l ArrowRef b (SRef st b) 
createRefA' far rs lr = 
   let ld = (SecVar "x0") in
   let pc' = SecLabel (LVar "x1") in
   let s_in = deriveSecType label_bottom far in
   FARef { computation = (\upd -> waitForYield >>>
                                  AR (\env -> do ref <- createMRef (dat env) rs
                                                 return env{dat=ref}) >>>
                                  yieldControl )
         , flow = Trans ld (SecRef (toSecType rs) (Lab lr))
         , constraints = [LEQ ld (toSecType rs), IS s_in (toSecType rs)]  
         , pc = pc'
         , uniset = [(Id pc',LExtr (Id ld))]
         }

readRefA :: (Lattice l, STSecType st l) 
           => (SecType l) -> FlowArrowRef l ArrowRef (SRef st b) b  
readRefA lv =
   let ld = (SecVar "x0") in
   let lr = (LVar "x1") in
   FARef { computation = (\upd -> waitForYield >>>
                                  AR (\env -> do d <- readMRef (dat env)
                                                 return env{dat=d}) >>>
                                  yieldControl)
         , flow = Trans (SecRef ld lr) lv
         , constraints = [LEQ ld lv, GUARD (SecLabel lr) lv]
         , pc = SecLabel (Lab label_top)
         , uniset = []
         }

writeRefA :: (Lattice l, STSecType st l) 
            => FlowArrowRef l ArrowRef (SRef st b, b) ()
writeRefA =
    let ld = (SecVar "x0") in
    let lr = (LVar "x1") in
    let pc' = (SecLabel (LVar "x2")) in
	FARef { computation = (\upd -> waitForYield >>>
                                   AR (\env -> do 
                                                 writeMRef (fst (dat env)) (snd (dat env))
                                                 return env{dat=()}) >>>
                                   yieldControl )
          , flow = Trans (SecPair (SecRef ld lr) ld) (SecLabel (Lab label_bottom))
          , constraints = [GUARD (SecLabel lr) ld]
          , pc = pc'
          , uniset = [(Id pc',LExtr (Id ld))]
          }

-- The following primitives are syntactic sugers.
fstPair :: (Lattice l) => FlowArrowRef l ArrowRef (a,b) a
fstPair =
    let s1 = (SecVar "x0") in
    let s2 = (SecVar "x1") in
    FARef { computation = (\upd -> waitForYield >>>
                                   AR (\env -> do 
                                                 d <- return $ fst (dat env)
                                                 return env{dat=d}) >>>
                                   yieldControl)
          , flow = Trans (SecPair s1 s2) s1
          , constraints = []
          , pc = SecLabel (Lab label_top)
          , uniset = []
          }

sndPair :: (Lattice l) => FlowArrowRef l ArrowRef (a,b) b
sndPair =
    let s1 = (SecVar "x0") in
    let s2 = (SecVar "x1") in
    FARef { computation = (\upd -> waitForYield >>>
                                   AR (\env -> do
                                                 d <- return $ snd (dat env)
                                                 return env{dat=d}) >>>
                                   yieldControl)
          , flow = Trans (SecPair s1 s2) s2
          , constraints = []
          , pc = SecLabel (Lab label_top)
          , uniset = []
          }

-- Id function to pass data.
idRef :: (Lattice l, Arrow a) 
         => FlowArrowRef l a b b
idRef =
   let s_in = (SecVar "x0") in
   FARef { computation = (\upd -> pure id)
         , flow = Trans s_in s_in
         , constraints = []
         , pc = (SecLabel (Lab label_top))
         , uniset = []
         }

-- SecPair right ((a,b),c) -> (a,(b,c)).
pairRight :: (Lattice l, Arrow a) 
             => FlowArrowRef l a ((b,c),d) (b,(c,d))
pairRight =
   let s1 = (SecVar "x0") in
   let s2 = (SecVar "x1") in
   let s3 = (SecVar "x2") in
   FARef { computation = (\upd -> pure (\((a,b),c) -> (a,(b,c))))
         , flow = Trans (SecPair (SecPair s1 s2) s3) (SecPair s1 (SecPair s2 s3))
         , constraints = []
         , pc = (SecLabel (Lab label_top))
         , uniset = []
         }

-- SecPair left (a,(b,c)) -> ((a,b),c).
pairLeft :: (Lattice l, Arrow a) 
             => FlowArrowRef l a (b,(c,d)) ((b,c),d)
pairLeft =
   let s1 = (SecVar "x0") in
   let s2 = (SecVar "x1") in
   let s3 = (SecVar "x2") in
   FARef { computation = (\upd -> pure (\(a,(b,c)) -> ((a,b),c)))
         , flow = Trans (SecPair s1 (SecPair s2 s3)) (SecPair (SecPair s1 s2) s3)
         , constraints = []
         , pc = (SecLabel (Lab label_top))
         , uniset = []
         }

-- Return a unit.
nullRef :: (Lattice l, Arrow a) 
           => FlowArrowRef l a b ()
nullRef =
   let s_in = (SecVar "x0") in
   FARef { computation = (\upd -> pure (\_ -> ()))
         , flow = Trans s_in (SecLabel (Lab label_bottom))
         , constraints = []
         , pc = (SecLabel (Lab label_top))
         , uniset = []
         }

-- The run-time system for multithreaded information flow.

data RRobin a = RRobin {
      dat  :: a,               -- real compuatation data
      blocks    :: Int,             -- nested protect count
      queue :: TVar [ThreadId], -- round-robin thread queue
      iD      :: ThreadId         -- identify of the thread
   }

data ArrowRef a b = AR ((RRobin a) -> IO (RRobin b)) 

unAR (AR f) = f

runArrowRef (AR f) a = do myid <- myThreadId
                          q <- newThreadQueue myid
                          env' <- f (RRobin a 0 q myid)
                          return (dat env')

newOrder = atomically $ newTVar []

instance Arrow ArrowRef where
  pure f = waitForYield >>>
           AR (\env -> do b <- return $ f (dat env)
                          return env{ dat = b } ) >>>
           yieldControl
              
  (AR f) >>> (AR g) =
     AR (\env -> f env >>= g)

  first (AR f) =
     AR (\env -> let (b,d) = (dat env) in
                 f (env{dat = b}) >>=
                 (\env' -> return env'{dat = (dat env',d)}) )

instance Arrow ArrowRef => ArrowChoice ArrowRef where
  left (AR f) = AR (\env -> case (dat env) of
                              Left d  -> (f env{ dat = d }) >>= 
                                         (\env' -> return env'{dat = Left (dat env')})
                              Right d -> return env{dat = (Right d)} )

instance Arrow ArrowRef => ArrowLoop ArrowRef where
  loop (AR f) = AR (\env -> do (d,c) <- mfix (\ ~(d,c) -> do env' <- f env{dat=(dat env,c)}
                                                             return $ dat env')
                               return env{dat=d}    
                   ) 

iterateArrowRef (AR f) = AR (\env -> let ite = (\(env,b) -> if b
                                                              then do env' <- f env
                                                                      b' <- return (snd (dat env'))
                                                                      ite (env'{dat = fst (dat env')},b')
                                                              else return env)
                                     in
                                     ite (env,True))

class Arrow a => ArrowAtomic a where
  beginAtomic :: a b b
  endAtomic :: a b b

instance ArrowAtomic ArrowRef where
  beginAtomic = waitForYield >>>
          AR (\env -> return env{blocks = ((blocks env)+1)} )

  endAtomic = AR (\env -> if (blocks env) <= 0 
                       then error "beginAtomic and endAtomic is not well paired."
                       else return env{blocks = ((blocks env)-1)} )
           >>> yieldControl

newLockRef :: IO (TVar Bool)
newLockRef = atomically $ newTVar True

newThreadQueue :: ThreadId -> IO (TVar [ThreadId])
newThreadQueue myid = atomically $ newTVar [myid]

waitForYield :: ArrowRef a a
waitForYield = AR (\env -> do waitTurn env
                              return env)

yieldControl :: ArrowRef a a
yieldControl = AR (\env -> do nextTurn env
                              return env)

waitTurn :: RRobin a -> IO ()
waitTurn env = if (blocks env) > 0
             then return ()
             else atomically $
                  do que <- readTVar (queue env)
                     if head que /= (iD env)
                       then retry
                       else return ()

nextTurn :: RRobin a -> IO ()
nextTurn env = if (blocks env) > 0
               then return ()
               else atomically $
                    do que <- readTVar (queue env)
                       if head que /= (iD env)
                         then error "nextTurn and waitTurn inconsistent."
                         else do writeTVar (queue env) ((tail que)++[head que])
                                 return ()

skip :: RRobin Int -> IO ()
skip env = if (dat env) <= 0
             then return ()
             else do waitTurn env
                     i' <- return ((dat env)-1)
                     nextTurn env
                     skip env{dat=i'}

skipRef :: (Lattice l) => FlowArrowRef l ArrowRef Int ()
skipRef =
   let s_in = (SecVar "x0") in
   FARef { computation = (\upd -> AR(\env -> do skip env
                                                return env{dat=()} ))
         , flow = Trans s_in (SecLabel (Lab label_bottom))
         , constraints = []
         , pc = SecLabel (Lab label_top)
         , uniset = []
         }

atomicA :: Lattice l => 
            FlowArrowRef l ArrowRef a b -> FlowArrowRef l ArrowRef a b
atomicA (FARef com' flow' cons' pc' uniset') =
    FARef { computation = (\upd ->  beginAtomic >>> (com' upd) >>> endAtomic)
          , flow = flow'
          , constraints = cons'
          , pc = pc'
          , uniset = uniset'
          }

forkRef :: (Lattice l) => 
           FlowArrowRef l ArrowRef a b -> FlowArrowRef l ArrowRef a ()
forkRef (FARef com' (Trans f_in f_out) cons' pc' uniset') =
   FARef { computation = (\upd -> let t = unAR (initThread >>> (com' upd) >>> endThread ) in
                                  waitForYield >>>
                                  AR (\env -> do env' <- return env{blocks = 0}
                                                 nid <-forkIO (((t env') >>= nullThread) 
                                                               `Control.Exception.catch` 
                                                               (finalThread env'))
                                                 newThread env nid
                                                 return env{dat=()}) >>>
                                  yieldControl )
         , flow = Trans f_in (SecLabel (Lab label_bottom))
         , constraints = cons'
         , pc = pc'
         , uniset = uniset'
         }
  where
  nullThread = (\_ -> return ())

newThread :: RRobin a -> ThreadId -> IO (RRobin a)
newThread env nid = do atomically $ do que <- readTVar (queue env)
                                       writeTVar (queue env) (que++[nid])
                       return env

initThread :: ArrowRef a a
initThread = AR (\env -> do myId <- myThreadId
                            return env{iD = myId} )

endThread :: ArrowRef a a
endThread = AR (\env -> do atomically $
                            do que <- readTVar (queue env)
                               writeTVar (queue env) (filter ((iD env)/=) que) 
                               return que
                           return env )

finalThread :: RRobin a -> Exception -> IO ()
finalThread env = (\e -> do 
                            q <- atomically $ readTVar (queue env)
                            mapM killThread q
                            return () )

-- Generate a random number in range (l,h).
randomRRef :: (Lattice l) => Int -> Int -> FlowArrowRef l ArrowRef Int Int
randomRRef l h =
   let s_in = (SecVar "x0") in
   FARef { computation = (\upd -> waitForYield >>>
                                  AR (\env -> do r <- randomRIO (l,h)
                                                 return env{dat=r}) >>>
                                  yieldControl )
         , flow = Trans s_in s_in
         , constraints = []
         , pc = SecLabel (Lab label_top)
         , uniset = []
         }
