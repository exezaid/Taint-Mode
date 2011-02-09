{-# OPTIONS -fallow-undecidable-instances -fglasgow-exts -farrows #-}

module FlowArrowRef
( FlowArrow
, FlowArrowRef
, ArrowRef
, Privilege
, AuthDB
, tagRef
, declassifyRef
, certifyRef
, certifyRefL
, authenticate
, FlowArrowRef.createRef
, FlowArrowRef.readRef
, FlowArrowRef.writeRef
, runArrowRef
, createPair
, fstPair
, sndPair 
, lowerA
, forkRef
, protectA
, skipRef
, iterateA
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
import Control.Arrow
import Data.IORef
import SecureFlow
import RefOp 
import Control.Concurrent
import Control.Concurrent.STM
import Control.Monad.Fix
import System.Random
import Priv
import Control.Exception

data Constraint l = 
    LEQ l l | USERGEQ l | IS l l deriving (Eq, Show)
-- IS l1 l2 is to force l1 has the same structure as l2.

data GConstraint l = GUARD l l | GSLEQL l l | GLLEQS l l
    deriving (Eq, Show)

{- temporary used for (UType l)
data UGConstraint l = UGUARD l l | UGSLEQL l l
    deriving (Eq, Show)
-}

data Flow l = Trans l l  
       deriving (Eq,Show)

{---------------------------------------------------
   Flow control for >>>                           
   We assume the renamed variable begin with "a", 
   so we can put variable with prefix "x".        
---------------------------------------------------}
flow_seq::Lattice l => Flow (SecType l) -> Flow (SecType l) 
                       -> ( Flow (SecType l)
                          , [Constraint (SecType l)]
                          , [(U (SecType l),U (SecType l))])
flow_seq (Trans s1 s2) (Trans s3 s4)= 
    if (hasVarSecType s3)
      then (Trans s1 s4, [],[(Id s2,Id s3)])   
      else (Trans s1 s4, [LEQ s2 s3],[])
             
{---------------------------------------------
   Flow control for first, second, and ***. 
---------------------------------------------}
flow_pair :: Lattice l => Flow (SecType l) -> Flow (SecType l) -> Flow (SecType l)
flow_pair (Trans s1 s2) (Trans s3 s4) = Trans (Pair s1 s3) (Pair s2 s4) 

{--------------------------
   Flow control for &&&. 
--------------------------}
flow_diverge :: Lattice l => Flow (SecType l) -> Flow (SecType l) 
                             -> ( Flow (SecType l)
                                , [Constraint (SecType l)]
                                , [(U (SecType l), U (SecType l))])
flow_diverge (Trans s1 s2) (Trans s1' s2') =
  if hasVarSecType s1
    then if hasVarSecType s1'
           then (Trans s1 out_flow, [], [(Id s1,Id s1')])
           else (Trans s1 out_flow, [LEQ s1 s1'], [])
    else if hasVarSecType s1'
           then (Trans s1' out_flow, [LEQ s1' s1], [])
           else (Trans (SecVar "x0") out_flow, [], [(Id (SecVar "x0"),Meet (Id s1) (Id s1'))])  
  where
  out_flow = (Pair s2 s2')

{-------------------------------------------
   Flow control for left, right, and +++. 
-------------------------------------------}
flow_either :: Lattice l => Flow (SecType l) -> Flow (SecType l) -> Flow (SecType l)
flow_either (Trans s1 s2) (Trans s3 s4) = Trans (SecEither s1 s3 (LVar "x0")) (SecEither s2 s4 (LVar "x0"))

{--------------------------
   Flow control for |||. 
--------------------------}
flow_converge :: Lattice l => Flow (SecType l) -> Flow (SecType l) 
                              -> ( Flow (SecType l)
                                 , [GConstraint (SecType l)]
                                 , [(U (SecType l),U (SecType l))])
flow_converge (Trans s1 s2) (Trans s1' s2') =
  let l = (LVar "x0") in
  let s_out = (SecVar "x1") in 
  (Trans (SecEither s1 s1' l) s_out
  ,[GUARD (SecLabel l) s1, GUARD (SecLabel l) s2]
  ,[(Id s_out, Join (Id s2) (Id s2'))])  

{-------------------------------------------------------
   Make substitution pair for both arrow computation. 
-------------------------------------------------------}
make_sub :: (Lattice l) => FlowArrow l a b c -> FlowArrow l a b' c' -> [SecType l]
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
  
{------------------------------------------------------
   Gather all variables in an FlowArrow computation. 
------------------------------------------------------}
extract_arrow :: Lattice l => FlowArrow l a b c -> [SecType l]
extract_arrow (FA s f c gc u) = total
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

{---------------------------------
   Variable Replacement functions 
----------------------------------}
{-replaceSecType sub t = foldl substi t sub
  where
  substi s (v,v') = replaceUType v v' s
-}
replaceSecType :: Lattice l => [(SecType l, SecType l)] -> SecType l -> SecType l
replaceSecType s v@(SecVar _) = findReplace v s 
replaceSecType s v@(SecLabel (LVar _)) = findReplace v s
replaceSecType s t@(SecLabel l) = t
replaceSecType s (Ref t l@(LVar _)) = Ref (replaceSecType s t) (unSecLabel (findReplace (SecLabel l) s))
replaceSecType s (Ref t l) = Ref (replaceSecType s t) l
replaceSecType s (Pair t1 t2) = Pair (replaceSecType s t1) (replaceSecType s t2)
replaceSecType s (SecEither t1 t2 l@(LVar _)) = 
               SecEither (replaceSecType s t1) (replaceSecType s t2) (unSecLabel (findReplace (SecLabel l) s))
replaceSecType s (SecEither t1 t2 l) = 
               SecEither (replaceSecType s t1) (replaceSecType s t2) l
replaceSecType s (SecHigh) = SecHigh

findReplace v2 [] = v2
findReplace v2 (x:xs) = if ((fst x) == v2) then snd x else findReplace v2 xs

replace_flow sub (Trans s1 s2) = Trans (replaceSecType sub s1) (replaceSecType sub s2) 

replace_cons :: Lattice l => [(SecType l, SecType l)] -> [Constraint (SecType l)] -> [Constraint (SecType l)]
replace_cons sub [] = []
replace_cons sub ((LEQ s1 s2):cs) = (LEQ (replaceSecType sub s1) (replaceSecType sub s2)):replace_cons sub cs
replace_cons sub ((USERGEQ s):cs) = (USERGEQ (replaceSecType sub s)):replace_cons sub cs
replace_cons sub ((IS s1 s2):cs) = (IS (replaceSecType sub s1) (replaceSecType sub s2)):replace_cons sub cs

replace_uniset sub [] = []
replace_uniset sub ((u1,u2):cs) = (replaceUType sub u1,replaceUType sub u2):replace_uniset sub cs

replaceUType :: Lattice l => [(SecType l, SecType l)] -> U (SecType l) -> U (SecType l)
replaceUType sub u = mapUType (replaceSecType sub) u

{--------------
   FlowArrow 
--------------}
data FlowArrow l a b c = FA
    { computation  :: ((SecType l) -> (SecType l)) -> a b c
    , flow         :: Flow (SecType l)
    , constraints  :: [Constraint (SecType l)]
    , gconstraints :: [GConstraint (SecType l)] 
    , uniset       :: [(U (SecType l), U (SecType l))]
    }

idflow = Trans (SecVar "id0") (SecVar "id0")

instance (Lattice l, Arrow a) => Arrow (FlowArrow l a) where
  pure f = FA { computation = (\upd -> pure f)
              , flow = Trans (SecVar "x0") SecHigh
              , constraints = []
              , gconstraints = []
              , uniset = []
              }
  a1@(FA c1 f1 t1 g1 u1) >>> a2@(FA c2 f2 t2 g2 u2) =
     let (sub1, sub2, _) = (make_sub a1 a2 []) in
     let (f,c,u) = flow_seq (replace_flow sub1 f1) (replace_flow sub2 f2) in
      FA { computation = (\upd -> c1 (upd.(replaceSecType sub1)) >>> c2 (upd.(replaceSecType sub2)))
         , flow = f
         , constraints = c ++ (replace_cons sub1 t1) ++ (replace_cons sub2 t2) 
         , gconstraints = (replace_gcons sub1 g1) ++ (replace_gcons sub2 g2)
         , uniset = u ++ (replace_uniset sub1 u1) ++ (replace_uniset sub2 u2)  
         }
  first a1@(FA c f t g u) = 
      let (sub1, sub2, _) = (make_sub_partial a1 idflow []) in
      let f' = flow_pair (replace_flow sub1 f) (replace_flow sub2 idflow) in 
      FA { computation = (\upd -> first (c (upd.(replaceSecType sub1))))
         , flow = f'
         , constraints = (replace_cons sub1 t)
         , gconstraints = (replace_gcons sub1 g)
         , uniset = (replace_uniset sub1 u)
         }
  second a2@(FA c f t g u) = 
      let (sub1,sub2, _) = (make_sub_partial a2 idflow []) in
      let f' = flow_pair (replace_flow sub2 idflow) (replace_flow sub1 f) in
      FA { computation = (\upd -> second (c (upd.(replaceSecType sub1))))
         , flow = f'
         , constraints = (replace_cons sub1 t)
         , gconstraints = (replace_gcons sub1 g)
         , uniset = (replace_uniset sub1 u)
         }
  a1@(FA c1 f1 t1 g1 u1) *** a2@(FA c2 f2 t2 g2 u2) =
     let (sub1, sub2, _) = make_sub a1 a2 [] in
      FA { computation = (\upd -> c1 (upd.(replaceSecType sub1)) *** c2 (upd.(replaceSecType sub2)))
         , flow = flow_pair (replace_flow sub1 f1) (replace_flow sub2 f2)
         , constraints = (replace_cons sub1 t1)++(replace_cons sub2 t2)
         , gconstraints = (replace_gcons sub1 g1) ++ (replace_gcons sub2 g2)
         , uniset = (replace_uniset sub1 u1) ++ (replace_uniset sub2 u2)
         }
  -- &&& :: a b c -> a b c' -> a b (c,c') 
  -- We need special attention here!
  -- How should we decide the SecType of both bs?
  a1@(FA c1 f1 t1 g1 u1) &&& a2@(FA c2 f2 t2 g2 u2) =
     let (sub1, sub2, _) = make_sub a1 a2 [] in
     let (f,c,u) = flow_diverge (replace_flow sub1 f1) (replace_flow sub2 f2) in
      FA { computation = (\upd -> c1 (upd.(replaceSecType sub1)) &&& c2 (upd.(replaceSecType sub2)))
         , flow = f
         , constraints = c++(replace_cons sub1 t1)++(replace_cons sub2 t2)
         , gconstraints = (replace_gcons sub1 g1) ++ (replace_gcons sub2 g2)
         , uniset = u++(replace_uniset sub1 u1) ++ (replace_uniset sub2 u2)
         }


instance (Lattice l, ArrowChoice a, ArrowAtomic a) => ArrowChoice (FlowArrow l a) where
  left a1@(FA c f t g u) = 
      let (sub1,sub2,_) = make_sub_partial a1 idflow [] in
      let f' = flow_either (replace_flow sub1 f) (replace_flow sub2 idflow) in
      FA { computation = (\upd -> left (c (upd.(replaceSecType sub1))))
         , flow = f'
         , constraints = (replace_cons sub1 t)
         , gconstraints = (replace_gcons sub1 g)
         , uniset = (replace_uniset sub1 u)
         }
  right a2@(FA c f t g u) = 
      let (sub1,sub2,_) = make_sub_partial a2 idflow [] in
      let f' = flow_either (replace_flow sub2 idflow) (replace_flow sub1 f) in
      FA { computation = (\upd -> right (c (upd.(replaceSecType sub1))))
         , flow = f'
         , constraints = (replace_cons sub1 t)
         , gconstraints = (replace_gcons sub1 g)
         , uniset = (replace_uniset sub1 u)
         }
  a1@(FA c1 f1 t1 g1 u1) +++ a2@(FA c2 f2 t2 g2 u2) =
      let (sub1, sub2, _) = make_sub a1 a2 [] in 
      FA { computation = (\upd -> hide >>> (c1 (upd.(replaceSecType sub1)) +++ c2 (upd.(replaceSecType sub2))) >>> unhide)
         , flow = flow_either (replace_flow sub1 f1) (replace_flow sub2 f2)
         , constraints = (replace_cons sub1 t1)++(replace_cons sub2 t2)
         , gconstraints = (replace_gcons sub1 g1) ++ (replace_gcons sub2 g2)
         , uniset = (replace_uniset sub1 u1) ++ (replace_uniset sub2 u2)
         }
  -- ||| :: a b d -> a c d -> a (Either b c) d
  -- We need special attention here!
  -- How should we decide the SecType of both ds?
  a1@(FA c1 f1 t1 g1 u1) ||| a2@(FA c2 f2 t2 g2 u2) =
      let (sub1, sub2, _) = make_sub a1 a2 [] in
      let (f,gc,u) = flow_converge (replace_flow sub1 f1) (replace_flow sub2 f2) in
      FA { computation = (\upd -> hide >>> (c1 (upd.(replaceSecType sub1)) ||| c2 (upd.(replaceSecType sub2))) >>> unhide)
	     , flow = f 
         , constraints = (replace_cons sub1 t1)++(replace_cons sub2 t2)
         , gconstraints = gc ++ (replace_gcons sub1 g1) ++ (replace_gcons sub2 g2)
         , uniset = u ++ (replace_uniset sub1 u1) ++ (replace_uniset sub2 u2)
         }

{-
instance (Lattice l, ArrowLoop a) => ArrowLoop (FlowArrow l a) where
 loop a1@(FA c f t u) = 
   let (f',t',u') = flow_loop f in
     FA { computation = (\upd -> loop (c upd)) 
        , flow = f'
        , constraints = t ++ t'
        , gconstraints = []
        , uniset = u ++ u'
        }
   where  
   flow_loop (Trans a b) = (Trans (UFst a) (UFst b),[],[])
-}

{---------------------------------------
   Restrict current security label.   
---------------------------------------}
tag :: (Lattice l, Arrow a) => l -> FlowArrow l a b b
tag l = 
    FA { computation = (\upd -> pure id)
       , flow = Trans (SecVar "x0") (SecVar "x1")
       , constraints = [LEQ (SecVar "x0") (SecVar "x1")]
       , gconstraints = []
       , uniset = [(Id (SecVar "x1"), Tag (Id (SecVar "x0")) (Id (SecLabel (Lab l))))]
       }

tagRef :: (Lattice l, Arrow a, Arrow (FlowArrow l a)) 
          => l -> FlowArrowRef l a b b
tagRef l = 
    FARef { flowarrow = tag l
          , pc = (SecLabel (Lab label_top)) 
          , constraintsRef = []
          , gconstraintsRef = []
          }

{------------------------------
   Declassify a computation. 
------------------------------}

{-
declassifyRef :: (Lattice l, Arrow a) => l -> FlowArrowRef l a b b
declassifyRef l =
   let s_in = (SecVar "x0") in
   let s_out = (SecVar "x1") in
   FARef { flowarrow = FA { computation = com'
                          , flow = Trans s_in s_out
                          , constraints = [USERGEQ s_in]
                          , uniset = [(Id s_out, Decl (Id s_in) (Id (SecLabel (Lab l))))]
                          }
         , pc = (SecLabel (Lab label_top))
         , constraintsRef = []
         , gconstraintsRef = []
         }
-}

-- deduce output type required when input security label is SecHigh
declassifyRef l = declassifyRef' l (pure id)

declassifyRef' :: (Lattice l, Arrow a, Arrow (FlowArrow l a)
                  ,Downgrade SecType l b ,Dummy b
                  ,DowngradeArrow SecType l (FlowArrowRef l a) b b) 
                  => l -> FlowArrowRef l a b b -> FlowArrowRef l a b b
declassifyRef' level total@(FARef (FA com' f' cons' gcons' uniset') pc' consRef' gconsRef') =
   let (s_in, s_out) = (lowFlow level total) in
   let s_out' = (SecVar "x1") in
   FARef { flowarrow = FA { computation = com'
                          , flow = Trans s_in s_out'
                          , constraints = [USERGEQ s_in]
                          , gconstraints = []
                          , uniset = [(Id s_out', Decl (Id s_in) (Id s_out) (Id (SecLabel (Lab level))))]
                          }
         , pc = (SecLabel (Lab label_top))
         , constraintsRef = []
         , gconstraintsRef = []
         }


{-----------------------------------------
   Id function to pass data
-----------------------------------------}
idRef :: (Lattice l, Arrow a, Arrow (FlowArrow l a)) 
         => FlowArrowRef l a b b
idRef =
   let s_in = (SecVar "x0") in
   FARef { flowarrow = FA { computation = (\upd -> pure id)
                          , flow = Trans s_in s_in
                          , constraints = []
                          , gconstraints = []
                          , uniset = []
                          }
         , pc = (SecLabel (Lab label_top))
         , constraintsRef = []
         , gconstraintsRef = []
         }

{------------------------------------------
   Pair right ((a,b),c) -> (a,(b,c))
------------------------------------------}
pairRight :: (Lattice l, Arrow a, Arrow (FlowArrow l a)) 
             => FlowArrowRef l a ((b,c),d) (b,(c,d))
pairRight =
   let s1 = (SecVar "x0") in
   let s2 = (SecVar "x1") in
   let s3 = (SecVar "x2") in
   FARef { flowarrow = FA { computation = (\upd -> pure (\((a,b),c) -> (a,(b,c))))
                          , flow = Trans (Pair (Pair s1 s2) s3) (Pair s1 (Pair s2 s3))
                          , constraints = []
                          , gconstraints = []
                          , uniset = []
                          }
         , pc = (SecLabel (Lab label_top))
         , constraintsRef = []
         , gconstraintsRef = []
         }

{------------------------------------------
   Pair left (a,(b,c)) -> ((a,b),c)
------------------------------------------}
pairLeft :: (Lattice l, Arrow a, Arrow (FlowArrow l a)) 
             => FlowArrowRef l a (b,(c,d)) ((b,c),d)
pairLeft =
   let s1 = (SecVar "x0") in
   let s2 = (SecVar "x1") in
   let s3 = (SecVar "x2") in
   FARef { flowarrow = FA { computation = (\upd -> pure (\(a,(b,c)) -> ((a,b),c)))
                          , flow = Trans (Pair s1 (Pair s2 s3)) (Pair (Pair s1 s2) s3)
                          , constraints = []
                          , gconstraints = []
                          , uniset = []
                          }
         , pc = (SecLabel (Lab label_top))
         , constraintsRef = []
         , gconstraintsRef = []
         }

{------------------------------------------
   Make null result
------------------------------------------}
nullRef :: (Lattice l, Arrow a, Arrow (FlowArrow l a)) 
           => FlowArrowRef l a b ()
nullRef =
   let s_in = (SecVar "x0") in
   FARef { flowarrow = FA { computation = (\upd -> pure (\_ -> ()))
                          , flow = Trans s_in (SecLabel (Lab label_bottom))
                          , constraints = []
                          , gconstraints = []
                          , uniset = []
                          }
         , pc = (SecLabel (Lab label_top))
         , constraintsRef = []
         , gconstraintsRef = []
         }

{-----------------------------------------
   Check and run FlowArrow computation. 
-----------------------------------------}
certify :: (Lattice l, Show (Constraint (SecType l))) => (SecType l) -> (SecType l) -> Privilege l 
           -> FlowArrow l a b c -> a b c
certify l_in l_out (PR label_user) (FA c f t g u) = 
--  error $ (show f) ++ "\nConstraint : " ++ (show t) ++ "\nUniset : " ++ (show u) ++ "\n sym : " ++ (show sym)
  let (f', t', g') = (resolve_flow sym f, resolve_cons sym t, resolve_gcons sym g) in
  if not $ check_levels l_in l_out f' then
      error $ "security level mismatch :\n" ++ "input: " ++ (show l_in) ++ "\nflow: " 
               ++ (show f') ++ "\noutput: " ++ (show l_out)
  else if not $ (check_constraints label_user t') && (check_gconstraints label_user g') then
      error $ "constraints cannot be met : "++ (show t') ++ "\n" ++ (show g')
  else 
      --error $ "flow : " ++ (show f') ++ "\nconstraints : " ++ (show t')
      c (replaceSecType sym)  
  where
  sym = unify u

certifyL :: (Lattice l, Show (Constraint (SecType l))) => (SecType l) -> l -> Privilege l 
           -> FlowArrow l a b c -> a b c
certifyL l_in l_out (PR label_user) (FA c f t g u) = 
--  error $ (show f) ++ "\nConstraint : " ++ (show t) ++ "\nUniset : " ++ (show u) ++ "\n sym : " ++ (show sym)
  let (f', t', g') = (resolve_flow sym f, resolve_cons sym t, resolve_gcons sym g) in
  if not $ check_levelsL l_in l_out f' then
      error $ "security level mismatch :\n" ++ "input: " ++ (show l_in) ++ "\nflow: " 
               ++ (show f') ++ "\noutput: " ++ (show l_out)
  else if not $ (check_constraints label_user t') && (check_gconstraints label_user g') then
      error $ "constraints cannot be met : "++ (show t') ++ "\n" ++ (show g')
  else 
      --error $ "flow : " ++ (show f') ++ "\nconstraints : " ++ (show t')
      c (replaceSecType sym)  
  where
  sym = unify u

{-------------------------------------------------------
   Help function for checking constraints in certify. 
-------------------------------------------------------}
check_levels label_in label_out (Trans s1 s2) = 
  (mlabel_leq label_in s1) && (mlabel_leq s2 label_out)

check_levelsL label_in label_out (Trans s1 s2) = 
  (mlabel_leq label_in s1) && (mlabel_leq s2 (mlabel_label label_out s2))

check_constraint p (LEQ s1 s2)= if mlabel_leq s1 s2 
                                  then True 
                                  else error $ "LEQ " ++ (show s1) ++ " " ++ (show s2) 
check_constraint p (USERGEQ s)= if label_leq (mext_join s) p 
                                  then True 
                                  else error $ "USERGEQ " ++ (show s)
-- only required in declassify...but maybe not in new definition
check_constraint p (IS s1 s2) =  True --if mlabel_eqstruct s1 (mlabel_top s2) 
                                      --then True 
                                      --else error $ "IS " ++ (show s1) ++ " " ++ (show s2)
check_constraints p t = all (check_constraint p) t

{----------------------------------------------------
  Hack! put p involve to restrict type variable s. 
----------------------------------------------------}
check_gconstraint :: (Lattice l) => l -> GConstraint (SecType l) -> Bool
check_gconstraint p (GUARD l s) = if label_guard l s then True else error $ "GUARD " ++ (show l) ++ "\n " ++ (show s)
check_gconstraint p (GSLEQL s l) = if label_gsleql s l then True else error $ "GSLEQL " ++ (show s) ++ "\n " ++ (show l)
check_gconstraint p (GLLEQS l s) = if label_glleqs l s then True else error $ "GLLEQS " ++ (show l) ++ "\n " ++ (show s)
check_gconstraints p fs = all (check_gconstraint p) fs

{---------------------------------------------------------
   Help function for resolving variables in (SecType l) 
---------------------------------------------------------}
resolve_flow :: (Lattice l, Show l) => [(SecType l,SecType l)] -> Flow (SecType l) -> Flow (SecType l)
resolve_flow = replace_flow

resolve_cons :: (Lattice l, Show l) => [(SecType l,SecType l)] -> [Constraint (SecType l)] -> [Constraint (SecType l)]
resolve_cons = replace_cons

{--------------------------------------------
   Check and run FlowArrowRef computation. 
--------------------------------------------}
certifyRef :: (Lattice l, Show (Constraint l)) 
              => (SecType l) -> (SecType l) -> Privilege l -> FlowArrowRef l a b c -> a b c
certifyRef l_in l_out priv@(PR user_label) f@(FARef c pc' t g) =
      let (FARef c' pc'' t' g') = adduniset f in
      let sym = unify (uniset c') in
--      error $ "Constraint : " ++ (show t') ++ "\n\nGConstraint : " ++ (show g') ++ "\n\nUnify : " ++ (show (uniset c'))
--              ++ "\n\nFlow : " ++ (show (flow c')) ++ "\n\nSym : " ++ (show sym)
      let (pc''', t'', g'') = (resolve_pc sym pc'', resolve_cons sym t', resolve_gcons sym g') in
      if not $ label_leq (mext_join l_in) pc''' then
        error $ "pc level mismatch : " ++ (show pc''') 
      else if not $ (check_constraints user_label t'') && (check_gconstraints user_label g'') then
        error $ "Ref constraints cannot be met : " ++ (show t'')  ++ (show g'')
      else
        certify l_in l_out priv c'  
  where
  varIn (Trans s1 s2) = if hasVarSecType s1 then [(Id l_in, Id s1)] else [] 
  adduniset (FARef (FA c f con gcon u) pc' t g) = (FARef (FA c f con gcon ((varIn f)++u)) pc' t g)

certifyRefL :: (Lattice l, Show (Constraint l)) 
              => (SecType l) -> l -> Privilege l -> FlowArrowRef l a b c -> a b c
certifyRefL l_in l_out priv@(PR user_label) f@(FARef c pc' t g) =
      let (FARef c' pc'' t' g') = adduniset f in
      let sym = unify (uniset c') in
--      error $ "Constraint : " ++ (show t') ++ "\n\nGConstraint : " ++ (show g') ++ "\n\nUnify : " ++ (show (uniset c'))
--              ++ "\n\nFlow : " ++ (show (flow c')) ++ "\n\nSym : " ++ (show sym)
      let (pc''', t'', g'') = (resolve_pc sym pc'', resolve_cons sym t', resolve_gcons sym g') in
      if not $ label_leq (mext_join l_in) pc''' then
        error $ "pc level mismatch : " ++ (show pc''')
      else if not $ (check_constraints user_label t'') && (check_gconstraints user_label g'') then
        error $ "Ref constraints cannot be met : " ++ (show t'')  ++ (show g'')
      else
        certifyL l_in l_out priv c'  
  where
  varIn (Trans s1 s2) = if hasVarSecType s1 then [(Id l_in, Id s1)] else [] 
  adduniset (FARef (FA c f con gcon u) pc' t g) = (FARef (FA c f con gcon ((varIn f)++u)) pc' t g)

{------------------------------------------------
   Help function to resolve (SecType l) to l. 
-------------------------------------------------}
resolve_pc :: Lattice l => [(SecType l, SecType l)] -> (SecType l) -> l
resolve_pc sym s = (unLabel.unSecLabel) (replace_pc sym s)

resolve_gcons :: Lattice l => 
                 [(SecType l, SecType l)] -> [GConstraint (SecType l)] -> [GConstraint (SecType l)]
resolve_gcons = replace_gcons 

type AuthDB = (((String, String), TriLabel),((String, String), TriLabel))

authenticate :: (FlowArrowRef TriLabel ArrowRef () AuthDB)
  -> String -> String -> IO (String, Privilege TriLabel)
authenticate adb username password =
  let res = adb >>> pure (\(((na,pa),padmin),((ng,pg),pguest)) -> 
                      if username == "admin" && password == pa 
                        then (na,PR padmin)
                        else if username == "guest" && password == pg
                               then (ng,PR pguest)
                               else ("nobody",PR LOW)) >>>
            declassifyRef LOW --(Pair (SecLabel (Lab LOW)) (SecLabel (Lab LOW)))
  in
  runArrowRef (certifyRef (SecLabel (Lab LOW)) (Pair (SecLabel (Lab LOW)) (SecLabel (Lab LOW)) ) (PR HIGH) res) ()
  where finder (u,p,_)= username==u && password==p

{-  
authenticate :: (FlowArrow TriLabel (->) () AuthDB) 
  ->String->String -> (String, Privilege TriLabel)
authenticate adb username password = 
  let res = adb >>> proc db -> do
      declassify HIGH LOW -< 
       case find finder db of
        Nothing         -> ("nobody", PR LOW)
        Just (u,p,priv) -> (u, PR priv)
  in 
  cert (PR HIGH) res ()
  where finder (u,p,_)= username==u && password==p
-}

{---------------------------------------------------------------------
  FlowArrowRef
----------------------------------------------------------------------}

replace_pc :: Lattice l => [(SecType l, SecType l)] -> (SecType l) -> (SecType l)
replace_pc = replaceSecType

replace_gcons :: Lattice l => [(SecType l, SecType l)] -> [GConstraint (SecType l)] -> [GConstraint (SecType l)]
replace_gcons sub = map (replace_gcon sub)

replace_gcon sub (GUARD t1 t2) = GUARD (replaceSecType sub t1) (replaceSecType sub t2)
replace_gcon sub (GSLEQL t1 t2) = GSLEQL (replaceSecType sub t1) (replaceSecType sub t2)
replace_gcon sub (GLLEQS t1 t2) = GLLEQS (replaceSecType sub t1) (replaceSecType sub t2)

data FlowArrowRef l a b c = FARef { flowarrow :: FlowArrow l a b c
                                    , pc :: (SecType l)
                                    , constraintsRef :: [Constraint (SecType l)]
                                    , gconstraintsRef :: [GConstraint (SecType l)] 
                                    }

instance (Lattice l, Arrow a, Arrow (FlowArrow l a)) => 
          Arrow (FlowArrowRef l a) where
  pure f = FARef { flowarrow = pure f
                 , pc = (SecLabel (Lab label_top))
                 , constraintsRef = []
                 , gconstraintsRef = []
                 }
  (FARef fa1 pc1 c1 g1) >>> (FARef fa2 pc2 c2 g2) =
     let pc' = (SecLabel (LVar "x0")) in
     let (sub1,sub2,[(_,pc'')]) = make_sub fa1 fa2 [pc'] in
     FARef { flowarrow = addUniset (fa1 >>> fa2) [(Id pc'',Meet (Id (replace_pc sub1 pc1)) (Id (replace_pc sub2 pc2)))]
           , pc = pc''
           , constraintsRef = (replace_cons sub1 c1) ++ (replace_cons sub2 c2)
           , gconstraintsRef = (replace_gcons sub1 g1) ++ (replace_gcons sub2 g2)
           }
  first (FARef fa pc cr gr) = 
      let (sub1,sub2,_) = make_sub_partial fa idflow [] in
      FARef { flowarrow = first fa
            , pc = (replace_pc sub1 pc)            
            , constraintsRef = (replace_cons sub1 cr)
            , gconstraintsRef = (replace_gcons sub1 gr)
            }
  second (FARef fa pc cr gr) = 
      let (sub1,sub2,_) = make_sub_partial fa idflow [] in
      FARef { flowarrow = second fa
            , pc = (replace_pc sub1 pc) 
            , constraintsRef = (replace_cons sub1 cr)
            , gconstraintsRef = (replace_gcons sub1 gr)
         }
  (FARef fa1 pc1 c1 g1) *** (FARef fa2 pc2 c2 g2) =
      let pc' = (SecLabel (LVar "x0")) in
      let (sub1,sub2,[(_,pc'')]) = make_sub fa1 fa2 [pc'] in
      FARef { flowarrow = addUniset (fa1 *** fa2) [(Id pc'',Meet (Id (replace_pc sub1 pc1)) (Id (replace_pc sub2 pc2)))]
            , pc = pc''
            , constraintsRef = (replace_cons sub1 c1) ++ (replace_cons sub2 c2)
            , gconstraintsRef = (replace_gcons sub1 g1) ++ (replace_gcons sub2 g2)
            }
  (FARef fa1 pc1 c1 g1) &&& (FARef fa2 pc2 c2 g2) =
      let pc' = (SecLabel (LVar "x0")) in
      let (sub1, sub2,[(_,pc'')]) = make_sub fa1 fa2 [pc'] in
      FARef { flowarrow = addUniset (fa1 &&& fa2) [(Id pc'',Meet (Id (replace_pc sub1 pc1)) (Id (replace_pc sub2 pc2)))]
            , pc = pc''
            , constraintsRef = (replace_cons sub1 c1)++(replace_cons sub2 c2)
            , gconstraintsRef = (replace_gcons sub1 g1) ++ (replace_gcons sub2 g2)
            }


instance (Lattice l, ArrowChoice a, ArrowChoice (FlowArrow l a)) => 
    ArrowChoice (FlowArrowRef l a) where
  left (FARef fa pc cr gr) = 
    let (sub1,sub2,_) = make_sub_partial fa idflow [] in
      FARef { flowarrow = left fa
            , pc = (replace_pc sub1 pc)
            , constraintsRef = (replace_cons sub1 cr)
            , gconstraintsRef = (replace_gcons sub1 gr)  
            }
  right (FARef fa pc cr gr) = 
    let (sub1,sub2,_) = make_sub_partial fa idflow [] in
      FARef { flowarrow = right fa
            , pc = (replace_pc sub1 pc)
            , constraintsRef = (replace_cons sub1 cr) 
            , gconstraintsRef = (replace_gcons sub1 gr)
            }
  (FARef fa1 pc1 cr1 gr1) +++ (FARef fa2 pc2 cr2 gr2) =
    let fa@(FA _ f _ _ _)     = fa1 +++ fa2  in
    let (Trans s_in s_out ) = f  in
    let pc' = (SecLabel (LVar "x0")) in
    let l_out' = (SecLabel (LVar "x1")) in
    let (sub1,sub2,[(_,pc''),(_,l_out'')]) = make_sub fa1 fa2 [pc',l_out'] in
      FARef { flowarrow = addUniset fa [(Id pc'',Meet (Id (replace_pc sub1 pc1)) (Id (replace_pc sub2 pc2)))
                                       ,(Id l_out'',LExtr (Id s_out))]
            , pc = pc''
            , constraintsRef = (replace_cons sub1 cr1)++(replace_cons sub2 cr2)
            , gconstraintsRef = (replace_gcons sub1 gr1) ++ (replace_gcons sub2 gr2) 
                                ++ [GSLEQL s_in pc'', GSLEQL s_in l_out'']
            }
  (FARef fa1 pc1 cr1 gr1) ||| (FARef fa2 pc2 cr2 gr2) =
    let fa@(FA _ f _ _ _)     = fa1 ||| fa2  in
    let (Trans s_in s_out ) = f  in
    let pc' = (SecLabel (LVar "x0")) in
    let l_out' = (SecLabel (LVar "x1")) in
    let (sub1,sub2,[(_,pc''),(_,l_out'')]) = make_sub fa1 fa2 [pc',l_out'] in
      FARef { flowarrow = addUniset fa [(Id pc'',Meet (Id (replace_pc sub1 pc1)) (Id (replace_pc sub2 pc2)))
                                       ,(Id l_out'',LExtr (Id s_out))]
            , pc = pc''
            , constraintsRef = (replace_cons sub1 cr1)++(replace_cons sub2 cr2)
            , gconstraintsRef = (replace_gcons sub1 gr1) ++ (replace_gcons sub2 gr2) 
                                ++ [GSLEQL s_in pc'', GSLEQL s_in l_out'']
            }

{-
instance (Lattice l, ArrowLoop a, ArrowLoop (FlowArrow l a)) =>
         ArrowLoop (FlowArrowRef l a) where
  loop (FARef fa pc cr gr) =
     FARef { flowarrow = loop fa
           , pc = pc
           , constraintsRef = []
           , gconstraintsRef = []
           }
-}

addUniset (FA c f con gcon uniset) us = (FA c f con gcon (us++uniset)) 

{-----------------------------------------------------------------------------
 References primitives
------------------------------------------------------------------------------}

data FlowEnv a = FlowEnv {
      user_data  :: a,                     -- real compuatation data
      lock_ref   :: TVar Bool,             -- lock reference
      p_count    :: Int,                   -- nested protect count
      job_que    :: TVar [ThreadId],       -- round-robin job queue
      ident      :: ThreadId               -- identify of the thread
   }

data ArrowRef a b = AR ((FlowEnv a) -> IO (FlowEnv b)) 

unAR (AR f) = f

runArrowRef (AR f) a = do l <- newLockRef
                          myid <- myThreadId
                          q <- newThreadQueue myid
                          env' <- f (FlowEnv a l 0 q myid)
                          return (user_data env')

newOrder = atomically $ newTVar []

instance Arrow ArrowRef where
  pure f = AR (\env -> do lock env
                          b <- return $ f (user_data env)
                          unlock env
                          return env{ user_data = b } )
              
  (AR f) >>> (AR g) =
     AR (\env -> f env >>= g)

  first (AR f) =
     AR (\env -> let (b,d) = (user_data env) in
                 f (env{user_data = b}) >>=
                 (\env' -> return env'{user_data = (user_data env',d)}) )

instance Arrow ArrowRef => ArrowChoice ArrowRef where
  left (AR f) = AR (\env -> case (user_data env) of
                              Left d  -> (f env{ user_data = d }) >>= 
                                         (\env' -> return env'{user_data = Left (user_data env')})
                              Right d -> return env{user_data = (Right d)} )

instance Arrow ArrowRef => ArrowLoop ArrowRef where
  loop (AR f) = AR (\env -> do (d,c) <- mfix (\ ~(d,c) -> do env' <- f env{user_data=(user_data env,c)}
                                                             return $ user_data env')
                               return env{user_data=d}    
                   ) 

iterateArrowRef (AR f) = AR (\env -> let ite = (\(env,b) -> if b 
                                                              then do env' <- f env
                                                                      b' <- return (snd (user_data env'))
                                                                      ite (env'{user_data = fst (user_data env')},b')
                                                              else return env)
                                     in
                                     ite (env,True))


class Arrow a => ArrowAtomic a where
  hide :: a b b
  unhide :: a b b

instance ArrowAtomic ArrowRef where
  hide = AR (\env -> do ok <- lock env
                        return env{p_count = ((p_count env)+1)} )

  unhide = AR (\env -> if (p_count env) <= 0 
                       then error "hide and unhide is not well paired."
                       else do unlock env{p_count = ((p_count env)-1)}
                               return env{p_count = ((p_count env)-1)} )

newLockRef :: IO (TVar Bool)
newLockRef = atomically $ newTVar True

newThreadQueue :: ThreadId -> IO (TVar [ThreadId])
newThreadQueue myid = atomically $ newTVar [myid]

lock :: FlowEnv a -> IO Bool
lock env = if (p_count env) > 0
             then return False
             else atomically $
                  do free <- readTVar (lock_ref env)
                     if free == False
                       then retry
                       else do que <- readTVar (job_que env)
                               if head que /= (ident env)
                                 then retry
                                 else do writeTVar (lock_ref env) False
                                         return True

unlock :: FlowEnv a -> IO Bool
unlock env = if (p_count env) > 0
               then return False
               else atomically $
                    do free <- readTVar (lock_ref env)
                       if free == True
                         then error "unlock and lock inconsistent."
                         else do que <- readTVar (job_que env)
                                 writeTVar (job_que env) ((tail que)++[head que])
                                 writeTVar (lock_ref env) True
                                 return True

skip :: FlowEnv Int -> IO ()
skip env = if (user_data env) <= 0
             then return ()
             else do lock env
                     i' <- return ((user_data env)-1)
                     ok <- unlock env
                     skip env{user_data=i'}

skipRef :: (Lattice l) => FlowArrowRef l ArrowRef Int ()
skipRef =
   FARef { flowarrow = FA { computation = (\upd -> AR(\env -> do skip env
                                                                 return env{user_data=()} ))
                          , flow = Trans (SecVar "x0") (SecLabel (Lab label_bottom))
                          , constraints = []
                          , gconstraints = []
                          , uniset = []
                          }
         , pc = SecLabel (Lab label_top)
         , constraintsRef = []
         , gconstraintsRef = []
         }

-- Iteration
iterateA :: Lattice l => 
            FlowArrowRef l ArrowRef a (a,Bool) -> FlowArrowRef l ArrowRef a a
iterateA (FARef (FA f' (Trans fin fout) cons' gcons' uniset') pc' consRef' gconsRef') =
    let vout = (SecVar "x0") in
    FARef { flowarrow = FA { computation = (\upd -> iterateArrowRef (f' upd))
                           , flow = Trans fin vout
                           , constraints = cons'
                           , gconstraints = gcons'
                           , uniset = (Id vout,Fst (Id fout)):uniset'
                           }
          , pc = pc'
          , constraintsRef = consRef'
          , gconstraintsRef = gconsRef'
          }

-- Arrow combinator for atomic execution
protectA :: Lattice l => 
            FlowArrowRef l ArrowRef a b -> FlowArrowRef l ArrowRef a b
protectA (FARef (FA f' flow' cons' gcons' uniset') pc' consRef' gconsRef') =
    FARef { flowarrow = FA { computation = (\upd ->  hide >>> (f' upd) >>> unhide)
                           , flow = flow'
                           , constraints = cons'
                           , gconstraints = gcons'
                           , uniset = uniset'
                           }
          , pc = pc'
          , constraintsRef = consRef'
          , gconstraintsRef = gconsRef'
          }

-- Arrow combinator for filtering high value
lowerA :: (Lattice l, Arrow ar,
         Downgrade SecType l a, Downgrade SecType l b,
         Dummy a, Dummy b, SecFilter SecType l a,
         DowngradeArrow SecType l (FlowArrowRef l ar) a b) 
        => 
          l -> FlowArrowRef l ar a b -> FlowArrowRef l ar a b
lowerA level total@(FARef (FA f flow' cons' gcons' uniset') pc' consRef' gconsRef') =
 if (hasVarSecType pc') || (not (pc' == SecLabel (Lab label_top)) )
   then error $ (show pc') ++ " : only explicit toppest side effect allowed in lowerA."
   else
   let (in_flow, out_flow) = (lowFlow level total) in
   let inputFilter updateVar = pure (\i -> (removeHigh level (updateVar in_flow) i)) in
   FARef { flowarrow = FA { computation = (\upd -> (inputFilter upd) >>> (f upd))
                          , flow = Trans in_flow out_flow
                          , constraints = [] 
                          , gconstraints = []
                          , uniset = [] 
                          }
         , pc = SecLabel (Lab label_top) 
         , constraintsRef = [] 
         , gconstraintsRef = [GLLEQS (SecLabel (Lab level)) in_flow]
         }

-- Implementation of the primitives (they should be in some kind of class, but later!)

forkRef :: (Lattice l) => 
           FlowArrowRef l ArrowRef a b -> FlowArrowRef l ArrowRef a ()
forkRef (FARef (FA com' (Trans f_in f_out) cons' gcons' uniset') pc' consRef' gconsRef') =
   FARef { flowarrow = FA { computation = (\upd -> let t = unAR (initThread >>> (com' upd) >>> endThread ) in
                                                   AR (\env -> do lock env
                                                                  env' <- return env{p_count = 0}
                                                                  nid <-forkIO (((t env') >>= nullThread) 
                                                                                `Control.Exception.catch` 
                                                                                (finalThread env'))
                                                                  newThread env nid
                                                                  unlock env
                                                                  return env{user_data=()}) )
                          , flow = Trans f_in (SecLabel (Lab label_bottom))
                          , constraints = cons'
                          , gconstraints = gcons'
                          , uniset = uniset'
                          }
         , pc = pc'
         , constraintsRef = consRef'
         , gconstraintsRef = gconsRef'
         }
  where
  nullThread = (\_ -> return ())

newThread :: FlowEnv a -> ThreadId -> IO (FlowEnv a)
newThread env nid = do atomically $ do que <- readTVar (job_que env)
                                       writeTVar (job_que env) (que++[nid])
                       return env

initThread :: ArrowRef a a
initThread = AR (\env -> do myId <- myThreadId
                            return env{ident = myId} )


endThread :: ArrowRef a a
endThread = AR (\env -> do atomically $
                            do que <- readTVar (job_que env)
                               writeTVar (job_que env) (filter ((ident env)/=) que) 
                               return que
                           return env )

finalThread :: FlowEnv a -> Exception -> IO ()
finalThread env = (\e -> do atomically $
                              do que <- readTVar (job_que env)
                                 writeTVar (job_que env) (tail que)  
                                 writeTVar (lock_ref env) True
                                 return ()
                            return () )
                          
-- Generate a random number in range (l,h).
randomRRef :: (Lattice l) => Int -> Int -> FlowArrowRef l ArrowRef Int Int
randomRRef l h =
   FARef { flowarrow = FA { computation = (\upd -> AR (\env -> do lock env
                                                                  r <- randomRIO (l,h)
                                                                  unlock env
                                                                  return env{user_data=r} ))
                          , flow = Trans (SecVar "x0") (SecVar "x0")
                          , constraints = []
                          , gconstraints = []
                          , uniset = []
                          }
         , pc = SecLabel (Lab label_top)
         , constraintsRef = []
         , gconstraintsRef = []
         }

-- Not a reference can only point to a simple value, ex. Int.
createRef :: (Lattice l) => l -> FlowArrowRef l ArrowRef b (SecRef b) 
createRef lr = 
   let ld = (SecVar "x0") in
   let pc' = SecLabel (LVar "x1") in
   FARef { flowarrow = FA { computation = (\upd -> AR (\env -> do lock env
                                                                  ref <- createMRef (user_data env)
                                                                  unlock env
                                                                  return env{user_data=ref}) )
                          , flow = Trans ld (Ref ld (Lab lr))
                          , constraints = []  
                          , gconstraints = []
                          , uniset = [(Id pc',LExtr (Id ld))]
                          } 
         , pc = pc'
         , constraintsRef = [] 
         , gconstraintsRef = []
         }

-- We don't know what exactly is the content of the reference. i.e. (UVar True "x0")
readRef :: (Lattice l) => (SecType l) -> FlowArrowRef l ArrowRef (SecRef b) b  
readRef lv =
   let ld = (SecVar "x0") in
   let lr = (LVar "x1") in
   FARef { flowarrow = FA { computation = (\upd -> AR (\env -> do lock env
                                                                  d <- readMRef (user_data env)
                                                                  unlock env
                                                                  return env{user_data=d}) )
                          , flow = Trans (Ref ld lr) lv
                          , constraints = [] 
                          , gconstraints = []
                          , uniset = []
                          }
         , pc = SecLabel (Lab label_top)
         , constraintsRef = [LEQ ld lv]
         , gconstraintsRef = [GUARD (SecLabel lr) lv]
         }

writeRef :: (Lattice l) => FlowArrowRef l ArrowRef (SecRef b, b) ()
writeRef =
    let ld = (SecVar "x0") in
    let lr = (LVar "x1") in
    let pc' = (SecLabel (LVar "x2")) in
	FARef { flowarrow = FA { computation = (\upd -> AR (\env -> 
                                                     do 
                                                       lock env
                                                       writeMRef (fst (user_data env)) (snd (user_data env))
                                                       unlock env
                                                       return env{user_data=()}) )
                           , flow = Trans (Pair (Ref ld lr) ld) 
                                          (SecLabel (Lab label_bottom))
                           , constraints = []
                           , gconstraints = []
                           , uniset = [(Id pc',LExtr (Id ld))]
                           }
          , pc = pc'
          , constraintsRef = []
          , gconstraintsRef = [GUARD (SecLabel lr) ld] 
          }

-- Primitive of Pair

createPair :: Lattice l => 
              (SecType l) -> (SecType l) -> FlowArrowRef l ArrowRef (a,b) (a,b)
createPair t1 t2 =
    FARef { flowarrow = FA { computation = (\upd -> AR (\env -> return env))
                           , flow = Trans (Pair (SecVar "x0") (SecVar "x1"))
                                          (Pair t1 t2)
                           , constraints = []
                           , gconstraints = []
                           , uniset = []
                           }
          , pc = SecLabel (Lab label_top)
          , constraintsRef = [LEQ (Pair (SecVar "x0") (SecVar "x1")) 
                                  (Pair t1 t2)]
          , gconstraintsRef = []
          }

fstPair :: (Lattice l) => FlowArrowRef l ArrowRef (a,b) a
fstPair =
    let s1 = (SecVar "x0") in
    let s2 = (SecVar "x1") in
    FARef { flowarrow = FA { computation = (\upd -> AR (\env -> do lock env
                                                                   d <- return $ fst (user_data env)
                                                                   unlock env
                                                                   return env{user_data=d}) )
                           , flow = Trans (Pair s1 s2) s1
                           , constraints = []
                           , gconstraints = []
                           , uniset = []
                           }
          , pc = SecLabel (Lab label_top)
          , constraintsRef = []
          , gconstraintsRef = []
          }

sndPair :: (Lattice l) => FlowArrowRef l ArrowRef (a,b) b
sndPair =
    let s1 = (SecVar "x0") in
    let s2 = (SecVar "x1") in
    FARef { flowarrow = FA { computation = (\upd -> AR (\env -> do lock env
                                                                   d <- return $ snd (user_data env)
                                                                   unlock env
                                                                   return env{user_data=d}) )
                           , flow = Trans (Pair s1 s2) s2
                           , constraints = []
                           , gconstraints = []
                           , uniset = []
                           }
          , pc = SecLabel (Lab label_top)
          , constraintsRef = []
          , gconstraintsRef = []
          }

