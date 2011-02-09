{-# OPTIONS -fglasgow-exts #-}

module Unification where

import Lattice
import Control.Monad.State

--------------------------
-- Unification datatype --
--------------------------
data U s = Meet (U s) (U s)
         | Join (U s) (U s)
         | Tag (U s) (U s)
         | Decl (U s) (U s) (U s)
         | LExtr (U s) 
         | Fst (U s)
         | Snd (U s)
         | Id s
    deriving (Eq, Show)

-- Unification monad
type CM l a = State (UEnv l) a

-- Unification set
data UEnv l = UEnv (WorkSet l) (ResultSet l)
    deriving (Show)

type WorkSet l = [UPair (U (SecType l))]
type ResultSet l = [UPair (SecType l)]

type UPair s = (s,s)

showPair s1 s2 = "(" ++ (show s1) ++ ", " ++ (show s2) ++ ")"

unify u = evalState (unifyU 0) (UEnv u [])

-------------
-- Unify U --
-------------
unifyU :: Lattice l => Int -> CM l (ResultSet l)
unifyU i =
  do p <- getNextUPair
     case p of
       Nothing -> getResultSet
       (Just n) -> case n of
                     (Id s1, Id s2) -> do
                                       us <- unifySecType (s1,s2)
                                       updateUEnv (updateSecType us)
                                       addResultSet (iterateUpdate us)
                                 --      (UEnv w r) <- get
                                 --      if i > 5
                                 --        then error $ (show w) ++ "\n" ++ (show r)-- ++ "\n" ++ (show us)
                                 --        else unifyU (i+1)
                                       unifyU (i+1)
                     p -> do addWorkSet p
                             unifyU (i+1)

iterateUpdate [] = []
iterateUpdate ((x1,x2):xs) = (updateSecType xs x1,updateSecType xs x2):(iterateUpdate xs)

-- update both WorkSet and ResultSet according to new uni-pairs
updateUEnv :: Lattice l => (SecType l -> SecType l) -> CM l ()
updateUEnv upd = do (UEnv w r) <- get
                    put (UEnv (updateUs upd w) (updateS upd r))

updateS _ [] = []
updateS upd ((x1,x2):xs) = (upd x1,upd x2):(updateS upd xs)

updateUs _ [] = []
updateUs upd ((x1,x2):xs) = (updateU upd x1, updateU upd x2):(updateUs upd xs)

updateU upd x = if hasVarU x' then x' else Id (simplifyU x')
  where
  x' = updateUType upd x

updateUType upd u = mapUType upd u

mapUType :: (SecType l -> SecType l) -> U (SecType l) -> U (SecType l)
mapUType f u =
  case u of
    Meet u1 u2 -> Meet (mapUType f u1) (mapUType f u2)
    Join u1 u2 -> Join (mapUType f u1) (mapUType f u2)
    Tag u1 u2 -> Tag (mapUType f u1) (mapUType f u2)
    Decl u1 u2 u3 -> Decl (mapUType f u1) (mapUType f u2) (mapUType f u3)
    LExtr u1 -> LExtr (mapUType f u1) 
    Fst u -> Fst (mapUType f u)
    Snd u -> Snd (mapUType f u)
    Id s -> Id (f s)

simplifyU :: Lattice l => (U (SecType l)) -> (SecType l)
simplifyU u = 
  case u of
    Meet u1 u2 -> mlabel_meet (simplifyU u1) (simplifyU u2)
    Join u1 u2 -> mlabel_join (simplifyU u1) (simplifyU u2)
    Tag u1 u2 -> mlabel_tag (simplifyU u1) ((unLabel.unSecLabel) (simplifyU u2))
    Decl u1 u2 u3 -> mlabel_decl (simplifyU u1) (simplifyU u2) ((unLabel.unSecLabel) (simplifyU u3))
    LExtr u1 -> SecLabel $ Lab (mextract (simplifyU u1))
    Fst u1 -> case (simplifyU u1) of
                (Pair s1 s2) -> s1
    Snd u1 -> case (simplifyU u1) of
                (Pair s1 s2) -> s2
    Id s -> s

unSecLabel (SecLabel l) = l
unLabel (Lab l) = l

hasVarU :: (U (SecType l)) -> Bool
hasVarU = propLeafU hasVarSecType (||) 

propLeafU :: (SecType l -> a) -> (a -> a -> a) -> U (SecType l) -> a
propLeafU f con (Meet u1 u2) = (propLeafU f con u1) `con` (propLeafU f con u2)
propLeafU f con (Join u1 u2) = (propLeafU f con u1) `con` (propLeafU f con u2)
propLeafU f con (Tag u1 u2) = (propLeafU f con u1) `con` (propLeafU f con u2)
propLeafU f con (Decl u1 u2 u3) = (propLeafU f con u1) `con` (propLeafU f con u2) `con` (propLeafU f con u3)
propLeafU f con (LExtr u1) = propLeafU f con u1
propLeafU f con (Fst u1) = propLeafU f con u1
propLeafU f con (Snd u1) = propLeafU f con u1
propLeafU f con (Id s) = f s

addResultSet :: ResultSet l -> CM l ()
addResultSet ps = do (UEnv w r) <- get
                     put (UEnv w (ps++r))

addWorkSet :: UPair (U (SecType l)) -> CM l ()
addWorkSet p = do (UEnv w r) <- get
                  put (UEnv (w++[p]) r)

getNextUPair :: CM l (Maybe (UPair (U (SecType l))))
getNextUPair = do (UEnv w r) <- get
                  if length w == 0
                    then return Nothing
                    else do put (UEnv (tail w) r)
                            return (Just (head w))

getResultSet :: CM l (ResultSet l)
getResultSet = do (UEnv w r) <- get
                  return r

-----------------
-- Unify Label --
----------------- 
unifyLabel :: Lattice l => (UPair (Label l)) -> CM l [(UPair (Label l))]
unifyLabel p = case p of
                 (Lab l1,Lab l2)  -> if l1 == l2 
                                       then return []
                                       else error $ "unifyLabel : " ++ showPair l1 l2
                 (t1@(LVar _),t2) -> return [(t1,t2)]
                 (t1,t2@(LVar _)) -> unifyLabel (t2,t1)

-------------------
-- Unify SecType --
-------------------
unifySecType :: Lattice l => (UPair (SecType l)) -> CM l [(UPair (SecType l))]
unifySecType p = 
  case p of
    (SecLabel l1, SecLabel l2) -> do ul <- unifyLabel (l1,l2)
                                     return $ expandMap ul
    (Ref s1 l1, Ref s2 l2) -> do ul <- unifyLabel (l1,l2)
                                 us1 <- return $ expandMap ul
                                 us2 <- unifySecType $ update us1 (s1,s2)
                                 return $ us1 ++ us2
    (Pair s1 s2, Pair s3 s4) -> do us1 <- unifySecType (s1,s3)
                                   us2 <- unifySecType $ update us1 (s2,s4)
                                   return $ us1 ++ us2
    (SecEither s1 s2 l1, SecEither s3 s4 l2) -> 
                                do ul <- unifyLabel (l1,l2)
                                   us1 <- return $ expandMap ul
                                   us2 <- unifySecType $ update us1 (s1,s3)
                                   us3 <- unifySecType $ ((update us2).(update us1)) (s2,s4)
                                   return $ us1 ++ us2 ++ us3
    (SecHigh, SecHigh) -> return []
    (v@(SecVar _), s) -> if v `appearIn` s
                           then error $ "unifySecType : " ++ (show v) ++ " appears in " ++ (show s)
                           else return [(v,s)]
    (s, v@(SecVar _)) -> unifySecType (v,s)
    (SecHigh, SecLabel l) -> do ul <- unifyLabel (Lab label_top,l)
                                return $ expandMap ul
{-
    (SecHigh, Ref s l) -> do ul <- unifyLabel (Lab label_top, l)
                             us1 <- return $ expandMap ul
                             us2 <- unifySecType $ update us1 (SecHigh,s)
                             return $ us1 ++ us2
-}
    (SecHigh, Pair s1 s2) -> do us1 <- unifySecType (SecHigh,s1)
                                us2 <- unifySecType $ update us1 (SecHigh,s2)
                                return $ us1 ++ us2
    (SecHigh, SecEither s1 s2 l) -> do ul <- unifyLabel (Lab label_top, l)
                                       us1 <- return $ expandMap ul
                                       us2 <- unifySecType $ update us1 (SecHigh,s1)
                                       us3 <- unifySecType $ ((update us2).(update us1)) (SecHigh,s2)
                                       return $ us1 ++ us2 ++ us3 
    (s, SecHigh) -> unifySecType (SecHigh, s)
    (s1, s2) -> error $ "unifySecType : " ++ showPair s1 s2
  where
  expandMap = map expand
  expand (s1,s2) = (SecLabel s1,SecLabel s2)
  update u (s1,s2) = (updateSecType u s1,updateSecType u s2)
  appearIn v1 v2@(SecVar t) = v1 == v2
  appearIn v SecHigh = False
  appearIn v (SecLabel _) = False
  appearIn v s = propLeaf (appearIn v) (||) s
  
---------------------------------------------------------------
-- Update a SecType according to a list of unification pairs --
---------------------------------------------------------------
updateSecType :: Lattice l => [UPair (SecType l)] -> (SecType l) -> (SecType l)
updateSecType uset t = foldl updateSec t uset

updateSec :: Lattice l => (SecType l) -> (UPair (SecType l)) -> (SecType l)
updateSec t pat@(v1@(SecVar _),new) =
  case t of
    (Ref s l) -> Ref (updateSec s pat) l
    (Pair s1 s2) -> Pair (updateSec s1 pat) (updateSec s2 pat)
    (SecEither s1 s2 l) -> SecEither (updateSec s1 pat) (updateSec s2 pat) l
    v2@(SecVar _) -> if v1 == v2 then new else v2
    s -> s
updateSec t pat@(SecLabel v1@(LVar _),SecLabel new) =
  case t of
    s@(SecLabel l) -> if v1 == l then (SecLabel new) else s
    (Ref s l) -> if v1 == l then Ref (updateSec s pat) new else Ref (updateSec s pat) l
    (Pair s1 s2) -> Pair (updateSec s1 pat) (updateSec s2 pat)
    (SecEither s1 s2 l) -> if v1 == l then SecEither (updateSec s1 pat) (updateSec s2 pat) new
                                      else SecEither (updateSec s1 pat) (updateSec s2 pat) l
    s -> s

hasVarSecType :: (SecType l) -> Bool
hasVarSecType = propLeaf isVarSecType (||) 

isVarSecType (SecVar _) = True
isVarSecType (SecLabel (LVar _)) = True
isVarSecType _ = False

{-
-- old version

--------------------------
-- Unification datatype --
--------------------------
type ResultSet l = [(U s, U s)]
type WorkingSet l = [(U s, U s)] 

----------------------------------------------
-- Unification algorithm. By Alan Robinson. --
----------------------------------------------
unify :: (Eq l, Show l, Lattice l) => ResultSet l -> WorkingSet l -> ResultSet l
unify r [] = r
unify r (w@(e1,e2):ws) = 
  if (e1 == e2) || (eqVar e1 e2) then unify r ws
              else
                case w of
                  (t@(UVar _ v), s) -> if t `appears` s 
                                         then error "#1 Unification failure!"
                                         else unify ((t,s):(replaceAll t s r)) (replaceAll t s ws)
                  (s, t@(UVar _ v)) -> if t `appears` s
                                         then error "#2 Unification failure!"
                                         else unify ((t,s):(replaceAll t s r)) (replaceAll t s ws)
                  (f1, f2) -> unify r (ws++(splitFunctor f1 f2))
  where
    splitFunctor (USecLabel l1) (USecLabel l2) = [(l1,l2)]
    splitFunctor (USecLabel l1) (UHigh) = [(l1,UHigh)]
    splitFunctor (UHigh) (USecLabel l2) = [(UHigh,l2)]
    splitFunctor (URef t1 l1) (URef t2 l2) = [(t1,t2),(l1,l2)]
    splitFunctor (URef t1 l1) (UHigh) = [(t1,UHigh),(l1,UHigh)]
    splitFunctor (UHigh) (URef t2 l2) = [(UHigh,t2),(UHigh,l2)]
    splitFunctor (UPair t1 s1 l1) (UPair t2 s2 l2) = [(t1,t2),(s1,s2),(l1,l2)]
    splitFunctor (UPair t1 s1 l1) (UHigh) = [(t1,UHigh),(s1,UHigh),(l1,UHigh)]
    splitFunctor (UHigh) (UPair t2 s2 l2) = [(UHigh,t2),(UHigh,s2),(UHigh,l2)]
    splitFunctor (UEither t1 s1) (UEither t2 s2) = [(t1,t2),(s1,s2)]
    splitFunctor (UEither t1 s1) (UHigh) = [(t1,UHigh),(s1,UHigh)]
    splitFunctor (UHigh) (UEither t2 s2) = [(UHigh,t2),(UHigh,s2)]
    splitFunctor _ (UAnything) = []
    splitFunctor (UAnything) t = splitFunctor t (UAnything)
    splitFunctor (UFst (UPair t1 _ _)) t2 = splitFunctor t1 t2
    splitFunctor t1@(UFst _) t2 = [(t1,t2)]
    splitFunctor t1 (UFst (UPair t2 _ _)) = splitFunctor t1 t2
    splitFunctor t1 t2@(UFst _) = [(t1,t2)]
--  special attention for (ULat _)
    splitFunctor (UHigh) (ULat t) = if t == label_top then [] else error "#4 Unification failure"
    splitFunctor (ULat t) (UHigh) = splitFunctor (UHigh) (ULat t)
    splitFunctor t1 s1 = error ("#3 Unification failure! " ++ (show t1) ++ " with  " ++ (show s1))
    v `appears` (ULat _) = False
    v `appears` s@(UVar _ t) = eqVar v s
    v `appears` (UHigh) = False
    v `appears` (UAnything) = False
    v `appears` s = propUTypeLeaf (appears v) (||) s
    replacePair v s (e1,e2) = (replaceUType v s e1, replaceUType v s e2)
    replaceAll v s ws = map (replacePair v s) ws 
                                                 
-----------------------------------------------
-- Replace a variable with another (Utype l) --
-----------------------------------------------
replaceUType :: UType l -> UType l -> UType l -> UType l
replaceUType v1@(UVar _ _) s v2@(UVar _ _) = if (eqVar v1 v2) then s else v2
replaceUType _ s t@(ULat l) = t
replaceUType v s (USecLabel l) = USecLabel (replaceUType v s l)
replaceUType v s (URef t l) = URef (replaceUType v s t) (replaceUType v s l)
replaceUType v s (UPair t1 t2 l) = UPair (replaceUType v s t1) (replaceUType v s t2) (replaceUType v s l)
replaceUType v s (UEither t1 t2) = UEither (replaceUType v s t1) (replaceUType v s t2)
replaceUType v s (UMeet t1 t2) = UMeet (replaceUType v s t1) (replaceUType v s t2)
replaceUType v s (UJoin t1 t2) = UJoin (replaceUType v s t1) (replaceUType v s t2)
replaceUType v s (UExtract t) = UExtract (replaceUType v s t)
replaceUType _ s (UHigh) = UHigh
replaceUType _ s (UAnything) = UAnything
replaceUType v s (UFst t) = UFst (replaceUType v s t)

----------------------------------------------
-- Check if two Uvar is with the same name. --
-- Currently served as equivalence of UVar. --
----------------------------------------------
eqVar (UVar _ s1) (UVar _ s2) = s1 == s2
eqVar _ _ = False


---------------------------------------------
-- Check if a (UType l) contains variables --
---------------------------------------------
hasVar = propUTypeLeaf (checkLeaf isVar) (||)

---------------------------------------------------------------
-- Check if a (UType l) contains forward-dependent variables --
---------------------------------------------------------------
hasForwardVar = propUTypeLeaf (checkLeaf forwardVar) (||)

----------------------------------------------------------------
-- Check if a (UType l) contains backward-dependent variables --
----------------------------------------------------------------
hasBackwardVar = propUTypeLeaf (checkLeaf $ not.forwardVar) (||)
  
checkLeaf f v@(UVar _ _) = f v
checkLeaf f (ULat _) = False
checkLeaf f (UHigh) = False
checkLeaf f (UAnything) = False

forwardVar (UVar True _) = True
forwardVar (UVar False _) = False
forwardVar _ = error "Error in hasForwardVar."

isVar (UVar _ _) = True
isVar _ = False

-------------------------------------------------------
-- Type a and type b can be transformed to the other --
-------------------------------------------------------
class Convert a b where
  toSlave :: a -> b
  toMaster :: b -> a

instance Lattice l => Convert (SecType l) (UType l) where
  toSlave (SecLabel l) = (USecLabel (ULat l))
  toSlave (Ref t l) = (URef (toSlave t) (ULat l))
  toSlave (Pair t1 t2 l) = (UPair (toSlave t1) (toSlave t2) (ULat l))
  toMaster t = case buildSec t of
            (Just s) -> s
            Nothing  -> error "UType to SecType failed!"

instance Lattice l => Convert l (UType l) where
  toSlave l = (ULat l)
  toMaster t = case buildLat t of
                 (Just l) -> l
                 Nothing -> error "UType to Lattice failed!"

-------------------------------------------
-- Transform from (UType l) to SecType l --
-------------------------------------------
buildSec :: Lattice l => UType l -> Maybe (SecType l) 
buildSec (UVar _ _) = fail "Variable is not permitted."
buildSec (USecLabel (ULat l)) = return (SecLabel l)
buildSec (USecLabel (UHigh)) = return (SecLabel label_top)
buildSec (UHigh) = return SecHigh
buildSec (UAnything) = return SecHigh
buildSec (URef t lab) = do
                          t' <- buildSec t
                          l  <- buildLat lab
                          return (Ref t' l)
buildSec (UPair t1 t2 lab) = do
                               t1' <- buildSec t1
                               t2' <- buildSec t2
                               l   <- buildLat lab
                               return (Pair t1' t2' l)
buildSec (UMeet t1 t2) = do
                           t1' <- buildSec t1
                           t2' <- buildSec t2
                           return (mlabel_meet t1' t2')
buildSec (UJoin t1 t2) = do
                           t1' <- buildSec t1
                           t2' <- buildSec t2
                           return (mlabel_join t1' t2')
buildSec (UFst t) = do (Pair t1 _ _) <- buildSec t
                       return t1
buildSec t = error $ "Not a valid pattern in buildSec : " ++ (show t)

----------------------------------------
-- Transform from (UType l) to l      --
----------------------------------------
buildLat :: Lattice l => UType l -> Maybe l
buildLat (ULat l) = return l
buildLat (UHigh) = return label_top
buildLat (UMeet l1 l2) = do l1' <- buildLat l1
                            l2' <- buildLat l2
                            return (label_meet l1' l2')
buildLat (UJoin l1 l2) = do l1' <- buildLat l1
                            l2' <- buildLat l2
                            return (label_join l1' l2')
buildLat (UExtract t) = do t' <- buildSec t
                           return $ mextract t'
buildLat t = error $ "Not a valid pattern in buildLat : " ++ (show t)
-}
----------------------------------------
-- Test program for unify             --
----------------------------------------
test = unify    [ (Id (SecLabel (Lab HIGH)), Id (SecLabel (LVar "a1")))
                , (Id (Ref (SecLabel (LVar "a2")) (Lab LOW))
                  ,(Id (Ref (SecLabel (LVar "a2")) (LVar "a6")))) 
                , (Id (Ref (SecLabel (LVar "a1")) (LVar "a2")), Id (Ref (SecLabel (LVar "a2")) (LVar "a3")))
                , (Id (Ref (SecLabel (LVar "a2")) (LVar "a6")), Id (Ref (SecVar "a4") (LVar "a5")))
                , (Meet (Id (SecLabel (Lab LOW))) (Id (SecLabel (Lab HIGH))), Id (SecVar "a7"))
                ]
