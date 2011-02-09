{-# OPTIONS -fglasgow-exts #-}

module Unification where

import Lattice
import Control.Monad.State

-- Unification constraints
data U s = Meet (U s) (U s)
         | Join (U s) (U s)
         | Decl (U s) (U s) (U s)
         | Tag (U s) (U s)
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

unify u = evalState unifyU (UEnv u [])

-- Unification of U 
unifyU :: Lattice l => CM l (ResultSet l)
unifyU =
  do p <- getNextUPair
     case p of
       Nothing -> getResultSet
       (Just n) -> case n of
                     (Id s1, Id s2) -> do
                                       us <- unifySecType (s1,s2)
                                       updateUEnv (updateSecType us)
                                       addResultSet (iterateUpdate us)
                                       (UEnv w r) <- get
                                       unifyU
                     p -> do addWorkSet p
                             unifyU

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
    Decl u1 u2 u3 -> Decl (mapUType f u1) (mapUType f u2) (mapUType f u3)
    Tag u1 u2 -> Tag (mapUType f u1) (mapUType f u2)
    LExtr u1 -> LExtr (mapUType f u1) 
    Fst u -> Fst (mapUType f u)
    Snd u -> Snd (mapUType f u)
    Id s -> Id (f s)

-- Resolve unification constraints
simplifyU :: Lattice l => (U (SecType l)) -> (SecType l)
simplifyU u = 
  case u of
    Meet u1 u2 -> min (simplifyU u1) (simplifyU u2)
    Join u1 u2 -> max (simplifyU u1) (simplifyU u2)
    Decl u1 u2 u3 -> ml_decl (simplifyU u1) (simplifyU u2) ((unLabel.unSecLabel) (simplifyU u3))
    Tag u1 u2 -> ml_tag (simplifyU u1) ((unLabel.unSecLabel) (simplifyU u2))
    LExtr u1 -> SecLabel $ Lab (mextract (simplifyU u1))
    Fst u1 -> case (simplifyU u1) of
                (SecPair s1 s2) -> s1
    Snd u1 -> case (simplifyU u1) of
                (SecPair s1 s2) -> s2
    Id s -> s

unSecLabel (SecLabel l) = l
unLabel (Lab l) = l

hasVarU :: (U (SecType l)) -> Bool
hasVarU = propLeafU hasVarSecType (||) 

propLeafU :: (SecType l -> a) -> (a -> a -> a) -> U (SecType l) -> a
propLeafU f con (Meet u1 u2) = (propLeafU f con u1) `con` (propLeafU f con u2)
propLeafU f con (Join u1 u2) = (propLeafU f con u1) `con` (propLeafU f con u2)
propLeafU f con (Decl u1 u2 u3) = (propLeafU f con u1) `con` (propLeafU f con u2) `con` (propLeafU f con u3)
propLeafU f con (Tag u1 u2) = (propLeafU f con u1) `con` (propLeafU f con u2)
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

-- Unification of security labels
unifyLabel :: Lattice l => (UPair (Label l)) -> CM l [(UPair (Label l))]
unifyLabel p = case p of
                 (Lab l1,Lab l2)  -> if l1 == l2 
                                       then return []
                                       else error $ "unifyLabel : " ++ showPair l1 l2
                 (t1@(LVar _),t2) -> return [(t1,t2)]
                 (t1,t2@(LVar _)) -> unifyLabel (t2,t1)

-- Unification of SecType 
unifySecType :: Lattice l => (UPair (SecType l)) -> CM l [(UPair (SecType l))]
unifySecType p = 
  case p of
    (SecLabel l1, SecLabel l2) -> do ul <- unifyLabel (l1,l2)
                                     return $ expandMap ul
    (SecRef s1 l1, SecRef s2 l2) -> do ul <- unifyLabel (l1,l2)
                                       us1 <- return $ expandMap ul
                                       us2 <- unifySecType $ update us1 (s1,s2)
                                       return $ us1 ++ us2
    (SecPair s1 s2, SecPair s3 s4) -> do us1 <- unifySecType (s1,s3)
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
    (SecHigh, SecPair s1 s2) -> do us1 <- unifySecType (SecHigh,s1)
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
  
-- Update a SecType according to a list of unification pairs. 
updateSecType :: Lattice l => [UPair (SecType l)] -> (SecType l) -> (SecType l)
updateSecType uset t = foldl updateSec t uset

updateSec :: Lattice l => (SecType l) -> (UPair (SecType l)) -> (SecType l)
updateSec t pat@(v1@(SecVar _),new) =
  case t of
    (SecRef s l) -> SecRef (updateSec s pat) l
    (SecPair s1 s2) -> SecPair (updateSec s1 pat) (updateSec s2 pat)
    (SecEither s1 s2 l) -> SecEither (updateSec s1 pat) (updateSec s2 pat) l
    v2@(SecVar _) -> if v1 == v2 then new else v2
    s -> s
updateSec t pat@(SecLabel v1@(LVar _),SecLabel new) =
  case t of
    s@(SecLabel l) -> if v1 == l then (SecLabel new) else s
    (SecRef s l) -> if v1 == l then SecRef (updateSec s pat) new else SecRef (updateSec s pat) l
    (SecPair s1 s2) -> SecPair (updateSec s1 pat) (updateSec s2 pat)
    (SecEither s1 s2 l) -> if v1 == l then SecEither (updateSec s1 pat) (updateSec s2 pat) new
                                      else SecEither (updateSec s1 pat) (updateSec s2 pat) l
    s -> s

hasVarSecType :: (SecType l) -> Bool
hasVarSecType = propLeaf isVarSecType (||) 

isVarSecType (SecVar _) = True
isVarSecType (SecLabel (LVar _)) = True
isVarSecType _ = False

