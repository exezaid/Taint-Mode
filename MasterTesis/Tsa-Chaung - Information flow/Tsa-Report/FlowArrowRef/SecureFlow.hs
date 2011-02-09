{-#  OPTIONS -fglasgow-exts -fallow-undecidable-instances #-}

module SecureFlow where

import Lattice
import Unification
import Control.Arrow
import RefOp
import Priv

import Data.LargeWord
import Codec.Utils

---------------------
-- class Downgrade --
---------------------
s_in = (SecVar "x0")

class (Lattice l) => Downgrade a l t where
  low :: l -> t -> (a l)
  unifyStruct :: t -> (a l)

instance (Lattice l) => Downgrade SecType l () where
  low l t = (SecLabel (Lab l))
  unifyStruct t = s_in

instance (Lattice l) => Downgrade SecType l Int where
  low l t = (SecLabel (Lab l))
  unifyStruct t = s_in

instance (Lattice l, Downgrade SecType l a, Downgrade SecType l b) =>
           Downgrade SecType l (a,b) where
  low l (x,y) = (Pair (low l x) (low l y))
  unifyStruct (x,y) = s_in

instance (Lattice l, Dummy a, Downgrade SecType l a) => 
            Downgrade SecType l (SecRef a) where
  low l (SecRef _ _ ) = (Ref (low l (dummy::a)) (Lab l))
  unifyStruct (SecRef _ _) = s_in

instance (Lattice l, Dummy a, Dummy b, 
          Downgrade SecType l a, Downgrade SecType l b)
          => Downgrade SecType l (Either a b) where
  low l t = (SecEither (low l (dummy::a)) (low l (dummy::b)) (Lab l))
  unifyStruct t = s_in

-- added for Bank System case study
instance Lattice l => Downgrade SecType l [a] where
  low l t = (SecLabel (Lab l))
  unifyStruct t = s_in

instance Lattice l => Downgrade SecType l Word128 where
  low l t = (SecLabel (Lab l))
  unifyStruct t = s_in

instance Lattice l => Downgrade SecType l Bool where
  low l t = (SecLabel (Lab l))
  unifyStruct t = s_in

instance Lattice l => Downgrade SecType l (Privilege TriLabel) where
  low l t = (SecLabel (Lab l))
  unifyStruct t = s_in
  
--------------------------
-- class DowngradeArrow --
--------------------------
class (Lattice l, Arrow a) => DowngradeArrow s l a b c where
  lowFlow :: l -> (a b c) -> (s l, s l)

instance (Lattice l, Downgrade SecType l b, Downgrade SecType l c
         , Dummy b, Dummy c, Arrow a) =>
          DowngradeArrow SecType l a b c where
  lowFlow l t = (unifyStruct (dummy::b), low l (dummy::c))

---------------------
-- class SecFilter --
---------------------
class (Lattice l) => SecFilter a l t where
  removeHigh :: l -> (a l) -> t -> t

instance (Lattice l) => SecFilter SecType l () where
  removeHigh l (SecLabel (Lab l')) t = if label_leq l' l then t else undefined

instance (Lattice l) => SecFilter SecType l Int where
  removeHigh l (SecLabel (Lab l')) t = if label_leq l' l then t else undefined

instance (Lattice l, SecFilter SecType l a, SecFilter SecType l b) =>
         SecFilter SecType l (a,b) where
  removeHigh l (Pair lx ly) (x,y) = (removeHigh l lx x, removeHigh l ly y)
  removeHigh l p pd = error $ (show l) ++ " :: " ++ (show p)  

instance (Lattice l, SecFilter SecType l a) => 
         SecFilter SecType l (SecRef a) where
  removeHigh l (Ref t (Lab l')) (SecRef r fin) = if label_leq l' l 
                                                        then (SecRef r ((removeHigh l t).fin) )
                                                        else undefined

instance Lattice l => SecFilter SecType l [a] where
  removeHigh l (SecLabel (Lab l')) t = if label_leq l' l then t else undefined


instance Lattice l => SecFilter SecType l Word128 where
  removeHigh l (SecLabel (Lab l')) t = if label_leq l' l then t else undefined

instance Lattice l => SecFilter SecType l Bool where
  removeHigh l (SecLabel (Lab l')) t = if label_leq l' l then t else undefined

instance (Lattice l, SecFilter SecType l a, SecFilter SecType l b)
          => SecFilter SecType l (Either a b) where
  removeHigh l (SecEither s1 s2 (Lab l')) (Left a) = if label_leq l' l 
                                                       then Left (removeHigh l s1 a)
                                                       else undefined
  removeHigh l (SecEither s1 s2 (Lab l')) (Right b) = if label_leq l' l
                                                        then Right (removeHigh l s2 b)
                                                        else undefined

-----------------
-- class Dummy --
-----------------
class Dummy t where
  dummy :: t

instance Dummy Int where
  dummy = 0

instance (Dummy a, Dummy b) => Dummy (a,b) where
  dummy = (dummy, dummy)

instance Dummy () where
  dummy = ()

instance Dummy (SecRef a) where
  dummy = SecRef undefined id 

instance Dummy [a] where
  dummy = []

instance Dummy Word128 where
  dummy = 0

instance Dummy Bool where
  dummy = True

instance (Dummy a, Dummy b) => Dummy (Either a b) where
  dummy = Left (dummy::a)

instance Dummy (Privilege TriLabel) where
  dummy = (PR LOW)

------------------------
-- class NoSideEffect --
------------------------
class NoSideEffect t where
  noSE :: t -> Bool

instance NoSideEffect Int where
  noSE a = True

instance (NoSideEffect a, NoSideEffect b) => NoSideEffect (a,b) where
  noSE (a,b) = True

instance NoSideEffect (SecRef a) where
  noSE r = True

instance NoSideEffect () where
  noSE a = True

instance NoSideEffect Bool where
  noSE a = True

instance NoSideEffect Word128 where
  noSE a = True

instance NoSideEffect Octet where
  noSE a = True

instance NoSideEffect a => NoSideEffect [a] where
  noSE a = True

instance (NoSideEffect a, NoSideEffect b) => NoSideEffect (Either a b) where
  noSE a = True

-----------------------------
-- class NoSideEffectArrow --
-----------------------------
class (NoSideEffect c, Arrow a) => NoSideEffectArrow a b c where
  noSideEffect :: (a b c) -> Bool

instance (Dummy c, NoSideEffect c, Arrow a) => NoSideEffectArrow a b c where
  noSideEffect t = noSE (dummy::c)
