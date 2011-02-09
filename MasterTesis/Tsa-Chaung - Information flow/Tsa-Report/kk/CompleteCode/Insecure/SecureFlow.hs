{-#  OPTIONS -fglasgow-exts -fallow-undecidable-instances #-}

module SecureFlow where

import Lattice
import RLattice
import Unification
import Control.Arrow
import RefOp
import Priv
import Data.IORef

class (Lattice l) => BuildSecType l t where
  buildSecType :: l -> t -> SecType l

instance (Lattice l) => BuildSecType l () where
  buildSecType l _ = (SecLabel (Lab l))
instance (Lattice l) => BuildSecType l Int where
  buildSecType l _ = (SecLabel (Lab l))
instance (Lattice l) => BuildSecType l Integer where
  buildSecType l _ = (SecLabel (Lab l))
instance (Lattice l, BuildSecType l a, BuildSecType l b) =>
           BuildSecType l (a,b) where
  buildSecType l _ = (SecPair (buildSecType l (undefined::a)) (buildSecType l (undefined::b)))
instance (Lattice l, STSecType rs l) => 
            BuildSecType l (SRef rs a) where
  buildSecType l _ = (SecRef (toSecType (undefined::rs)) (Lab l))
instance (Lattice l, 
          BuildSecType l a, BuildSecType l b)
          => BuildSecType l (Either a b) where
  buildSecType l _ = (SecEither (buildSecType l (undefined::a)) (buildSecType l (undefined::b)) (Lab l))
-- The following instances are for types used in case studies.
instance Lattice l => BuildSecType l [a] where
  buildSecType l _ = (SecLabel (Lab l))
instance Lattice l => BuildSecType l Bool where
  buildSecType l _ = (SecLabel (Lab l))
instance Lattice l => BuildSecType l (Privilege TriLabel) where
  buildSecType l _ = (SecLabel (Lab l))
  
class (Lattice l, Arrow a) => TakeOutputType l a b c where
  deriveSecType :: l -> (a b c) -> SecType l

instance (Lattice l, BuildSecType l c, Arrow a) =>
          TakeOutputType l a b c where
  deriveSecType l _ = buildSecType l (undefined::c)

class (Lattice l) => FilterData l t where
  removeData :: l -> (SecType l) -> t -> t

instance (Lattice l) => FilterData l () where
  removeData l (SecLabel (Lab l')) t = if label_leq l' l then t else undefined
instance (Lattice l) => FilterData l Int where
  removeData l (SecLabel (Lab l')) t = if label_leq l' l then t else undefined
instance (Lattice l) => FilterData l Integer where
  removeData l (SecLabel (Lab l')) t = if label_leq l' l then t else undefined
instance (Lattice l, FilterData l a, FilterData l b) =>
         FilterData l (a,b) where
  removeData l (SecPair lx ly) (x,y) = (removeData l lx x, removeData l ly y)
  --removeData l p pd = error $ (show l) ++ " :: " ++ (show p)  
instance (Lattice l, STSecType rs l, FilterData l a) => 
         FilterData l (SRef rs a) where
  removeData l (SecRef t (Lab l')) (MkSRef rs c fread) = 
        if label_leq l' l 
          then (MkSRef rs c ((removeData l t).fread))
          else undefined
-- The following instances are for types used in case studies.
instance Lattice l => FilterData l [a] where
  removeData l (SecLabel (Lab l')) t = if label_leq l' l then t else undefined
instance Lattice l => FilterData l Bool where
  removeData l (SecLabel (Lab l')) t = if label_leq l' l then t else undefined
instance (Lattice l, FilterData l a, FilterData l b)
          => FilterData l (Either a b) where
  removeData l (SecEither s1 s2 (Lab l')) (Left a) = if label_leq l' l 
                                                       then Left (removeData l s1 a)
                                                       else undefined
  removeData l (SecEither s1 s2 (Lab l')) (Right b) = if label_leq l' l
                                                        then Right (removeData l s2 b)
                                                        else undefined
  
class ResetProject t where
  resetProject :: t -> t
  resetProject = id

instance ResetProject () 
instance ResetProject Int
instance ResetProject Integer
instance (ResetProject a, ResetProject b) 
         => ResetProject (a,b) where
  resetProject (a,b) = (resetProject a, resetProject b)
instance ResetProject (SRef rs a) where
  resetProject (MkSRef rs a fread) = (MkSRef rs a id)
instance ResetProject [a]
instance ResetProject Bool
instance (ResetProject a, ResetProject b) 
         => ResetProject (Either a b) where
  resetProject (Left a) = Left (resetProject a)
  resetProject (Right b) = Right (resetProject b)

