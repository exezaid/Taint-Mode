
module BidLattice where

import Lattice

data BidLabel = SYS | USER
  deriving (Eq, Show)

instance Lattice BidLabel where
  label_top = USER
  label_bottom = SYS
  label_join x y = if label_leq x y then y else x
  label_meet x y = if label_leq x y then x else y
  label_leq USER SYS = False
  label_leq _ _ = True
