{-# OPTIONS -fglasgow-exts #-}

module BidLattice where

import Lattice
import RLattice

data BidLabel = SYS | USER
  deriving (Eq, Show)

instance Lattice BidLabel where
  label_top = USER
  label_bottom = SYS
  label_join x y = if label_leq x y then y else x
  label_meet x y = if label_leq x y then x else y
  label_leq USER SYS = False
  label_leq _ _ = True

data RSys  = MkSys  deriving Show
data RUser = MkUser deriving Show

instance STLabel RSys BidLabel where
  toLabel _ = SYS

instance STLabel RUser BidLabel where
  toLabel _ = USER

