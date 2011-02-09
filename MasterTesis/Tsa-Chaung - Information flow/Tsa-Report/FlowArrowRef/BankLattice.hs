
module BankLattice where

import Lattice

data BankLabel = CLIENT | BANK | ATM_BANK | BANK_ATM | TOP | BOTTOM
  deriving (Eq, Show)

instance Lattice BankLabel where
  label_top = TOP
  label_bottom = BOTTOM

  label_leq BOTTOM _ = True
  label_leq _ TOP = True
  label_leq CLIENT CLIENT = True
  label_leq ATM_BANK ATM_BANK = True
  label_leq ATM_BANK BANK = True
  label_leq BANK_ATM BANK_ATM = True
  label_leq BANK_ATM BANK = True
  label_leq BANK BANK = True
  label_leq _ _ = False

  label_join TOP _ = TOP
  label_join _ TOP = TOP
  label_join BOTTOM y = y
  label_join x BOTTOM = x
  label_join CLIENT BANK = TOP
  label_join BANK CLIENT = TOP
  label_join CLIENT ATM_BANK = TOP
  label_join ATM_BANK CLIENT = TOP
  label_join CLIENT BANK_ATM = TOP
  label_join BANK_ATM CLIENT = TOP
  label_join BANK ATM_BANK = BANK
  label_join ATM_BANK BANK = BANK
  label_join BANK BANK_ATM = BANK
  label_join BANK_ATM BANK = BANK
  label_join ATM_BANK BANK_ATM = BANK
  label_join BANK_ATM ATM_BANK = BANK
  label_join CLIENT CLIENT = CLIENT
  label_join BANK BANK = BANK
  label_join ATM_BANK ATM_BANK = ATM_BANK
  label_join BANK_ATM BANK_ATM = BANK_ATM

  label_meet BOTTOM _ = BOTTOM
  label_meet _ BOTTOM = BOTTOM
  label_meet TOP y = y
  label_meet x TOP = x
  label_meet CLIENT BANK = BOTTOM
  label_meet BANK CLIENT = BOTTOM
  label_meet CLIENT ATM_BANK = BOTTOM
  label_meet ATM_BANK CLIENT = BOTTOM
  label_meet CLIENT BANK_ATM = BOTTOM
  label_meet BANK_ATM CLIENT = BOTTOM
  label_meet BANK ATM_BANK = ATM_BANK
  label_meet ATM_BANK BANK = ATM_BANK
  label_meet BANK BANK_ATM = BANK_ATM
  label_meet BANK_ATM BANK = BANK_ATM
  label_meet ATM_BANK BANK_ATM = BOTTOM
  label_meet BANK_ATM ATM_BANK = BOTTOM
  label_meet CLIENT CLIENT = CLIENT
  label_meet BANK BANK = BANK
  label_meet ATM_BANK ATM_BANK = ATM_BANK
  label_meet BANK_ATM BANK_ATM = BANK_ATM
  label_meet x y = error $ "label_meet : " ++ (show x) ++ " : " ++ (show y)

