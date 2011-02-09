{-# OPTIONS -fglasgow-exts #-}

module BankTCB where

import BankLattice
import BankSystem
import FlowArrowRef
import Lattice
import Control.Arrow
import SecureFlow
import RefOp
import BankKey
import System.Random
import Codec.Utils
import Data.LargeWord
import Codec.Encryption.RSA as RSA
import Codec.Encryption.AES as AES
import Codec.Encryption.Modes
import Codec.Encryption.Padding
import Priv

-- Get client private key if password is correct
client_getPriKey :: (Privilege BankLabel) -> String -> IO (Maybe (Protected ([Octet],[Octet])))
client_getPriKey pr p =
  if p /= clientPW
    then return Nothing
    else let key = clientPriKey >>> declassifyRef BOTTOM in
         do pri <- expose pr (SecLabel (Lab BOTTOM)) key
            return $ Just (tagRef BANK >>> lowerA BANK (pure (\()  -> (clientModulus,pri))))

-- IO monad to simulate network
main =
  do -- Declare reference and protect them
     atm_ATMNounce   <- getNewRef ATM_BANK (1::Int)
     atm_BankNounce  <- getNewRef BANK_ATM (2::Int)
     atm_SessionKey  <- getNewRef BANK (3::Word128)
     bank_ATMNounce  <- getNewRef ATM_BANK (4::Int)
     bank_BankNounce <- getNewRef BANK_ATM (5::Int)
     bank_SessionKey <- getNewRef BANK (0x06a9214036b8a15b512e03d534120006 :: Word128)
     -- Protocol begin
     auth_req <- atm_authRequest atm_ATMNounce (PR BANK)
     auth_res <- bank_authResponse auth_req bank_ATMNounce bank_BankNounce bank_SessionKey (PR BANK)
     tran_req <- atm_tranRequest auth_res atm_ATMNounce atm_BankNounce atm_SessionKey
                                 (client_getPriKey (PR CLIENT)) (PR BANK)
     tran_res <- bank_tranResponse tran_req bank_ATMNounce bank_BankNounce bank_SessionKey (PR BANK)
     atm_resultProcess tran_res
     return ()
  where
  getNewRef l init =
    do ref <- newSecRef init
       let pref = tagRef l >>> lowerA l (pure (\() -> ref))
       return pref

