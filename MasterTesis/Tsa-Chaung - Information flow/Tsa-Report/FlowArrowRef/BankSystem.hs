{-# OPTIONS -fglasgow-exts #-}


module BankSystem where

import BankLattice
import BankKey
import FlowArrowRef
import Lattice
import Control.Arrow
import SecureFlow
import RefOp
import System.Random
import Codec.Utils
import Data.LargeWord
import Codec.Encryption.RSA as RSA
import Codec.Encryption.AES as AES
import Codec.Encryption.Modes
import Codec.Encryption.Padding

-- Certify function
expose :: (Privilege BankLabel) -> SecType BankLabel -> Protected c -> IO c
expose p r t = runArrowRef (certifyRef (SecLabel (Lab BOTTOM)) (mlabel_bottom r) p t) ()

exposeL :: (Privilege BankLabel) -> Protected c -> IO c
exposeL p t = runArrowRef (certifyRefL (SecLabel (Lab BOTTOM)) label_bottom p t) ()


-----------------
-- Client Card --
-----------------
-- Get account id
client_getAccountId :: IO Int
client_getAccountId = return clientID

---------
-- ATM --
---------
-- Generate authentication request
atm_authRequest :: Protected (SecRef Int) -> (Privilege BankLabel) -> IO [Octet]
atm_authRequest atm_nounce priv = 
  do id <- client_getAccountId
     atm_getNewNounce priv atm_nounce
     req <- atm_buildAuthRequest id atm_nounce
     atm_RSAencrypt priv req (bankModulus,bankPubKey) 

-- Generate transaction request
atm_tranRequest :: [Octet] -> Protected (SecRef Int) -> Protected (SecRef Int) 
                   -> Protected (SecRef Word128) 
                   -> (String -> IO (Maybe (Protected ([Octet],[Octet]))))
                   -> (Privilege BankLabel)
                   -> IO [Word128]
atm_tranRequest res atm_nounce bank_nounce sessionKey client_prikey priv = 
  do (ok,pw) <- atm_AuthResDecrypt res atm_nounce bank_nounce sessionKey client_prikey priv   
     if not ok
       then error "ATM nounce is not consistent."
       else do putStrLn "Authentication response received and correct."
               atm_getNewNounce priv atm_nounce
               tran <- atm_buildTransaction atm_nounce
               sig <- atm_getSignature tran client_prikey pw
               atm_buildTranRequest tran sig atm_nounce bank_nounce sessionKey priv

-- End of transaction
atm_resultProcess :: [Word128] -> IO ()
atm_resultProcess r = putStrLn "Transaction response received.\nThank you."

-- Generate new atm nounce
atm_getNewNounce priv = getNewNounce ATM_BANK priv

-- Merge account id and atm nounce
atm_buildAuthRequest :: Int -> Protected (SecRef Int)-> IO (Protected [Octet])
atm_buildAuthRequest id atm_nounce =
  do let req = atm_nounce >>> readRef (SecLabel (Lab ATM_BANK)) >>> 
               lowerA ATM_BANK (pure (\r -> (toOctets 256 id)++(toOctets 256 r)))
     return req

-- Use RSA and public key of bank to encrypt request and release
atm_RSAencrypt = encryptRSA BANK

-- Decrypt authentication response with private key of client card
atm_AuthResDecrypt :: [Octet] -> Protected (SecRef Int) -> Protected (SecRef Int) 
                      -> Protected (SecRef Word128) 
                      -> (String -> IO (Maybe (Protected ([Octet],[Octet]))))
                      -> (Privilege BankLabel)
                      -> IO (Bool, String) 
atm_AuthResDecrypt res atm_nounce bank_nounce sessionKey client_prikey priv=
  do putStr "Please enter password : "
     pw <- getLine
     cpri <- client_prikey pw
     case cpri of 
       Nothing   -> do putStrLn "Password is not correct."
                       atm_AuthResDecrypt res atm_nounce bank_nounce sessionKey client_prikey priv
       (Just pk) -> do
                    let dres = pk >>> lowerA BANK (pure (\key -> RSA.decrypt key res)) >>>
                               lowerA BANK (pure (\p -> drop (128-18) p)) >>>
                               lowerA BANK (pure (\p -> (fromOctets 256 (take 16 p),(drop 16 p)))) >>>
                               ( (atm_StoreRef BANK sessionKey >>> tagRef BANK) *** 
                                 ( lowerA BANK (pure (\p -> (fromOctets 256 (take 1 p), fromOctets 256 (drop 1 p)))) >>>
                                   ( ( ((lowerA BANK (pure (\_ -> ())) >>> declassifyRef ATM_BANK >>>
                                         atm_nounce >>> readRef (SecLabel (Lab ATM_BANK)) >>> tagRef BANK)
                                        &&& lowerA BANK (pure id)) >>>
                                       lowerA BANK (pure (\(a,b) -> if a == b then Right True else Left False)) >>>
                                       ( lowerA BANK (pure id) ||| lowerA BANK (pure id) )
                                     )
                                     *** (atm_StoreRef BANK_ATM bank_nounce >>> tagRef BANK)
                                   ) >>> lowerA BANK (pure (\(x,y) -> x))  -- take result of atm_nounce
                                 )
                               ) >>> lowerA BANK (pure (\(x,y) -> y)) >>>  -- take result of atm_nounce
                               declassifyRef BOTTOM  
                    v <- expose priv (SecLabel (Lab BOTTOM)) dres 
                    return (v,pw)
                               
atm_StoreRef :: forall a . 
                (SecFilter SecType BankLabel a,
                 Downgrade SecType BankLabel a, Dummy a) => 
                 BankLabel -> Protected (SecRef a) -> FlowArrowRef BankLabel ArrowRef a ()
atm_StoreRef l ref = declassifyRef l >>>
                     ((lowerA l (pure (\_ -> ())) >>> ref) &&& (lowerA l (pure id)) ) >>>
                     writeRef 
     
atm_buildTransaction :: Protected (SecRef Int) -> IO (Protected [Octet])
atm_buildTransaction atm_nounce = 
  do id <- client_getAccountId
     putStr "Please choose action([1] deposite [2] withdraw) : "
     ac <- getLine
     action <- return (read ac)
     putStr "Amount(0~255) : "
     am <- getLine
     amount <- return (read am)
     let ptran = atm_nounce >>> readRef (SecLabel (Lab ATM_BANK)) >>> tagRef BANK >>> 
                 lowerA BANK (pure (\n -> (toOctets 256 id) ++ (toOctets 256 action) ++
                                         (toOctets 256 amount) ++ (toOctets 256 n) ))
     return ptran

atm_getSignature :: Protected [Octet] 
                    -> (String -> IO (Maybe (Protected ([Octet],[Octet]))))
                    -> String -> IO (Protected [Octet])
atm_getSignature tran client_prikey pw =
  do cpri <- client_prikey pw
     case cpri of
       Nothing   -> error "password is wrong!"
       (Just cp) -> do
                    let sig = (cp &&& tran) >>>
                              lowerA BANK (pure (\(key,t) -> RSA.encrypt key t))
                    return sig

atm_buildTranRequest :: Protected [Octet] -> Protected [Octet] 
                        -> Protected (SecRef Int) -> Protected (SecRef Int) 
                        -> Protected (SecRef Word128) 
                        -> (Privilege BankLabel)
                        -> IO [Word128]
atm_buildTranRequest ptran psig atm_nounce bank_nounce sessionKey priv =
  do let tran = ( (ptran &&& psig) 
                   &&& 
                  ((atm_nounce >>> readRef (SecLabel (Lab ATM_BANK)) >>> tagRef BANK) 
                   &&& 
                   (bank_nounce >>> readRef (SecLabel (Lab BANK_ATM)) >>> tagRef BANK))) >>>
                lowerA BANK (pure (\((tr,si),(atm_n,bank_n)) -> tr ++ si ++ 
                  (toOctets 256 atm_n) ++ (toOctets 256 bank_n))) >>>
                ( lowerA BANK (pure id) &&& (lowerA BANK (pure (\i -> ())) >>> sessionKey 
                  >>> readRef (SecLabel (Lab BANK)))) >>>
                lowerA BANK (pure (\(c,key) -> cbc AES.encrypt sessionIV key (pkcs5 c) )) >>>
                declassifyRef BOTTOM
     expose priv (SecLabel (Lab BOTTOM)) tran 
     
----------
-- Bank --
----------
-- Generate authentication response
bank_authResponse :: [Octet] -> Protected (SecRef Int) 
                     -> Protected (SecRef Int)
                     -> Protected (SecRef Word128) 
                     -> (Privilege BankLabel)
                     -> IO [Octet]
bank_authResponse req atm_nounce bank_nounce sessionKey priv = 
  do id <- bank_RSAdecrypt req atm_nounce priv
     putStrLn "Authentication request received."
     bank_getNewNounce priv bank_nounce
     res <- bank_buildAuthResponse atm_nounce bank_nounce sessionKey 
     bank_RSAencrypt priv res (clientModulus,clientPubKey)

-- Generate transaction response
bank_tranResponse :: [Word128] -> Protected (SecRef Int)
                     -> Protected (SecRef Int) 
                     -> Protected (SecRef Word128) 
                     -> (Privilege BankLabel)
                     -> IO [Word128]
bank_tranResponse tran atm_nounce bank_nounce sessionKey priv = 
  do (tr,sig,atm_n,bank_n) <- bank_tranDecrypt tran sessionKey priv
     ok <- bank_checkBankNounce bank_n bank_nounce priv
     if not ok
       then error "Bank nounce is not consistent."
       else do putStrLn "Transaction request received and correct."
               bank_updateATMNounce atm_n atm_nounce priv
               bank_getNewNounce priv bank_nounce 
               bank_buildTranResponse atm_nounce bank_nounce sessionKey priv

-- Decrypt transaction request
bank_tranDecrypt :: [Word128] -> Protected (SecRef Word128) 
                    -> (Privilege BankLabel)
                    -> IO (Protected [Octet], Protected [Octet], Protected Int, Protected Int)
bank_tranDecrypt tran sessionKey priv =
  do let dtran = sessionKey >>> readRef (SecLabel (Lab BANK)) >>>
                 lowerA BANK (pure (\key -> unPkcs5 (unCbc AES.decrypt sessionIV key tran) )) >>>
                 lowerA BANK (pure (\dt -> (take 4 dt, drop 4 dt) )) >>>
                 ( lowerA BANK (pure id)
                   ***
                   ( lowerA BANK (pure (\dt -> (take 128 dt, drop 128 dt))) >>>
                     ( lowerA BANK (pure id)
                       ***
                       lowerA BANK (pure (\dt -> (fromOctets 256 (take 1 dt), fromOctets 256 (drop 1 dt))))
                     )
                   )
                 ) >>> declassifyRef BOTTOM 
     (trans,(sig,(atm_n,bank_n))) <- exposeL priv dtran
     return (protect trans, protect sig, protect atm_n, protect bank_n)
  where
  protect t = tagRef BANK >>> lowerA BANK (pure (\() -> t))    

-- Check if bank nounce is the same
bank_checkBankNounce :: Protected Int -> Protected (SecRef Int) 
                        -> (Privilege BankLabel) -> IO Bool
bank_checkBankNounce bank_n bank_nounce priv =
  do let same = (bank_n &&& (bank_nounce >>> readRef (SecLabel (Lab BANK_ATM)) >>> tagRef BANK)) >>>
                lowerA BANK (pure (\(x,y) -> if x == y then True else False)) >>>
                declassifyRef BOTTOM
     expose priv (SecLabel (Lab BOTTOM)) same 
     
-- Store new atm nounce
bank_updateATMNounce :: Protected Int -> Protected (SecRef Int) 
                        -> (Privilege BankLabel) -> IO ()
bank_updateATMNounce atm_n atm_nounce priv =
  do let upd = (atm_nounce &&& (atm_n >>> declassifyRef ATM_BANK)) >>>
               writeRef >>> declassifyRef BOTTOM
     expose priv (SecLabel (Lab BOTTOM)) upd 

-- Build AES encrypted transaction response
bank_buildTranResponse :: Protected (SecRef Int) -> Protected (SecRef Int)
                          -> Protected (SecRef Word128) 
                          -> (Privilege BankLabel)
                          -> IO [Word128]
bank_buildTranResponse atm_nounce bank_nounce sessionKey priv =
  do let enres = ((atm_nounce >>> readRef (SecLabel (Lab ATM_BANK)) >>> tagRef BANK) 
                  &&& 
                  (bank_nounce >>> readRef (SecLabel (Lab BANK_ATM)) >>> tagRef BANK)) >>>
                 lowerA BANK (pure (\(a,b) -> (toOctets 256 1)++(toOctets 256 a)++(toOctets 256 b))) >>>
                 ( lowerA BANK (pure id)
                   &&&
                   (lowerA BANK (pure (\t -> ())) >>> sessionKey >>> readRef (SecLabel (Lab BANK)))
                 ) >>>
                 lowerA BANK (pure (\(dat,key)-> cbc AES.encrypt sessionIV key $ pkcs5 dat)) >>>
                 declassifyRef BOTTOM
     expose priv (SecLabel (Lab BOTTOM)) enres

-- Encrypt authentication response
bank_RSAencrypt priv = encryptRSA BANK priv

-- Build authentication response
bank_buildAuthResponse :: Protected (SecRef Int) -> Protected (SecRef Int) ->
                          Protected (SecRef Word128) -> IO (Protected [Octet])
bank_buildAuthResponse atm_nounce bank_nounce sessionKey = 
  do let n = atm_nounce >>> readRef (SecLabel (Lab ATM_BANK)) >>> tagRef BANK >>> 
             lowerA BANK (pure (\natm -> (natm,()))) >>>
             (second (declassifyRef BANK_ATM)) >>>
             (second bank_nounce) >>> (second (readRef (SecLabel (Lab BANK_ATM)) >>> tagRef BANK)) >>> 
	         lowerA BANK (pure (\(natm,nbank) -> (toOctets 256 natm) ++ (toOctets 256 nbank))) >>>
             lowerA BANK (pure (\nounce -> ((),nounce))) >>>
             (first sessionKey) >>> (first (readRef (SecLabel (Lab BANK)))) >>>
             lowerA BANK (pure (\(sk,nounce) -> (toOctets 256 sk) ++ nounce))
     return n

-- Generate new bank nounce
bank_getNewNounce priv = getNewNounce BANK_ATM priv
    
-- Decryption of request and extract account id and atm nounce
bank_RSAdecrypt :: [Octet] -> Protected (SecRef Int) 
                   -> (Privilege BankLabel)
                   -> IO Int
bank_RSAdecrypt req atm_nounce priv = 
 do let dereq = bankPriKey >>> tagRef BANK >>>
                lowerA BANK (pure (\prikey -> RSA.decrypt (bankModulus, prikey) req)) >>>
                  lowerA BANK (pure (\plain -> (fromOctets 256 (take 1 (drop 126 plain)),
                                                fromOctets 256 (drop 1 (drop 126 plain))))) >>>
                ( lowerA BANK (pure id) *** 
                  ( declassifyRef ATM_BANK >>> 
                    lowerA ATM_BANK (pure (\x -> (x,x))) >>>
                    (first (lowerA ATM_BANK (pure (\_ -> ())) >>> atm_nounce)) >>> 
                    writeRef
                  )
                ) >>> tagRef BANK >>>
                lowerA BANK (pure (\(a,_) -> a)) >>> 
                declassifyRef BOTTOM
    ident <- expose priv (SecLabel (Lab BOTTOM)) dereq
    return ident

--------------------
-- Util functions --
--------------------
-- Generate new nounce
getNewNounce :: BankLabel -> (Privilege BankLabel) -> Protected (SecRef Int) -> IO ()
getNewNounce l_nounce p_owner nounce =
 do newNounce <- randomRIO (0,255)
    let nn = nounce >>> tagRef l_nounce >>> lowerA l_nounce (pure (\r -> (r,newNounce))) >>> 
             writeRef >>> declassifyRef BOTTOM
    expose p_owner (SecLabel (Lab BOTTOM)) nn

-- Use RSA and public key to encrypt and then release
encryptRSA :: BankLabel -> (Privilege BankLabel) -> Protected [Octet] -> ([Octet],[Octet]) -> IO [Octet]
encryptRSA l_owner p_owner req key =
     let enreq = req >>> tagRef l_owner >>> lowerA l_owner (pure (\plain -> RSA.encrypt key plain))
                 >>> declassifyRef BOTTOM
     in
     do r <- expose p_owner (SecLabel (Lab BOTTOM)) enreq
        return r
