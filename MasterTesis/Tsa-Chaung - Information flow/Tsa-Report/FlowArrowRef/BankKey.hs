
module BankKey where

import FlowArrowRef
import BankLattice
import Control.Arrow
import Codec.Utils
import Data.LargeWord


type Protected c = FlowArrowRef BankLabel ArrowRef () c

-- Id and password of the card
clientID = 99 :: Int
clientPW = "0000"

-- Client private key
clientPriKey :: Protected [Octet]
clientPriKey = tagRef CLIENT >>> lowerA CLIENT (pure (\() -> cPriKey)) 
  where
    cPriKey :: [Octet]
    cPriKey =  
       [0xa5, 0xda, 0xfc, 0x53, 0x41, 0xfa, 0xf2,
        0x89, 0xc4, 0xb9, 0x88, 0xdb, 0x30, 0xc1, 0xcd,
        0xf8, 0x3f, 0x31, 0x25, 0x1e, 0x06, 0x68, 0xb4,
        0x27, 0x84, 0x81, 0x38, 0x01, 0x57, 0x96, 0x41,
        0xb2, 0x94, 0x10, 0xb3, 0xc7, 0x99, 0x8d, 0x6b,
        0xc4, 0x65, 0x74, 0x5e, 0x5c, 0x39, 0x26, 0x69,
        0xd6, 0x87, 0x0d, 0xa2, 0xc0, 0x82, 0xa9, 0x39,
        0xe3, 0x7f, 0xdc, 0xb8, 0x2e, 0xc9, 0x3e, 0xda,
        0xc9, 0x7f, 0xf3, 0xad, 0x59, 0x50, 0xac, 0xcf,
        0xbc, 0x11, 0x1c, 0x76, 0xf1, 0xa9, 0x52, 0x94,
        0x44, 0xe5, 0x6a, 0xaf, 0x68, 0xc5, 0x6c, 0x09,
        0x2c, 0xd3, 0x8d, 0xc3, 0xbe, 0xf5, 0xd2, 0x0a,
        0x93, 0x99, 0x26, 0xed, 0x4f, 0x74, 0xa1, 0x3e,
        0xdd, 0xfb, 0xe1, 0xa1, 0xce, 0xcc, 0x48, 0x94,
        0xaf, 0x94, 0x28, 0xc2, 0xb7, 0xb8, 0x88, 0x3f,
        0xe4, 0x46, 0x3a, 0x4b, 0xc8, 0x5b, 0x1c, 0xb3,
        0xc1]

-- Client public key
clientPubKey :: [Octet]
clientPubKey = [0x11]

-- Client modulus
clientModulus :: [Octet]
clientModulus = 
   [0xbb, 0xf8, 0x2f, 0x09, 0x06, 0x82, 0xce, 0x9c,
    0x23, 0x38, 0xac, 0x2b, 0x9d, 0xa8, 0x71, 0xf7,
    0x36, 0x8d, 0x07, 0xee, 0xd4, 0x10, 0x43, 0xa4,
    0x40, 0xd6, 0xb6, 0xf0, 0x74, 0x54, 0xf5, 0x1f,
    0xb8, 0xdf, 0xba, 0xaf, 0x03, 0x5c, 0x02, 0xab,
    0x61, 0xea, 0x48, 0xce, 0xeb, 0x6f, 0xcd, 0x48,
    0x76, 0xed, 0x52, 0x0d, 0x60, 0xe1, 0xec, 0x46,
    0x19, 0x71, 0x9d, 0x8a, 0x5b, 0x8b, 0x80, 0x7f,
    0xaf, 0xb8, 0xe0, 0xa3, 0xdf, 0xc7, 0x37, 0x72,
    0x3e, 0xe6, 0xb4, 0xb7, 0xd9, 0x3a, 0x25, 0x84,
    0xee, 0x6a, 0x64, 0x9d, 0x06, 0x09, 0x53, 0x74,
    0x88, 0x34, 0xb2, 0x45, 0x45, 0x98, 0x39, 0x4e,
    0xe0, 0xaa, 0xb1, 0x2d, 0x7b, 0x61, 0xa5, 0x1f,
    0x52, 0x7a, 0x9a, 0x41, 0xf6, 0xc1, 0x68, 0x7f,
    0xe2, 0x53, 0x72, 0x98, 0xca, 0x2a, 0x8f, 0x59,
    0x46, 0xf8, 0xe5, 0xfd, 0x09, 0x1d, 0xbd, 0xcb]


-- Bank private key
bankPriKey :: Protected [Octet]
bankPriKey = tagRef BANK >>> lowerA BANK (pure (\() -> cPriKey)) 
  where
    cPriKey :: [Octet]
    cPriKey =  
       [0xa5, 0xda, 0xfc, 0x53, 0x41, 0xfa, 0xf2,
        0x89, 0xc4, 0xb9, 0x88, 0xdb, 0x30, 0xc1, 0xcd,
        0xf8, 0x3f, 0x31, 0x25, 0x1e, 0x06, 0x68, 0xb4,
        0x27, 0x84, 0x81, 0x38, 0x01, 0x57, 0x96, 0x41,
        0xb2, 0x94, 0x10, 0xb3, 0xc7, 0x99, 0x8d, 0x6b,
        0xc4, 0x65, 0x74, 0x5e, 0x5c, 0x39, 0x26, 0x69,
        0xd6, 0x87, 0x0d, 0xa2, 0xc0, 0x82, 0xa9, 0x39,
        0xe3, 0x7f, 0xdc, 0xb8, 0x2e, 0xc9, 0x3e, 0xda,
        0xc9, 0x7f, 0xf3, 0xad, 0x59, 0x50, 0xac, 0xcf,
        0xbc, 0x11, 0x1c, 0x76, 0xf1, 0xa9, 0x52, 0x94,
        0x44, 0xe5, 0x6a, 0xaf, 0x68, 0xc5, 0x6c, 0x09,
        0x2c, 0xd3, 0x8d, 0xc3, 0xbe, 0xf5, 0xd2, 0x0a,
        0x93, 0x99, 0x26, 0xed, 0x4f, 0x74, 0xa1, 0x3e,
        0xdd, 0xfb, 0xe1, 0xa1, 0xce, 0xcc, 0x48, 0x94,
        0xaf, 0x94, 0x28, 0xc2, 0xb7, 0xb8, 0x88, 0x3f,
        0xe4, 0x46, 0x3a, 0x4b, 0xc8, 0x5b, 0x1c, 0xb3,
        0xc1]

-- Bank public key
bankPubKey :: [Octet]
bankPubKey = [0x11]

-- Bank modulus
bankModulus :: [Octet]
bankModulus = 
   [0xbb, 0xf8, 0x2f, 0x09, 0x06, 0x82, 0xce, 0x9c,
    0x23, 0x38, 0xac, 0x2b, 0x9d, 0xa8, 0x71, 0xf7,
    0x36, 0x8d, 0x07, 0xee, 0xd4, 0x10, 0x43, 0xa4,
    0x40, 0xd6, 0xb6, 0xf0, 0x74, 0x54, 0xf5, 0x1f,
    0xb8, 0xdf, 0xba, 0xaf, 0x03, 0x5c, 0x02, 0xab,
    0x61, 0xea, 0x48, 0xce, 0xeb, 0x6f, 0xcd, 0x48,
    0x76, 0xed, 0x52, 0x0d, 0x60, 0xe1, 0xec, 0x46,
    0x19, 0x71, 0x9d, 0x8a, 0x5b, 0x8b, 0x80, 0x7f,
    0xaf, 0xb8, 0xe0, 0xa3, 0xdf, 0xc7, 0x37, 0x72,
    0x3e, 0xe6, 0xb4, 0xb7, 0xd9, 0x3a, 0x25, 0x84,
    0xee, 0x6a, 0x64, 0x9d, 0x06, 0x09, 0x53, 0x74,
    0x88, 0x34, 0xb2, 0x45, 0x45, 0x98, 0x39, 0x4e,
    0xe0, 0xaa, 0xb1, 0x2d, 0x7b, 0x61, 0xa5, 0x1f,
    0x52, 0x7a, 0x9a, 0x41, 0xf6, 0xc1, 0x68, 0x7f,
    0xe2, 0x53, 0x72, 0x98, 0xca, 0x2a, 0x8f, 0x59,
    0x46, 0xf8, 0xe5, 0xfd, 0x09, 0x1d, 0xbd, 0xcb]

-- Initial vector used in cbc scheme
sessionIV  = 0x3dafba429d9eb430b422da802c9fac41 :: Word128
