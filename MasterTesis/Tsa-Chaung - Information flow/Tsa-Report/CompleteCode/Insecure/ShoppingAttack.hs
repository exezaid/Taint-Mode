{-# OPTIONS -fglasgow-exts #-}

module Shopping where

import FlowArrowRef
import SecureFlow
import Lattice
import RLattice
import RefOp
import Control.Arrow
import Priv
import System.Time

type Protected b c = FlowArrowRef TriLabel ArrowRef b c

type Name = [Char]
type Tel  = [Char]
type CNum = Integer
type Addr = [Char]
type ClientData = ((Name,Tel),(CNum,Addr))
type PubItem = ((Name,Tel),Addr)

clientDatabase = [(("Bob","0704231232"),(9999999999999999,"Rotary, Gothenburg."))]

main = do
       begin <- getClockTime
       -- protected program clientInit are certified and run in runArrowRef
       pub <- runArrowRef (certifyRef (SecLabel (Lab LOW)) (SecLabel (Lab LOW))
                                    (PR HIGH) clientInit) clientDatabase
       mapM_ showClient (reverse pub)
       end <- getClockTime
       putStrLn $ timeDiffToString (diffClockTimes end begin) ++ "."

showClient ((name,tel),addr) = 
    putStrLn $ "### Client ###\nName : " ++ name ++ "\nTel  : " ++ tel ++
               "\nAddr : " ++ addr

-- Declare references and call serverInit to handle each client
clientInit :: Protected [ClientData] [PubItem]
clientInit = 
    (((lowerA HIGH (pure (\_ -> [])) >>> createRefA (VSecLabel VHigh) LOW)
      &&&
      (lowerA LOW (pure (\_ -> [])) >>> createRefA (VSecLabel VLow) LOW)
     )
     &&&
     (idRef
      &&&
      lowerA LOW (pure (\d -> (0,length d)))
     )
    ) >>>
    iterateA serverInit >>>
    (idRef
     ***
     -- A long delay waiting for completion of all purchases
     (lowerA LOW (pure (\_ -> 3700000)) >>> skipRef)
    ) >>>
    fstPair >>>
    (readRefA (SecLabel (Lab HIGH))
     ***
     readRefA (SecLabel (Lab LOW))
    ) >>>
    -- return public data only
    lowerA LOW (pure (\(_,p)->p))
 
-- Protect a client's data with adequate security types and 
-- fork a new thread to handle client data
serverInit :: (STSecType rs1 TriLabel, STSecType rs2 TriLabel) =>
              Protected ((SRef rs1 [CNum], SRef rs2 [PubItem]),([ClientData], (Int,Int))) 
                        (((SRef rs1 [CNum], SRef rs2 [PubItem]),([ClientData], (Int,Int))), Bool) 
serverInit =
    (((((idRef
         ***
         (lowerA LOW (pure (\(c,_) -> case head c of
                                        ((name,tel),(cnum,addr)) -> (cnum,((name,tel),addr)) )) >>>
          (tagRef HIGH  -- protect credit card number with HIGH
           ***
           idRef        -- other fields are LOW
          )
         ) 
        ) >>>
        forkRef purchase'
       )
       &&&
       (idRef
        ***
        lowerA LOW (pure (\(c,(from,to)) -> (tail c, (from+1,to)) ))
       )
      ) >>> 
      sndPair
     )
     &&&
     lowerA LOW (pure (\((_,_),(_,(from,to))) -> if (from+1) < to then True else False))
    )

-- A safe processing function
purchase :: (STSecType rs1 TriLabel, STSecType rs2 TriLabel) =>
                 Protected ((SRef rs1 [CNum], SRef rs2 [PubItem]),
                            (CNum,((Name,Tel),Addr)))
                           ()
purchase = 
   -- copy credit card number to the secret reference
   (atomicA
    (
     (lowerA HIGH (pure (\((r,_),_) -> r))
      &&&
      (
       (lowerA HIGH (pure (\(_,(cnum,_)) -> cnum))
        &&&
        (lowerA HIGH (pure (\((r,_),_) -> r)) >>> readRefA (SecLabel (Lab HIGH)))
       ) >>>
       lowerA HIGH (pure (\(cnum,record) -> cnum:record ))  
      )
     ) >>> 
     writeRefA
    )
    &&&
    -- copy public data to the public references
    atomicA
    (
     (lowerA LOW (pure (\((_,r),_) -> r))
      &&&
      (
       (lowerA LOW (pure (\(_,(_,pub)) -> pub))
        &&&
        (lowerA LOW (pure (\((_,r),_) -> r )) >>> readRefA (SecLabel (Lab LOW)))
       ) >>>
       lowerA LOW (pure (\(pub,record) -> pub:record))
      )
     ) >>>
     writeRefA
    )
   ) >>>
   sndPair 

-- Malicious program trying to obtain credit card number
purchase' :: (STSecType rs1 TriLabel, STSecType rs2 TriLabel) =>
                   Protected ((SRef rs1 [CNum], SRef rs2 [PubItem]),
                             (CNum,((Name,Tel),Addr)))
                             ()
purchase' = (copyCNum &&& (attackProgram >>> copyPublicData)) >>>
           lowerA LOW (pure (\_ -> ()))

-- Copy credit card number to HIGH reference
copyCNum :: (STSecType rs1 TriLabel, STSecType rs2 TriLabel) =>
                   Protected ((SRef rs1 [CNum], SRef rs2 [PubItem]),
                             (CNum,((Name,Tel),Addr)))
                             ()
copyCNum =
  (atomicA (
   (lowerA HIGH (pure (\((highRef,_),_) -> highRef))
    &&&
    ((lowerA HIGH (pure (\(_,(cnum,_)) -> cnum))
      &&&
      (lowerA HIGH (pure (\((highRef,_),_) -> highRef)) >>> readRefA (SecLabel (Lab HIGH)))
     ) >>>
     lowerA HIGH (pure (\(cnum,record) -> cnum:record ))  
    )
   ) >>> writeRefA)
  )

-- Attack program
attackProgram = idRef *** (launchAttack >>> appendPublic)

-- Create a LOW reference to store attack results and
-- repeat attackOneBit for each bit of a credit number.
launchAttack =
  ((
    ((
      lowerA LOW (pure (\_ -> [])) >>>
      -- reference to store attack result
      createRefA (VSecLabel VLow) LOW  
     )
     &&&
     -- number of bits to derive
     (lowerA LOW (pure (\_ -> 53)) 
      &&&
      idRef  
     )
    ) >>> 
    -- repeat the same attack for every bit
    iterateA attackOneBit >>> 
    fstPair >>> 
    readRefA (SecLabel (Lab LOW))
   )
   ***
   idRef 
  )

-- Append attack result to address field
appendPublic =
  lowerA LOW (pure (\(attackResult,((name,tel),addr)) -> 
                        (0::Integer,((name,tel),addr++"\n"++attackResult))))

-- Copy public data to LOW reference
copyPublicData :: (STSecType rs1 TriLabel, STSecType rs2 TriLabel) =>
                   Protected ((SRef rs1 [CNum], SRef rs2 [PubItem]),
                             (CNum,((Name,Tel),Addr)))
                             ()
copyPublicData =
  atomicA (
   (lowerA LOW (pure (\((_,lowRef),_) -> lowRef))
    &&&
    (
     (lowerA LOW (pure (\(_,(_,newPubData)) -> newPubData))
      &&&
      (lowerA LOW (pure (\((_,lowRef),_) -> lowRef )) >>> readRefA (SecLabel (Lab LOW)))
     ) >>>
     lowerA LOW (pure (\(newPubData,record) -> newPubData:record))
    )
   ) >>>
   writeRefA )

-- A thread forked to compete with main thread
attackThread :: (STSecType rs TriLabel) => Protected (SRef rs Int) ()
attackThread =
  ((tagRef LOW >>> idRef)
   &&&
   (lowerA LOW (pure (\_ -> 10000)) >>> skipRef)
  ) >>>
  fstPair >>>
  (idRef
   &&&
   lowerA LOW (pure (\_ -> 0))
  ) >>>
  writeRefA

-- Derive one bit information of credit card number each run
attackOneBit :: (STSecType rs TriLabel) => 
                Protected (SRef rs [Char],(Int,CNum)) ((SRef rs [Char],(Int,CNum)),Bool)
attackOneBit =
  ((exploitTimingChannel >>> appendResult)
   &&&
   continueCheck
  ) >>>
  sndPair

-- Attack based on internal timing channels
exploitTimingChannel =
  idRef 
  ***
  ((idRef 
    &&&
    (lowerA LOW (pure (\_ -> 99::Int)) >>> createRefA (VSecLabel VLow) LOW)
   ) >>>
   ((sndPair >>> (idRef &&& forkRef attackThread))
    &&&
    ((first (lowerA HIGH (pure (\(k,cnum) -> if cnum >= 2^k then Left 30000 else Right 0)) >>>
             ((skipRef >>> tagRef HIGH)
              |||
              (skipRef >>> tagRef HIGH)
             )
            )
     ) >>>
     (second (((tagRef LOW >>> idRef)
              &&&
              lowerA LOW (pure (\_ -> 1))
              ) >>>
              writeRefA >>>
              lowerA LOW (pure (\_ -> 30000)) >>>
              skipRef
             )
     )
    )
   ) >>>
   lowerA LOW (pure (\((a,_),_) -> a)) >>>
   readRefA (SecLabel (Lab LOW))
  )

-- Store attack result to the result LOW reference
appendResult :: STSecType rs TriLabel => Protected (SRef rs [Char], Int) ()
appendResult =
  ((idRef &&& readRefA (SecLabel (Lab LOW)))
   ***
   idRef
  ) >>>  
  pairRight >>> 
  (second (lowerA LOW (pure (\(d,b) -> d ++ (show b))))) >>> 
  writeRefA 

-- Check if all bits are derived
continueCheck :: STSecType rs TriLabel =>
                 Protected (SRef rs [Char], (Int, CNum)) 
                           ((SRef rs [Char], (Int, CNum)), Bool)
continueCheck =
  (idRef 
   ***
   (lowerA LOW (pure (\(k,_) -> k-1))  
    &&&
    lowerA HIGH (pure (\(k,c) -> if c >= 2^k then c-(2^k) else c)) 
   )
  )
  &&&
  -- return True if not finished, False, otherwise
  lowerA LOW (pure (\(_,(k,_)) -> if k > 0 then True else False))

