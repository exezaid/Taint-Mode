{-# OPTIONS -fallow-undecidable-instances -fglasgow-exts -farrows  #-}

import Control.Arrow
import Lattice
import RLattice
import FlowArrowRef
import System
import Data.IORef
import SecureFlow
import RefOp
import System.Time
import Priv

t1 :: Int -> FlowArrowRef TriLabel ArrowRef () Int
t1 dtime = 
           lowerA LOW (pure (\() -> 99)) >>> 
           createRef (MkLabel MkLow) LOW >>> 
           ( lowerA LOW (pure id) &&& forkRef t2) >>> 
           ( second
              ( pure (\() -> 0) >>>
               pure (\i -> if i > 5 then Left dtime else Right 0) >>>
                ( (skipRef >>> tagRef HIGH)
                 ||| 
                  (skipRef >>> tagRef HIGH)
                )  
              )) >>> 
           second (lowerA LOW (pure (\_ -> 1))) >>>  -- (r,1)
           (lowerA LOW (pure (\(x,y) -> x)) &&& (writeRef >>> pure (\() -> 10000) >>> skipRef )) >>>
           lowerA LOW (pure (\(x,y) -> x)) >>>
           readRef (SecLabel (Lab LOW)) 

t2 :: (ValidSecType rs TriLabel, Dummy rs) 
      => FlowArrowRef TriLabel ArrowRef (SRef rs Int) ()
t2 = ( lowerA LOW (pure id) &&& lowerA LOW (pure (\_ -> 2))) >>> writeRef 

test1 dtime = runArrowRef (certifyRef (SecLabel (Lab LOW)) (SecLabel (Lab HIGH)) (PR HIGH) (t1 dtime)) ()

exet1 dtime = do begin <- getClockTime
                 (one,ten) <- recur 100 (0,0)
                 end <- getClockTime
                 dur <- return $ timeDiffToString (diffClockTimes end begin)
                 putStrLn $ "(1,2) = ("  ++ (show one) ++ "," ++ (show ten) ++ ") in " ++ dur
  where
  recur 0 (one,two) = return (one,two)
  recur n (one,two) = do
                         result <- test1 dtime
                         putStrLn $ "# " ++ (show n)
                         if result == 1
                           then recur (n-1) (one+1,two)
                           else if result == 2 
                                  then recur (n-1) (one,two+1)
                                  else error "invalid value"
