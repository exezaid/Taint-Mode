{-# OPTIONS -fallow-undecidable-instances -fglasgow-exts -farrows  #-}

import Control.Arrow
import Lattice
import FlowArrowRef
import System
import Data.IORef
import SecureFlow
import RefOp
import System.Time

type Protected a = FlowArrowRef TriLabel ArrowRef () a
type Priv = Privilege TriLabel

getNumber :: IO Int
getNumber = do 
{ 
  line <- getLine;
  case reads line of
      [] -> return 0;
      (i,_):s -> return i;
}

guest_service :: Priv -> 
      (Protected (SecRef Int)) -> IO (Protected (SecRef Int))
guest_service priv stat = do 
{
  putStrLn "Enter a number:";
  i <- getNumber;
  putStrLn "Thank you";
  let stat' = lowerA HIGH (pure (\() -> ())) >>> stat >>> (idRef &&& readRef (SecLabel (Lab HIGH))) >>> 
              (idRef *** lowerA HIGH (pure (\x -> if i > x then i else x)) ) >>>
              (fstPair &&& writeRef) >>> fstPair
  in
  return stat';
}

admin_service :: Priv -> 
      (Protected (SecRef Int)) -> IO (Protected (SecRef Int))
admin_service priv stat = 
  do
  let value = (stat >>> (readRef (SecLabel (Lab HIGH))) >>> (declassifyRef LOW)) 
  summary <- runArrowRef (certifyRef (SecLabel (Lab HIGH)) (SecLabel (Lab LOW)) priv value) ()
  putStrLn (show summary)
  let stat_new = pure (\() -> ()) >>> stat >>> (((idRef &&& pure (\r -> 0)) >>> writeRef) &&& idRef) >>> sndPair 
  return stat_new

service_loop :: (Protected AuthDB) -> 
                (Protected (SecRef Int)) -> IO ()
service_loop auth_db stat = do
{
  putStrLn "Enter username and password:";
  u <- getLine; p <- getLine;
  (ident,priv) <- authenticate auth_db u p;
  stat_new <- case ident of 
    "admin" -> admin_service priv stat;
    "guest" -> guest_service priv stat;
     _ -> do { 
               putStrLn "login error"; 
               return stat;
             }
  ; 
  service_loop auth_db stat_new;
}

main = do
{
  let auth_db :: (Protected AuthDB) = 
       (
         pure (\() -> ((("admin","admin"),HIGH), 
                      (("guest","guest"),LOW)) ) 
         >>> 
         tagRef HIGH
       )
      secret_val :: (Protected (SecRef Int)) = lowerA HIGH (pure (\() -> 0)) >>> createRef HIGH 
  in
  service_loop auth_db secret_val;
}



{- Added by ALE
   Example of an insecure program 
-}
{-
insec1 :: FlowArrowRef TriLabel (SecType TriLabel) ArrowRef () (IORef Int) 
insec1 = 
  proc () -> do 
    {   
      x <- tagRef (SecLabel HIGH) -< 5;
      if x > 3 then createRef LOW HIGH -< x 
               else createRef LOW HIGH -< x+1 ;
    } 
 
-- Error : The label of result should at least as label of content of reference.
insec2 :: FlowArrowRef TriLabel (SecType TriLabel) ArrowRef () Int
insec2 =
  proc () -> do
    {
      x <- tagRef (SecLabel HIGH) -< 5;
      r1 <- createRef HIGH LOW -< x;
      readRef HIGH LOW LOW -< r1;
    }

-- Error : The label of result should at least as label of reference.
insec3 :: FlowArrowRef TriLabel (SecType TriLabel) ArrowRef () Int
insec3 =
  proc () -> do
    {
      x <- tagRef (SecLabel LOW) -< 5;
      r1 <- createRef LOW HIGH -< x;
      readRef LOW HIGH LOW -< r1;
    }

-- Error : Reference with ld < lr cannot be written.
insec4 :: FlowArrowRef TriLabel (SecType TriLabel) ArrowRef () () 
insec4 =
  proc () -> do
    {
      x <- tagRef (SecLabel LOW) -< 5;
      r1 <- createRef LOW HIGH -< x;
      writeRef LOW HIGH -< (r1,x);
    }

-- Error : The resulting label should be guarded by l.
insec5 :: FlowArrowRef TriLabel (SecType TriLabel) ArrowRef () Int
insec5 = 
  proc () -> do
    {
      x <- tagRef (SecLabel LOW) -< 5;
      p <- createPair HIGH (SecLabel LOW) (SecLabel HIGH) -< (x, x+1);
      fstPair HIGH (SecLabel LOW) (SecLabel HIGH) (SecLabel LOW) -< p;
    }
-}

--exSideEffect :: FlowArrowRef TriLabel (SecType TriLabel) ArrowRef Int (IO ())
--exSideEffect = lowerA $ pure (\x -> putStrLn (show x))

{- Two examples of secure programs -}
ex0 :: FlowArrowRef TriLabel ArrowRef (SecRef Int) Int
--ex0 = (pure (\() -> 5)) >>> (pure (\a->a+1))
--ex0 = (arr id &&& (arr (\x -> x) >>> createRef HIGH HIGH)) >>> ((lowerA (arr (\(y,x) -> x))) >>> readRef HIGH )
ex0 = ((lowerA LOW (arr (\x -> x))) >>> readRef (SecLabel (Lab HIGH)) )
--ex0 = ((lowerA (arr (\x -> x))) >>> (lowerA (arr (\x -> x))) )


ex1 :: FlowArrowRef TriLabel ArrowRef Int Int
--ex1 = lowerA LOW ((arr id &&& (arr (\x -> x) >>> createRef HIGH)) >>> arr (\(y,x) -> x)) >>> readRef (SecLabel (Lab HIGH)) 
ex1 = (arr id &&& (tagRef HIGH >>> lowerA HIGH (arr (\x -> x)) >>> createRef HIGH)) >>> lowerA HIGH (arr (\(y,x) -> x)) 
      >>> readRef (SecLabel (Lab HIGH)) 

ex1' :: FlowArrowRef TriLabel ArrowRef Int Int
--ex1' = ((arr id &&& (arr (\x -> x) >>> createRef HIGH HIGH)) >>> lowerA (arr (\(y,x) -> x))) >>> readRef (Lab HIGH) 
ex1' = (arr id &&& (arr (\x -> x) >>> createRef HIGH)) >>> (lowerA LOW (arr (\(y,x) -> x)) 
       >>> readRef (SecLabel (Lab HIGH)) )

ex2 :: FlowArrowRef TriLabel ArrowRef Int Int
ex2 = lowerA LOW (arr (\i -> if i>100 then 5 else 4)) >>> lowerA LOW (arr (\i -> i+3))

ex3 :: FlowArrowRef TriLabel ArrowRef Int Int
ex3 = ( (lowerA LOW (arr (\i -> (i,i+100)))) >>> (createPair (SecLabel (Lab HIGH)) (SecLabel (Lab LOW))) ) 
      >>> (lowerA LOW (arr (\(x,y) -> (x,y)))) >>> sndPair 

ex3' :: FlowArrowRef TriLabel ArrowRef Int Int
ex3' = ((lowerA LOW (arr (\i -> (i,i+100)))) >>> (createPair (SecLabel (Lab HIGH)) (SecLabel (Lab LOW))) )
       >>> (lowerA LOW (arr (\(x,y) -> (x,y)))) >>> fstPair 

ex4 :: FlowArrowRef TriLabel ArrowRef Int Int
ex4 = ((lowerA LOW (pure (\i -> i))) >>> createRef LOW) >>> (lowerA LOW (pure (\r -> r))) >>> lowerA LOW (pure (\r -> 5))

-- It's legal now...because content of reference is LOW.
ex4' :: FlowArrowRef TriLabel ArrowRef Int Int
ex4' = ((lowerA LOW (pure (\i -> i))) >>> createRef LOW) >>> (lowerA LOW (pure (\r -> r))) >>> readRef (SecLabel (Lab HIGH))

ex5 :: FlowArrowRef TriLabel ArrowRef Int Int
ex5 = lowerA LOW (pure (\i -> (i,10))) >>>  (first (createRef LOW)) >>> 
      (first (readRef (SecLabel (Lab LOW)))) >>>
      lowerA LOW (pure (\(a,b) -> b))

ex6 :: FlowArrowRef TriLabel ArrowRef Int Int
ex6 = pure (\i -> i) >>> ( createRef LOW &&& (pure (\t -> t+2) >>> createRef HIGH)) >>> 
      (readRef (SecLabel (Lab HIGH)) *** readRef (SecLabel (Lab HIGH))) >>> pure (\(x,y) -> x+y)

ex7 :: FlowArrowRef TriLabel ArrowRef Int (IO ())
ex7 = pure (\i -> putStrLn (show i))

ex8 :: FlowArrowRef TriLabel ArrowRef Int Int
ex8 = pure (\k -> if k > 10 then (Left k) else (Right k)) >>> 
      ((lowerA LOW (pure(\_ -> 1))) ||| (lowerA LOW (pure (\_->0))))

ex9 :: FlowArrowRef TriLabel ArrowRef Int (Either Int Int)
ex9 = pure (\k -> if k > 10 then (Left k) else (Right k)) >>>
      ((lowerA LOW (pure(\_ -> 1))) +++ (lowerA LOW (pure (\_->0))))

ex10 :: FlowArrowRef TriLabel ArrowRef Int (IO ())
ex10 = pure (\x -> putStrLn (show x))

-- show the effect of new constraint in lowerA
-- the content of ref = LOW
-- identity of ref = HIGH
-- Although ref is not used in lowerA HIGH, it cannot pass through.

ex11 :: FlowArrowRef TriLabel ArrowRef Int Int
ex11 = lowerA LOW (pure id) >>> 
       createRef HIGH >>> 
       lowerA HIGH (pure (\r -> r)) >>> 
       pure (\_ -> 1)

{-
sec0 :: FlowArrowRef TriLabel ArrowRef () Int 
sec0 =
  proc () -> do
    {
      --x <- tagRef (SecLabel HIGH) -< 5;
      r <- createRef HIGH HIGH -< 5;
      readRef HIGH -< r
    }

sec1 :: FlowArrowRef TriLabel ArrowRef () (IORef Int) 
sec1 = 
  proc () -> do 
    {   
      x <- tagRef (SecLabel HIGH) -< 5;
      if x > 3 then createRef HIGH LOW -< x 
               else createRef HIGH LOW -< x+1 ;
    }
-}

sec1' :: FlowArrowRef TriLabel ArrowRef () (SecRef Int)
sec1' = (arr id &&& (arr (\() -> 5) >>> tagRef HIGH) ) >>>
        (arr (\((),x) -> if x>3 then (Left ((),x)) else (Right ((),x)))) >>>
        ((arr (\((),x) -> x) >>> createRef LOW ) |||
         (arr (\((),x) -> x+1) >>> createRef LOW) ) 
{-
sec2 :: FlowArrowRef TriLabel (SecType TriLabel) ArrowRef () (IORef Int) 
sec2 = 
  proc () -> do 
    {   
      x <- tagRef (SecLabel HIGH) -< 5;
      if x > 3 then createRef HIGH HIGH -< x 
               else createRef HIGH HIGH -< x+1 ;
    } 


sec3 :: FlowArrowRef TriLabel (SecType TriLabel) ArrowRef () Int
sec3 =
  proc () -> do
    {
      x <- tagRef (SecLabel LOW) -< 5;
      r1 <- createRef HIGH HIGH -< x;
      readRef HIGH HIGH HIGH -< r1;
      writeRef HIGH HIGH -< (r1,x+1);
      readRef HIGH HIGH HIGH -< r1;
    }


sec4 :: FlowArrowRef TriLabel (SecType TriLabel) ArrowRef () ()
sec4 =
  proc () -> do
    {
      x <- (tagRef (SecLabel HIGH) >>> (declassifyRef (SecLabel HIGH) (SecLabel LOW))) -< 5;
      r1 <- createRef LOW LOW -< x;
      readRef LOW LOW LOW -< r1;
      writeRef LOW LOW -< (r1,x+1);
      y <- readRef LOW LOW HIGH -< r1;
      r2 <- createRef HIGH HIGH -< y;
      writeRef HIGH HIGH -< (r2,x);
    }

sec5 :: FlowArrowRef TriLabel (SecType TriLabel) ArrowRef () Int
sec5 = 
  proc () -> do
    {
      x <- tagRef (SecLabel LOW) -< 5;
      p <- createPair HIGH (SecLabel LOW) (SecLabel HIGH) -< (x, x+1);
      fstPair HIGH (SecLabel LOW) (SecLabel HIGH) (SecLabel HIGH) -< p;
    }

-}
{- this shows the constraints that are saved "inside" of the arrow -}
--kk1 = showC insec1
--kk2 = showC sec1
--kk3 = showC sec2
--kk4 = showC sec3

-- Test if the constraints are met.

--icc p = runArrowRef (certifyRef (SecLabel LOW) (SecLabel LOW) (PR (SecLabel LOW)) p) ()
--icc2 = runArrowRef (certifyRef (SecLabel LOW) (SecLabel LOW) (PR (SecLabel LOW)) insec2) ()
cex0 = do rr <- newSecRef 0
          r <- runArrowRef (certifyRef (Ref (SecLabel (Lab LOW)) (Lab LOW)) (SecLabel (Lab HIGH)) (PR LOW) ex0) rr
          putStrLn (show r)
cex1 = do r <- runArrowRef (certifyRef (SecLabel (Lab LOW)) (SecLabel (Lab HIGH)) (PR LOW) ex1) 99
          putStrLn (show r)
cex1' = do r<- runArrowRef (certifyRef (SecLabel (Lab LOW)) (SecLabel (Lab HIGH)) (PR LOW) ex1') 99
           putStrLn (show r)
cex2 = do r <- runArrowRef (certifyRef (SecLabel (Lab LOW)) (SecLabel (Lab LOW)) (PR LOW) ex2) 200
          putStrLn (show r)
cex2' = do r <- runArrowRef (certifyRef (SecLabel (Lab HIGH)) (SecLabel (Lab LOW)) (PR LOW) ex2) 200
           putStrLn (show r)
cex3 = do r <- runArrowRef (certifyRef (SecLabel (Lab LOW)) (SecLabel (Lab HIGH)) (PR LOW) ex3) 15
          putStrLn (show r)
cex3' = do r <- runArrowRef (certifyRef (SecLabel (Lab LOW)) (SecLabel (Lab HIGH)) (PR LOW) ex3') 15
           putStrLn (show r)
cex4 = do r <- runArrowRef (certifyRef (SecLabel (Lab LOW)) (SecLabel (Lab HIGH)) (PR LOW) ex4) 15
          putStrLn (show r)
cex4' = do r <- runArrowRef (certifyRef (SecLabel (Lab LOW)) (SecLabel (Lab HIGH)) (PR LOW) ex4') 15
           putStrLn (show r)
cex5 = do r <- runArrowRef (certifyRef (SecLabel (Lab LOW)) (SecLabel (Lab HIGH)) (PR LOW) ex5) 11
          putStrLn (show r)
cex6 = do r <- runArrowRef (certifyRef (SecLabel (Lab LOW)) (SecLabel (Lab HIGH)) (PR LOW) ex6) 10
          putStrLn (show r)
cex7 = do r <- runArrowRef (certifyRef (SecLabel (Lab LOW)) (SecLabel (Lab HIGH)) (PR LOW) ex7) 10
          r --putStrLn (show r)
cex8 = do r <- runArrowRef (certifyRef (SecLabel (Lab HIGH)) (SecLabel (Lab LOW)) (PR LOW) ex8) 11
          putStrLn (show r)
cex9 = do r <- runArrowRef (certifyRef (SecLabel (Lab HIGH)) (SecEither (SecLabel (Lab LOW)) (SecLabel (Lab LOW)) (Lab LOW)) (PR LOW) ex9) 11
          putStrLn (show r)

cex10 = do r <- runArrowRef (certifyRef (SecLabel (Lab HIGH)) (SecLabel (Lab HIGH)) (PR HIGH) ex10) 99
           r
cex11 = do r <- runArrowRef (certifyRef (SecLabel (Lab LOW)) (SecLabel (Lab HIGH)) (PR LOW) ex11) 11
           putStrLn (show r)
--cc0 = runArrowRef (certifyRef (SecLabel LOW) (SecLabel HIGH) (PR LOW) sec0) ()
cc1 = runArrowRef (certifyRef (SecLabel (Lab LOW)) (Ref (SecLabel (Lab LOW)) (Lab LOW)) (PR LOW) sec1') ()
--cc2 = runArrowRef (certifyRef (SecLabel HIGH) (SecLabel HIGH) (PR LOW) sec2) ()
--cc3 = runArrowRef (certifyRef (SecLabel LOW) (SecLabel HIGH) (PR HIGH) sec3) ()
--cc4 = runArrowRef (certifyRef (SecLabel HIGH) (SecLabel HIGH) (PR HIGH) sec4) ()
--cc5 = runArrowRef (certifyRef (SecLabel LOW) (SecLabel HIGH) (PR HIGH) sec5) ()

{-
skip :: Int -> Int
skip i = if i > 0 then skip (i-1)
                  else 0
-}
{-
t1' :: Int -> FlowArrowRef TriLabel ArrowRef () Int
t1' dtime = lowerA LOW (pure (\() -> 99)) >>> createRef LOW >>>
            ( forkRef t2 &&& lowerA LOW (pure id)) >>>
            ( ( pure (\() -> 0) >>>
                protectA (
                pure (\i -> if i > 5 then Left dtime else Right 0) >>>
                 ( skipRef
                  ||| 
                   skipRef
                 ) )
               ) *** lowerA LOW (pure id)) >>>
            lowerA LOW (pure (\(k,r) -> (r,1))) >>>  -- the identity of pair is LOW, so it's ok.
            (lowerA LOW (pure (\(r,d) -> r)) &&& (writeRef >>> pure (\() -> 10000) >>> skipRef )) >>>
            pure (\(r,b) -> r) >>>
            readRef (SecLabel (Lab HIGH))
-}

t1 :: Int -> FlowArrowRef TriLabel ArrowRef () Int
t1 dtime = tagRef HIGH >>>
           lowerA HIGH (pure (\() -> 99)) >>> 
           createRef HIGH >>> 
           ( idRef &&& forkRef t2) >>> 
           ( second
              ( pure (\() -> 0) >>>
               --protectA (
               pure (\i -> if i > 5 then Left dtime else Right 0) >>>
                ( (skipRef >>> tagRef HIGH)
                 ||| 
                  (skipRef >>> tagRef HIGH)
                ) --) 
              )) >>> 
           second (pure (\_ -> 1)) >>>  -- (r,1)
           (fstPair &&& (writeRef >>> pure (\() -> 10000) >>> skipRef )) >>>
           fstPair >>>
           readRef (SecLabel (Lab HIGH)) 

t2 :: FlowArrowRef TriLabel ArrowRef (SecRef Int) ()
t2 = ( idRef &&& lowerA HIGH (pure (\_ -> 2))) >>> writeRef 

t3 :: FlowArrowRef TriLabel ArrowRef (SecRef Int) ()
t3 = ( idRef &&& lowerA HIGH (pure (\_ -> 3))) >>> writeRef

test1 dtime = runArrowRef (certifyRef (SecLabel (Lab LOW)) (SecLabel (Lab HIGH)) (PR HIGH) (t1 dtime)) ()

exet1 dtime = do begin <- getClockTime
                 (one,ten) <- recur 100 (0,0)
                 end <- getClockTime
                 dur <- return $ timeDiffToString (diffClockTimes end begin)
                 putStrLn $ "(1,2) = ("  ++ (show one) ++ "," ++ (show ten) ++ ") in " ++ dur
  where
  recur 0 (one,two) = return (one,two)
  recur n (one,two) = do
                         --begin <- getClockTime
                         result <- test1 dtime
                         --end <- getClockTime
                         --putStrLn $ show (diffClockTimes end begin)
                         putStrLn $ "# " ++ (show n)
                         if result == 1
                           then recur (n-1) (one+1,two)
                           else if result == 2 
                                  then recur (n-1) (one,two+1)
                                  else error "invalid value"
