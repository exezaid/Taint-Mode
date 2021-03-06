
--module Bidders where

import BidLattice
import FlowArrowRef
import Lattice
import Control.Arrow
import SecureFlow
import Unification
import RefOp
import System.Random

type Protected b c = FlowArrowRef BidLabel ArrowRef b c

type Bid = Int      -- Value of the bid.
type Ident = Int    -- Identity number of a customer.
type Result = Int   -- < 0 for join, == 0 for lost, and > 0 for get a new bid.
type HostData = (Bid,[(Ident,Result)])

----------
-- Host --
----------
main = do (b,history) <- runArrowRef (certifyRef (SecLabel (Lab SYS)) 
                                                 (Pair (SecLabel (Lab SYS)) (SecLabel (Lab SYS))) 
                                                 (PR USER) baseMain) ()
          putStrLn $ "Final bid : " ++ (show b)
          putStrLn $ "History   :\n" ++ parseHistory (reverse history)

parseHistory :: [(Ident,Result)] -> String
parseHistory = concatMap parHs 
  where
  parHs (i,r) = if r < 0
                  then msg i ("join with bid " ++ (show (-r)))
                  else if r == 0
                         then msg i "lost"
                         else msg i ("gets " ++ (show r))
  msg i s = "[Bidder " ++ (show i) ++ " " ++ s ++ "]\n"

-- Base system
baseMain :: Protected () HostData
baseMain = baseInitState >>> 
           (((idRef 
               &&& 
              (nullRef >>> tagRef SYS >>> lowerA SYS (pure (\_ -> (0::Int,4::Int))))
             ) >>>
             (iterateA baseNewBidder)  
            )
            &&&
            idRef
           ) >>>
           sndPair >>>
           ((nullRef >>> tagRef SYS >>>
             lowerA SYS (pure (\_ -> 200 )) >>> skipRef
            )
            &&&
            readRef (Pair (SecLabel (Lab SYS)) (SecLabel (Lab SYS)))
           ) >>>
           lowerA SYS (pure (\(_,re) -> re ))
           
           
-- Create initial state of system
baseInitState :: Protected () (SecRef HostData)
baseInitState = tagRef SYS >>> lowerA SYS (pure (\() -> (0,[]))) >>> createRef SYS

-- Generate a new bidder
baseNewBidder :: Protected (SecRef HostData,(Int,Int)) ((SecRef HostData,(Int,Int)),Bool)
baseNewBidder = lowerA SYS (pure (\d@(r,(n,t))-> if n < t then Left d else Right d )) >>>
                ((((lowerA SYS (pure (\(r,(n,t)) -> (r,n))) >>> forkRef bidderInit)
                   &&&
                   (lowerA SYS (pure (\(r,(n,t)) -> ((r,(n+1,t)),True) )) )
                  ) >>> 
                  lowerA SYS (pure (\(a,b) -> b))
                 )
                 ||| 
                 lowerA SYS (pure (\((r,(n,t))) -> ((r,(n,t)),False) ))
                )

{- ArrowLoop version                 
baseNewBidder :: Protected ((SecRef BidLabel HostData,(Int,Int)),Int) ((SecRef BidLabel HostData,(Int,Int)),Int)
baseNewBidder = lowerA SYS (pure (\d@((r,(n,t)),(c))-> if n < t then Left d else Right d )) >>>
                ((((lowerA SYS (pure (\((r,(n,t)),c) -> (r,n))) >>> forkRef bidderInit)
                   &&&
                   (lowerA SYS (pure (\((r,(n,t)),c) -> ((r,(n+1,t)),c) )) )
                  ) >>> 
                  lowerA SYS (pure (\(a,b) -> b))
                 )
                 ||| 
                 lowerA SYS (pure (\(~((r,(n,t)),c)) -> ((r,(n,t)),0) ))
                )
-}

bidderInit :: Protected (SecRef HostData,Ident) ()
bidderInit = tagRef USER >>> 
             (second
               (idRef
                &&&
                (lowerA USER (pure (\_ -> 0)) >>> randomRRef 50 100)
               )
             ) >>>
             (idRef
              &&&
              (protectA 
               (
               (first
                 (idRef
                   &&&
                  readRef (Pair (SecLabel (Lab USER)) (SecLabel (Lab USER)))
                 )
               ) >>>
               pairRight >>>
               (second
                 (lowerA USER (pure (\((bid,his),(i,b)) -> (bid,(i,(-b)):his) )))
               ) 
               >>>
               declassifyRef SYS >>>
               writeRef )
              )
             ) >>>
             fstPair >>> 
             tagRef USER >>>
             iterateA bidderAction >>>
             nullRef

{-
bidderInit :: Protected (SecRef HostData,Ident) ()
bidderInit = tagRef USER >>> 
             -- the content of reference is low
             (lowerA USER (pure id)
              &&& 
              (lowerA USER (pure (\_ -> 0)) >>> randomRRef 50 100)
             ) >>> 
             (protectA (
              (((lowerA USER (pure (\((r,i),b) -> r)) >>> readRef (Pair (SecLabel (Lab USER)) (SecLabel (Lab USER))))
               &&&
               lowerA USER (pure id)
               ) >>>
               lowerA USER (pure (\((bid,his),((r,i),b)) -> (r,(bid,(i,b):his)))) >>>
               declassifyRef SYS >>>
               writeRef
              ) 
              &&&
              lowerA USER (pure id) )
             ) >>>
             tagRef USER >>>
             lowerA USER (pure (\(a,b) -> b)) >>>
             (iterateA bidderAction) >>>
             lowerA USER (pure (\_ -> ()))

dlabel1 = (Pair (Ref (Pair (SecLabel (Lab SYS)) (SecLabel (Lab SYS))) (Lab SYS))
                (Pair (SecLabel (Lab SYS)) (SecLabel (Lab SYS)))
                )
-}

bidderAction :: Protected (SecRef HostData,(Ident,Bid)) ((SecRef HostData,(Ident,Bid)),Bool)
bidderAction = (idRef
                &&&
                protectA
                (
                 (first
                   (idRef
                    &&&
                    readRef (Pair (SecLabel (Lab USER)) (SecLabel (Lab USER)))
                   )
                 ) >>>
                 pairRight >>>  -- (r,((bid,his),(i,bu)))
                 declassifyRef SYS >>>
                 (second 
                  (
                   (lowerA SYS (pure (\((bid,his),(i,bu)) -> if bu > bid
                                                               then Left ((bid,his),i)
                                                               else Right ((bid,his),i) ))) >>>
                   (
                    (lowerA SYS (pure (\((bid,his),i) -> if (length his == 0) || (notLastBidder his i)
                                                           then ((bid+1,(i,bid+1):his),True)
                                                           else ((bid,his),True) )))
                    |||
                    (lowerA SYS (pure (\((bid,his),i) -> ((bid,(i,0):his), False) )))
                   )
                  )
                 ) >>>
                 pairLeft >>>
                 (first writeRef) >>>
                 sndPair >>>
                 tagRef USER
                )
               )  
  where
  notLastBidder his i = if (snd.head) his /= 0
                          then (fst.head) his /= i
                          else notLastBidder (tail his) i      
                
{-
               protectA (
               ((lowerA USER (pure (\((r,i),bu) -> r)) >>> readRef (Pair (SecLabel (Lab USER)) (SecLabel (Lab USER))) )
                &&&
                lowerA USER (pure id)
               ) >>>
               (lowerA USER (pure (\(a,b) -> b)) 
                &&&
                (declassifyRef SYS >>>
                 (lowerA SYS (pure (\((bid,his),((r,i),bu)) -> if bu > bid 
                                                                 then Left ((bid,his),(r,i))
                                                                 else Right ((bid,his),(r,i)) )) >>>
                  ((lowerA SYS (pure (\((bid,his),(r,i)) -> if (length his == 0) || ((fst.head) his /= i)
                                                              then Left (r,(bid+1,(i,bid+1):his))
                                                              else Right (r,(bid,his)) )) >>>
                    (writeRef --(declassifyRef dlabel >>> writeRef)
                     |||
                     lowerA SYS (pure (\_ -> ()))
                    ) >>>
                    lowerA SYS (pure (\_ -> True))
                   )
                   |||
                   (lowerA SYS (pure (\((bid,his),(r,i)) -> (r,(bid,(i,(-1)):his)) )) >>>
                 -- declassifyRef dlabel >>>
                    writeRef >>> 
                    lowerA SYS (pure (\_ -> False))
                   )
                  )
                 ) >>>
                 tagRef USER >>>
                 lowerA USER (pure id)
                )
               ) 
              )

dlabel2 = Pair (Pair (SecLabel (Lab SYS)) (SecLabel (Lab SYS)))
               (Pair (Pair (Ref (Pair (SecLabel (Lab SYS)) (SecLabel (Lab SYS))) (Lab SYS)) 
                           (SecLabel (Lab SYS))) 
                     (SecLabel (Lab SYS)))
-}               
