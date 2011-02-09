{-# OPTIONS -fglasgow-exts #-}

module RefOp where

import Data.IORef
import Lattice

-- Data for reference
-- (SecType l) is security label of content. This should not change along computation.
-- (a->a) is a write projection function
-- Write projection function is not necessary if we keep the security label of the content invariant.
data SecRef a = SecRef (IORef a) (a->a) 

newSecRef :: a -> IO (SecRef a)
newSecRef a = do r <- newIORef a
                 return (SecRef r id)

readSecRef :: SecRef a -> IO a
readSecRef (SecRef r f) = do a <- readIORef r
                             return (f a)

writeSecRef :: SecRef a -> a -> IO ()
writeSecRef (SecRef r f) a = writeIORef r a


-- Class RefMonad
class RefMonad m r | m -> r where
  createMRef :: a -> m (r a)
  readMRef :: (r a) -> m a
  writeMRef :: (r a) -> a -> m ()

instance RefMonad IO SecRef where
  createMRef = newSecRef
  readMRef = readSecRef
  writeMRef = writeSecRef


