{-# OPTIONS -fglasgow-exts #-}

module RefOp where

import Data.IORef

data SRef rs a = MkSRef rs (IORef a) (a->a)

newSRef :: a -> rs -> IO (SRef rs a)
newSRef a rs = do r <- newIORef a
                  return (MkSRef rs r id)

readSRef :: SRef rs a -> IO a
readSRef (MkSRef rs r f) = do x <- readIORef r
                              return (f x)

writeSRef :: SRef rs a -> a -> IO ()
writeSRef (MkSRef rs r _) a = writeIORef r a

class RefMonad m r rs | m -> r where
  createMRef :: a -> rs -> m (r rs a) 
  readMRef :: (r rs a) -> m a
  writeMRef :: (r rs a) -> a -> m ()

instance RefMonad IO SRef rs where
  createMRef = newSRef
  readMRef = readSRef
  writeMRef = writeSRef



