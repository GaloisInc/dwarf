{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Main (main) where

import           Control.Exception
import           Control.Monad (forM_, when)
import           Control.Monad.IO.Class (MonadIO)
import           Control.Monad.Reader (ReaderT(..))
import qualified Data.ByteString as BS
import           Data.Dwarf.Internals
import           Data.IORef
import           Data.Int
import           Data.Word
import           System.Exit
import           System.IO


-- | Ifnormation about a test case
data TestCtx = TestCtx { tctxName :: !String
                       , tctxArgs :: ![(String, String)]
                       }

newtype TestM a = TestM (ReaderT TestCtx IO a)
  deriving (Functor, Applicative, Monad, MonadIO)

data TestException = TestException
  deriving Show

instance Exception TestException

testFailure :: String -> TestM a
testFailure msg = TestM $ ReaderT $ \ctx -> do
  hPutStrLn stderr $ tctxName ctx ++ " failed."
  forM_ (tctxArgs ctx) $ \(fld, val) -> do
    hPutStrLn stderr $ fld ++ ": " ++ val
  hPutStrLn stderr $  msg
  throwIO TestException

newtype TestCase = TestCase (IO ())

-- | `runTest nm args m` runs the test given by the test suite.
mkTest :: String -> [(String, String)] -> TestM () -> TestCase
mkTest nm args (TestM m) = TestCase $ do
  runReaderT m (TestCtx nm args)

parseSLEB :: Int64 -> [Word8] -> TestCase
parseSLEB expected bytes =
  mkTest "parseSLEB" [("Bytes", show bytes)] $
    case tryStrictGet getSLEB128 (BS.pack bytes) of
      Left (_,msg) -> do
        testFailure $ "Parse failure: " ++ msg
      Right (bytes', _, actual) -> do
        when (BS.length bytes' /= 0) $ do
          testFailure "Bytes remaining"
        when (actual /= expected) $ do
          testFailure $ "Unexpected actual " ++ show actual

runTests :: [TestCase] -> IO ()
runTests cases = do
  r <- newIORef False
  let h :: TestException -> IO ()
      h _ = writeIORef r True
  forM_ cases $ \(TestCase m) -> catch m h
  failed <- readIORef r
  when failed $ exitFailure

main :: IO ()
main =
  runTests
    [ parseSLEB     2  [ 2 ]
    , parseSLEB   (-2) [ 0x7e ]
    , parseSLEB   127  [127 + 0x80,  0]
    , parseSLEB (-127) [1 + 0x80,    0x7f]
    , parseSLEB   128  [0 + 0x80,    1]
    , parseSLEB (-128) [0 + 0x80,    0x7f]
    , parseSLEB   129  [1 + 0x80,    1]
    , parseSLEB (-129) [0x7f + 0x80, 0x7e]
    , parseSLEB   (-1) [ 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f ]
    ]
