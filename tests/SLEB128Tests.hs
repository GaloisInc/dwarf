{-# LANGUAGE OverloadedStrings #-}
-- | SLEB128 encoding tests
module SLEB128Tests (tests) where

import           Data.Binary.Get (runGetOrFail)
import           Data.Int (Int64)
import qualified Data.ByteString.Lazy as BL
import           Data.Dwarf.Internals (getSLEB128)
import           Data.Word (Word8)
import           Test.Tasty (TestTree)
import           Test.Tasty.HUnit (testCase, (@?=), assertFailure)
import           Control.Monad (when)

-- | SLEB128 parsing tests
tests :: [TestTree]
tests =
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

parseSLEB :: Int64 -> [Word8] -> TestTree
parseSLEB expected bytes =
  testCase ("parseSLEB " ++ show expected ++ " " ++ show bytes) $ do
    let bs = BL.pack bytes
    case runGetOrFail getSLEB128 bs of
      Left (_,_,msg) -> assertFailure $ "Parse failure: " ++ msg
      Right (remaining, _, actual) -> do
        when (BL.length remaining /= 0) $
          assertFailure "Bytes remaining after parse"
        actual @?= expected
