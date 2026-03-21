-- | Test suite entry point. See @doc\/dev.md@ for full documentation.
module Main (main) where

import           Test.Tasty (defaultMain, testGroup)
import qualified Golden
import qualified SLEB128Tests

main :: IO ()
main = do
  goldenTests <- Golden.tests
  defaultMain $ testGroup "DWARF Tests"
    [ goldenTests
    , testGroup "SLEB128 Tests" SLEB128Tests.tests
    ]
