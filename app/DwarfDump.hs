module Main (main) where

import           Control.Monad (when)
import qualified Data.Text.Lazy.IO as TLIO
import qualified Options.Applicative as Opt
import           System.Exit (die)

import           ElfLoader (loadDwarfFromElf)
import           PrettyPrint (ppDebugInfo)

data Options = Options
  { optFile :: FilePath
  , optDebugInfo :: Bool
  }

optionsParser :: Opt.Parser Options
optionsParser = Options
  <$> Opt.argument Opt.str (Opt.metavar "FILE")
  <*> Opt.switch (Opt.long "debug-info" <> Opt.help "Dump .debug_info section")

main :: IO ()
main = do
  opts <- Opt.execParser $ Opt.info (optionsParser Opt.<**> Opt.helper)
    ( Opt.fullDesc
    <> Opt.progDesc "Dump DWARF debug information"
    <> Opt.header "dwarf-dump - DWARF information dumper" )

  result <- loadDwarfFromElf (optFile opts)
  case result of
    Left err -> die $ "Error loading ELF file: " ++ err
    Right (fileFormat, endian, sections) -> do
      when (optDebugInfo opts) $ do
        putStrLn $ optFile opts ++ ":\tfile format " ++ fileFormat
        putStrLn ""
        TLIO.putStr $ ppDebugInfo endian sections
