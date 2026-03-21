{-# LANGUAGE OverloadedStrings #-}
-- | Golden test suite for DWARF parsing. See @doc\/dev.md@ for full documentation.
module Golden (tests) where

import           Control.Monad (filterM, forM, unless)
import           Data.List (isSuffixOf, isPrefixOf, nub, sort)
import           Data.Maybe (isJust)
import qualified Data.ByteString.Lazy.Char8 as BLC
import           System.Directory ( doesFileExist
                                  , doesDirectoryExist
                                  , findExecutable
                                  , listDirectory
                                  )
import           System.Environment (lookupEnv)
import           System.Exit (ExitCode(..))
import           System.FilePath (takeBaseName, (</>), (<.>))
import           System.Process (readProcess, readProcessWithExitCode)
import           Test.Tasty (TestTree, testGroup)
import           Test.Tasty.Golden (goldenVsStringDiff)

-- | All supported compiler identifiers. Must be kept in sync with
-- @ALL_COMPILERS@ and @RESOLVE_COMPILER@ in @tests\/Makefile@.
allCompilers :: [String]
allCompilers =
  [ "gcc-13-x86_64",   "clang-16-x86_64", "clang-17-x86_64", "clang-18-x86_64"
  , "gcc-13-aarch64",  "clang-18-aarch64"
  , "gcc-13-aarch32",  "clang-18-aarch32"
  , "gcc-13-ppc32",    "clang-18-ppc32"
  , "gcc-13-ppc64",    "clang-18-ppc64"
  ]

-- | Build the golden tests based on environment configuration
tests :: IO TestTree
tests = do
  fullMode <- isJust <$> lookupEnv "DWARF_FULL_TEST"
  dwarfDumpPath <- findDwarfDump
  compilerTests <-
    if fullMode
      then buildFullTests dwarfDumpPath
      else buildCommittedTests dwarfDumpPath
  return $ testGroup "Golden Tests" compilerTests

-- | Normal mode: test only compiler/fixture pairs with committed golden files.
buildCommittedTests :: FilePath -> IO [TestTree]
buildCommittedTests dwarfDumpPath = do
  compilers <- discoverCompilers
  forM compilers $ \compiler -> do
    fixtures <- discoverFixturesForCompiler compiler
    let tests' = map (goldenTest dwarfDumpPath compiler) fixtures
    return $ testGroup compiler tests'

-- | Full mode: test all compiler/fixture combinations regardless of @//%@ annotations.
-- Any missing golden files are auto-generated from @llvm-dwarfdump@ if available.
buildFullTests :: FilePath -> IO [TestTree]
buildFullTests dwarfDumpPath = do
  mLlvmPath <- findExecutable "llvm-dwarfdump"
  entries <- listDirectory "tests/test-data"
  let allFixtures = sort [ "tests/test-data" </> e | e <- entries, ".c" `isSuffixOf` e ]
  forM allCompilers $ \compiler -> do
    let fixtures = allFixtures
    tests' <- forM fixtures $ \cFile -> do
      let goldenFile = goldenPath (takeBaseName cFile) compiler
      goldenExists <- doesFileExist goldenFile
      unless goldenExists $
        case mLlvmPath of
          Nothing   -> return ()
          Just llvm -> generateGoldenFile llvm compiler cFile goldenFile
      return $ goldenTest dwarfDumpPath compiler cFile
    return $ testGroup compiler tests'

-- | Generate a golden file from llvm-dwarfdump output for a given compiler/fixture.
generateGoldenFile :: FilePath -> String -> FilePath -> FilePath -> IO ()
generateGoldenFile llvmPath compiler cFile goldenFile = do
  (dwarfDumpFlags, compilerFlags) <- extractFlags cFile
  let binFile = binaryPath (takeBaseName cFile) compiler
  precompiled <- doesFileExist binFile
  unless precompiled $
    compileFixture compiler compilerFlags cFile binFile
  output <- readProcess llvmPath (dwarfDumpFlags ++ [binFile]) ""
  sanitized <- sanitize output
  writeFile goldenFile sanitized

-- | Discover compilers that have at least one committed golden file.
discoverCompilers :: IO [String]
discoverCompilers = do
  entries <- listDirectory "tests/test-data"
  let compilers = nub
        [ compiler'
        | e <- entries
        , ".txt" `isSuffixOf` e
        , let base = take (length e - 4) e   -- drop .txt
        , '.' `elem` base
        , let compiler' = drop 1 (dropWhile (/= '.') base)  -- drop fixture + '.'
        , not (null compiler')
        ]
  return compilers

-- | Discover C fixture files that have committed golden files for a compiler.
discoverFixturesForCompiler :: String -> IO [FilePath]
discoverFixturesForCompiler compiler = do
  entries <- listDirectory "tests/test-data"
  let suffix = "." ++ compiler ++ ".txt"
  let cFiles = [ "tests/test-data" </> takeWhile (/= '.') e <.> "c"
               | e <- entries, suffix `isSuffixOf` e ]
  filterM doesFileExist cFiles

-- | Path to a compiled binary.
binaryPath :: String -> String -> FilePath
binaryPath fixture compiler = "tests/test-data" </> fixture ++ "." ++ compiler

-- | Path to a golden file.
goldenPath :: String -> String -> FilePath
goldenPath fixture compiler = "tests/test-data" </> fixture ++ "." ++ compiler ++ ".txt"

-- | Create golden test for a compiler/fixture pair.
--
-- Uses a pre-compiled binary at @tests\/test-data\/<fixture>.<compiler>@ if
-- present. Falls back to compiling with the named compiler if absent.
goldenTest :: FilePath -> String -> FilePath -> TestTree
goldenTest dwarfDumpPath compiler cFile =
  goldenVsStringDiff testName diff goldenFile $ do
    (dwarfDumpFlags, compilerFlags) <- extractFlags cFile
    let binFile = binaryPath fixture compiler
    precompiled <- doesFileExist binFile
    unless precompiled $
      compileFixture compiler compilerFlags cFile binFile
    output <- readProcess dwarfDumpPath (dwarfDumpFlags ++ [binFile]) ""
    sanitized <- sanitize output
    return $ BLC.pack sanitized
  where
    fixture    = takeBaseName cFile
    testName   = fixture
    goldenFile = goldenPath fixture compiler
    diff ref new = ["diff", "-u", ref, new]

-- | Find the dwarf-dump executable in cabal build directory
findDwarfDump :: IO FilePath
findDwarfDump = do
  let buildDir = "dist-newstyle/build"
  dirExists <- doesDirectoryExist buildDir
  if dirExists
    then do
      found <- findExecutableInDir buildDir "dwarf-dump"
      case found of
        Just path -> return path
        Nothing -> error "Could not find dwarf-dump executable. Please run 'cabal build dwarf-dump' first."
    else
      error "Build directory does not exist. Please run 'cabal build dwarf-dump' first."

-- | Recursively find an executable in a directory
findExecutableInDir :: FilePath -> String -> IO (Maybe FilePath)
findExecutableInDir dir name = do
  entries <- listDirectory dir
  let paths = map (dir </>) entries
  dirs  <- filterM doesDirectoryExist paths
  files <- filterM doesFileExist paths
  let matches = filter ((== name) . last . splitPath) files
  case matches of
    (exe:_) -> return $ Just exe
    [] -> do
      results <- mapM (\d -> findExecutableInDir d name) dirs
      return $ foldr (<|>) Nothing results
  where
    Nothing <|> b = b
    a       <|> _ = a
    splitPath = foldr f [[]]
      where f c (x:xs) | c == '/'  = [] : x : xs
                       | otherwise = (c:x) : xs
            f _ [] = []

-- | Extract flags from C file comments
--
-- * Lines starting with @//# @ specify dwarf-dump flags
-- * Lines starting with @//\@ @ specify compiler flags
extractFlags :: FilePath -> IO ([String], [String])
extractFlags path = do
  contents <- readFile path
  let ls = lines contents
  let dwarfDumpFlags = [drop 4 l | l <- ls, "//# " `isPrefixOf` l]
  let compilerFlags  = [drop 4 l | l <- ls, "//@ " `isPrefixOf` l]
  return (dwarfDumpFlags, compilerFlags)

-- | Map a compiler identifier to its binary and any cross-compilation flags.
-- Must be kept in sync with @RESOLVE_COMPILER@ in @tests\/Makefile@.
resolveCompiler :: String -> (String, [String])
resolveCompiler c = case c of
  "gcc-13-x86_64"    -> ("gcc-13",   [])
  "clang-16-x86_64"  -> ("clang-16", [])
  "clang-17-x86_64"  -> ("clang-17", [])
  "clang-18-x86_64"  -> ("clang-18", [])
  "gcc-13-aarch64"   -> ("aarch64-linux-gnu-gcc-13",    [])
  "clang-18-aarch64" -> ("clang-18", ["--target=aarch64-linux-gnu"])
  "gcc-13-aarch32"   -> ("arm-linux-gnueabihf-gcc-13",  [])
  "clang-18-aarch32" -> ("clang-18", ["--target=arm-linux-gnueabihf"])
  "gcc-13-ppc32"     -> ("powerpc-linux-gnu-gcc-13",    [])
  "clang-18-ppc32"   -> ("clang-18", ["--target=powerpc-linux-gnu"])
  "gcc-13-ppc64"     -> ("powerpc64le-linux-gnu-gcc-13",[])
  "clang-18-ppc64"   -> ("clang-18", ["--target=powerpc64le-linux-gnu"])
  _                  -> (c, [])

-- | Compile C fixture with extracted flags.
-- Uses -nostdlib -nostartfiles to avoid cross-libc dependencies while still
-- producing a fully linked ELF with resolved DWARF relocations.
compileFixture :: String -> [String] -> FilePath -> FilePath -> IO ()
compileFixture compiler compilerFlags cFile oFile = do
  let (binary, crossFlags) = resolveCompiler compiler
  let allFlags = ["-nostdlib", "-nostartfiles", "-g", "-O0"]
               ++ crossFlags ++ compilerFlags ++ [cFile, "-o", oFile]
  (exitCode, _stdout, stderr) <- readProcessWithExitCode binary allFlags ""
  case exitCode of
    ExitSuccess -> return ()
    ExitFailure n ->
      error $ unlines
        [ "Compilation with " ++ compiler ++ " failed (exit " ++ show n ++ "): " ++ stderr
        , "Hint: pre-compile fixtures via Docker to match the CI environment:"
        , "  docker build --platform linux/amd64 -t galois-dwarf-golden tests/"
        , "  docker run --platform linux/amd64 --rm -v $(pwd):/work galois-dwarf-golden make -f tests/Makefile compile"
        ]

-- | Sanitize output for environment-independent golden comparison by piping
-- through @tests\/sanitize.sh@, which is the single source of truth for
-- sanitization rules (also used by @tests\/Makefile@ when generating golden files).
sanitize :: String -> IO String
sanitize input = readProcess "sh" ["tests/sanitize.sh"] input
