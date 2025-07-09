{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Data.Dwarf.LNI where

import           Control.Monad (replicateM, forM)
import           Data.Binary (Binary(..), Get)
import           Data.Binary.Get (getWord8, bytesRead)
import qualified Data.ByteString as B
import           Data.Dwarf.Internals
import           Data.Dwarf.Reader
import           Data.Int (Int8, Int64)
import           Data.Word (Word8, Word64)
import           qualified Data.Map as Map
import Data.Dwarf.Form
import Data.Dwarf.AT
import Data.Maybe (fromMaybe)

-- Section 7.21 - Line Number Information
data DW_LNI
    = DW_LNI_special Word64 Int64
    | DW_LNS_copy
    | DW_LNS_advance_pc Word64
    | DW_LNS_advance_line Int64
    | DW_LNS_set_file Word64
    | DW_LNS_set_column Word64
    | DW_LNS_negate_stmt
    | DW_LNS_set_basic_block
    | DW_LNS_const_add_pc Word64
    | DW_LNS_fixed_advance_pc Word64
    | DW_LNS_set_prologue_end
    | DW_LNS_set_epilogue_begin
    | DW_LNS_set_isa Word64
    | DW_LNE_end_sequence
    | DW_LNE_set_address Word64
    | DW_LNE_define_file !B.ByteString Word64 Word64 Word64
    | DW_LNE_set_descriminator !Word64
    deriving (Eq, Ord, Read, Show)

getDW_LNE :: Endianess -> TargetSize -> Get DW_LNI
getDW_LNE end tgt = do
  w <- getWord8
  case w of
    0x01 ->
      pure DW_LNE_end_sequence
    0x02 ->
      DW_LNE_set_address <$> getTargetAddress end tgt
    0x03 ->
      DW_LNE_define_file <$> getByteStringNul
                         <*> getULEB128
                         <*> getULEB128
                         <*> getULEB128
    0x04 ->
      DW_LNE_set_descriminator <$> getULEB128
    _ | 0x80 <= w && w <= 0xff ->
        fail $ "User DW_LNE data requires extension of parser for code " ++ show w
      | otherwise ->
        fail $ "Unexpected DW_LNE code " ++ show w

getDW_LNI :: Endianess -> TargetSize  -> Int64 -> Word8 -> Word8 -> Word64 -> Get DW_LNI
getDW_LNI end tgt line_base line_range opcode_base minimum_instruction_length = fromIntegral <$> getWord8 >>= getDW_LNI_
    where getDW_LNI_ 0x00 = do
            rest <- getByteStringLen getULEB128
            case tryStrictGet (getDW_LNE end tgt) rest of
              Left (_, msg) -> fail msg
              Right (_, _, r) -> pure r

          getDW_LNI_ 0x01 = pure DW_LNS_copy
          getDW_LNI_ 0x02 = pure DW_LNS_advance_pc <*> (* minimum_instruction_length) <$> getULEB128
          getDW_LNI_ 0x03 = pure DW_LNS_advance_line <*> getSLEB128
          getDW_LNI_ 0x04 = pure DW_LNS_set_file <*> getULEB128
          getDW_LNI_ 0x05 = pure DW_LNS_set_column <*> getULEB128
          getDW_LNI_ 0x06 = pure DW_LNS_negate_stmt
          getDW_LNI_ 0x07 = pure DW_LNS_set_basic_block
          getDW_LNI_ 0x08 = pure $ DW_LNS_const_add_pc (minimum_instruction_length * fromIntegral ((255 - opcode_base) `div` line_range))
          getDW_LNI_ 0x09 = pure DW_LNS_fixed_advance_pc <*> fromIntegral <$> derGetW16 end
          getDW_LNI_ 0x0a = pure DW_LNS_set_prologue_end
          getDW_LNI_ 0x0b = pure DW_LNS_set_epilogue_begin
          getDW_LNI_ 0x0c = pure DW_LNS_set_isa <*> getULEB128
          getDW_LNI_ n | n >= opcode_base =
            let addr_incr = minimum_instruction_length * fromIntegral ((n - opcode_base) `div` line_range)
                line_incr = line_base + fromIntegral ((n - opcode_base) `mod` line_range)
             in pure $ DW_LNI_special addr_incr line_incr
          getDW_LNI_ n = fail $ "Unexpected DW_LNI opcode " ++ show n

stepLineMachine :: Bool -> Word8 -> DW_LNE -> [DW_LNI] -> [DW_LNE]
stepLineMachine _ _ _ [] = []
stepLineMachine is_stmt mil lnm (DW_LNI_special addr_incr line_incr : xs) =
    let row = lnm { lnmAddress = lnmAddress lnm + addr_incr, lnmLine = lnmLine lnm + fromIntegral line_incr }
        new = row { lnmDescriminator = 0
                  , lnmBasicBlock = False
                  , lnmPrologueEnd = False
                  , lnmEpilogueBegin = False
                  }
    in row : stepLineMachine is_stmt mil new xs
stepLineMachine is_stmt mil lnm (DW_LNS_copy : xs) =
    let row = lnm
        new = row { lnmDescriminator = 0
                  , lnmBasicBlock = False
                  , lnmPrologueEnd = False
                  , lnmEpilogueBegin = False
                  }
    in row : stepLineMachine is_stmt mil new xs
stepLineMachine is_stmt mil lnm (DW_LNS_advance_pc incr : xs) =
    let new = lnm { lnmAddress = lnmAddress lnm + incr }
    in stepLineMachine is_stmt mil new xs
stepLineMachine is_stmt mil lnm (DW_LNS_advance_line incr : xs) =
    let new = lnm { lnmLine = lnmLine lnm + fromIntegral incr }
    in stepLineMachine is_stmt mil new xs
stepLineMachine is_stmt mil lnm (DW_LNS_set_file file : xs) =
    let new = lnm { lnmFile = file }
    in stepLineMachine is_stmt mil new xs
stepLineMachine is_stmt mil lnm (DW_LNS_set_column col : xs) =
    let new = lnm { lnmColumn = col }
    in stepLineMachine is_stmt mil new xs
stepLineMachine is_stmt mil lnm (DW_LNS_negate_stmt : xs) =
    let new = lnm { lnmStatement = not (lnmStatement lnm) }
    in stepLineMachine is_stmt mil new xs
stepLineMachine is_stmt mil lnm (DW_LNS_set_basic_block : xs) =
    let new = lnm { lnmBasicBlock = True }
    in stepLineMachine is_stmt mil new xs
stepLineMachine is_stmt mil lnm (DW_LNS_const_add_pc incr : xs) =
    let new = lnm { lnmAddress = lnmAddress lnm + incr }
    in stepLineMachine is_stmt mil new xs
stepLineMachine is_stmt mil lnm (DW_LNS_fixed_advance_pc incr : xs) =
    let new = lnm { lnmAddress = lnmAddress lnm + incr }
    in stepLineMachine is_stmt mil new xs
stepLineMachine is_stmt mil lnm (DW_LNS_set_prologue_end : xs) =
    let new = lnm { lnmPrologueEnd = True }
    in stepLineMachine is_stmt mil new xs
stepLineMachine is_stmt mil lnm (DW_LNS_set_epilogue_begin : xs) =
    let new = lnm { lnmEpilogueBegin = True }
    in stepLineMachine is_stmt mil new xs
stepLineMachine is_stmt mil lnm (DW_LNS_set_isa isa : xs) =
    let new = lnm { lnmISA = isa }
    in stepLineMachine is_stmt mil new xs
stepLineMachine is_stmt mil lnm (DW_LNE_end_sequence : xs) =
    let row = lnm { lnmEndSequence = True }
        new = defaultLNE is_stmt (lnmFiles lnm)
    in row : stepLineMachine is_stmt mil new xs
stepLineMachine is_stmt mil lnm (DW_LNE_set_address address : xs) =
    let new = lnm { lnmAddress = address }
    in stepLineMachine is_stmt mil new xs
stepLineMachine is_stmt mil lnm (DW_LNE_define_file name dir_index time len : xs) =
    let new = lnm { lnmFiles = lnmFiles lnm ++ [(name, dir_index, time, len)] }
    in stepLineMachine is_stmt mil new xs
stepLineMachine is_stmt mil lnm (DW_LNE_set_descriminator d : xs) =
    let new = lnm { lnmDescriminator =  d }
     in stepLineMachine is_stmt mil new xs

data DW_LNE = DW_LNE
    { lnmAddress       :: Word64
    , lnmFile          :: Word64
    , lnmLine          :: Word64
    , lnmColumn        :: Word64
    , lnmStatement     :: Bool
    , lnmDescriminator :: !Word64
    , lnmBasicBlock    :: Bool
    , lnmEndSequence   :: Bool
    , lnmPrologueEnd   :: Bool
    , lnmEpilogueBegin :: Bool
    , lnmISA           :: Word64
    , lnmFiles         :: [(B.ByteString, Word64, Word64, Word64)]
    } deriving (Eq, Ord, Read, Show)

defaultLNE :: Bool -> [(B.ByteString, Word64, Word64, Word64)] -> DW_LNE
defaultLNE is_stmt files = DW_LNE
    { lnmAddress       = 0
    , lnmFile          = 1
    , lnmLine          = 1
    , lnmColumn        = 0
    , lnmStatement     = is_stmt
    , lnmDescriminator = 0
    , lnmBasicBlock    = False
    , lnmEndSequence   = False
    , lnmPrologueEnd   = False
    , lnmEpilogueBegin = False
    , lnmISA           = 0
    , lnmFiles         = files
    }

-- | Retrieves the line information for a DIE from a given substring
-- of the .debug_line section. The offset into the .debug_line section
-- is obtained from the DW_AT_stmt_list attribute of a DIE.
parseLNE :: Sections -> Endianess -> TargetSize -> Word64 -> B.ByteString -> ([B.ByteString], [DW_LNE])
parseLNE secs endianess target64 offset bs =
  let bs' = B.drop (fromIntegral offset) bs
   in case tryStrictGet (getLNE secs endianess target64) bs' of
        Left (_, msg) -> error msg
        Right (_, _, r) -> r

getDebugLineFileNames :: Get [(B.ByteString, Word64, Word64, Word64)]
getDebugLineFileNames = go []
  where go prev = do
          -- Read fillnames until we get a null.
          fileName <- getByteStringNul
          if B.null fileName then
            pure (reverse prev)
           else do
            dir_index   <- getULEB128
            last_mod    <- getULEB128
            file_length <- getULEB128
            go ((fileName, dir_index, last_mod, file_length):prev)




newtype DW_LNCT = DW_LNCT Word64 
      deriving (Eq,Ord)

pattern DW_LNCT_path :: DW_LNCT
pattern DW_LNCT_path = DW_LNCT 0x1

pattern DW_LNCT_directory_index :: DW_LNCT
pattern DW_LNCT_directory_index = DW_LNCT 0x2

pattern DW_LNCT_size :: DW_LNCT
pattern DW_LNCT_size = DW_LNCT 0x4


data LineFileEntryFormat = LineFileEntryFormat {contentType :: DW_LNCT, form:: DW_FORM}

parseLineEntryToVal ::  Sections -> Endianess -> Encoding -> TargetSize -> LineFileEntryFormat -> Get (DW_LNCT,DW_ATVAL)
parseLineEntryToVal secs end encoding tgt (LineFileEntryFormat {contentType=ct, form=form'}) = 
    (ct,) <$> getRealizedForm secs end encoding tgt form'
        


parseFileEntryForm :: Get LineFileEntryFormat
parseFileEntryForm = do
    contentTy <- getULEB128
    formCode <- getULEB128
    pure $ LineFileEntryFormat {contentType=DW_LNCT contentTy, form=DW_FORM formCode}

parseFormList :: Int -> Get [LineFileEntryFormat]
parseFormList ct = 
    replicateM ct parseFileEntryForm


data FileLineHeaderEntry = FileLineHeaderEntry (Map.Map DW_LNCT DW_ATVAL)


parseEntry :: Sections -> Endianess -> Encoding -> TargetSize -> [LineFileEntryFormat] -> Get FileLineHeaderEntry
parseEntry secs end enc tgt forms = FileLineHeaderEntry . Map.fromList <$> forM forms (parseLineEntryToVal secs end enc tgt)

-- | Parse an array of entries given a declared format
parseEntries :: Int -> Sections -> Endianess -> Encoding -> TargetSize -> [LineFileEntryFormat] -> Get [FileLineHeaderEntry]
parseEntries entNum secs end encoding tgt ents = replicateM entNum (parseEntry secs end encoding tgt ents)


getWithDefault :: FileLineHeaderEntry -> DW_LNCT -> (DW_ATVAL -> Maybe a) -> a -> a 
getWithDefault (FileLineHeaderEntry mp) k f d =
        fromMaybe d (do 
            atVal <- Map.lookup k mp
            f atVal)

createLegacyFileName :: FileLineHeaderEntry -> LegacyFileName 
createLegacyFileName hd = 
    let defU64 lc d = getWithDefault hd lc (\case {DW_ATVAL_UINT s -> Just s; _ -> Nothing}) d
        pth = getWithDefault hd DW_LNCT_path (\case {DW_ATVAL_STRING s -> Just s; _ -> Nothing}) ""
        dirIndex = defU64 DW_LNCT_directory_index 0 
        size = defU64 DW_LNCT_size 0 
    in (pth, dirIndex, 0, size)
parsePaths :: Int -> Sections -> Endianess -> Encoding -> TargetSize -> [LineFileEntryFormat] -> Get [LegacyFileName]
parsePaths entNum secs end encoding tgt formEnts = 
    let ents = parseEntries entNum secs end encoding tgt formEnts in 
      map createLegacyFileName  <$> ents


type LegacyFileName = (B.ByteString, Word64, Word64, Word64)
data ParsedLineHeader = ParsedLineHeader {lineBase :: Int8, lineRange :: Word8, opCodeBase :: Word8, minimumInstructionLength :: Word8, defaultIsStmt :: Bool,
    fileNames :: [LegacyFileName]}

parseLNEV5 :: Sections -> Endianess -> Encoding -> TargetSize ->  Get ParsedLineHeader 
parseLNEV5 secs endianess enc target64  = do 
    _addrSize <- getWord8
    _segSelectorSize <- getWord8
    _header_length      <- desrGetOffset endianess enc
    minimum_instruction_length <- getWord8
    _maximum_operations_per_instruction <- getWord8
    default_is_stmt            <- (/= 0) <$> getWord8
    line_base                  <- get :: Get Int8
    line_range                 <- getWord8
    opcode_base                <- getWord8
    _standard_opcode_lengths   <- replicateM (fromIntegral opcode_base - 1) getWord8
    dirEntryCount <- getWord8
    dirForms <- parseFormList (fromIntegral dirEntryCount)
    dirCount <- getULEB128
    _includes <- parsePaths (fromIntegral dirCount) secs endianess enc target64 dirForms
    fileNameEntryCount <- getWord8
    fileForms <- parseFormList (fromIntegral fileNameEntryCount)
    fileNamesCount <- getULEB128
    fileNames' <- parsePaths (fromIntegral fileNamesCount) secs endianess enc target64 fileForms
    pure ParsedLineHeader {lineBase=line_base, lineRange=line_range, opCodeBase=opcode_base, minimumInstructionLength=minimum_instruction_length, 
        defaultIsStmt=default_is_stmt, fileNames=fileNames'}

parseLNEV4 :: Endianess -> Encoding -> Get ParsedLineHeader 
parseLNEV4 endianess enc = do 
    _header_length             <- desrGetOffset endianess enc
    minimum_instruction_length <- getWord8
    default_is_stmt            <- (/= 0) <$> getWord8
    line_base                  <- get :: Get Int8
    line_range                 <- getWord8
    opcode_base                <- getWord8
    _standard_opcode_lengths   <- replicateM (fromIntegral opcode_base - 1) getWord8
    _include_directories       <- whileM (\b -> not (B.null b)) getByteStringNul
    file_names'                 <- getDebugLineFileNames
    pure ParsedLineHeader {lineBase=line_base, lineRange=line_range, opCodeBase=opcode_base, minimumInstructionLength=minimum_instruction_length, 
        defaultIsStmt=default_is_stmt, fileNames=file_names'} 


data LNEContext = LNEContext {file_names :: [B.ByteString]}

getLNE :: Sections -> Endianess -> TargetSize -> Get ([B.ByteString], [DW_LNE])
getLNE secs endianess target64 = do
    (enc, size) <- getDwarfSize endianess
    pos <- bytesRead
    let endPos = fromIntegral pos + size
    version                   <- derGetW16 endianess
    prsed <- if version >= 5 then parseLNEV5 secs endianess enc target64 else parseLNEV4 endianess enc
    curPos <- fromIntegral <$> bytesRead
    -- Check if we have reached the end of the section.
    let fnames = fileNames prsed
    let line_base = lineBase prsed
    let opcode_base = opCodeBase prsed
    let line_range = lineRange prsed 
    let minimum_instruction_length = minimumInstructionLength prsed
    let default_is_stmt = defaultIsStmt prsed
    if endPos <= curPos
      then pure (map (\(name, _, _, _) -> name) fnames, [])
      else do
        line_program <-
          fmap (++ [DW_LNE_end_sequence]) .
          whileM (/= DW_LNE_end_sequence) .
            getDW_LNI endianess target64 (fromIntegral line_base) line_range opcode_base $
            fromIntegral minimum_instruction_length
        let initial_state = defaultLNE default_is_stmt fnames
            line_matrix = stepLineMachine default_is_stmt minimum_instruction_length initial_state line_program
         in pure (map (\(name, _, _, _) -> name) fnames, line_matrix)
