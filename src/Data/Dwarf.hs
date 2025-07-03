{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TupleSections #-}

-- | Parses the DWARF 2-5 specifications at http://www.dwarfstd.org given
-- the debug sections in ByteString form.
module Data.Dwarf
  ( -- * Encoding and target information
    Encoding (..),
    Endianess (..),
    TargetSize (..),

    -- * Parsing
    Sections (..),
    mkSections,
    CUContext,
    cuReader,
    cuSections,
    firstCUContext,
    cuFirstDie,
    nextCUContext,
    parseInfo,

    -- * Debug information entries
    DieID (..),
    dieID,
    DIE (..),
    (!?),
    DIERefs (..),
    DIEMap,

    -- * Reading utilities
    Reader (..),
    reader,
    drEndianess,
    drEncoding,
    desrGetOffset,

    -- * .debug_aranges
    CUOffset (..),
    parseAranges,

    -- * .debug_pubnames
    parsePubnames,

    -- * .debug_pubtypes
    parsePubtypes,

    -- * Call frames information
    module Data.Dwarf.Frame,

    -- * Unclassified
    Range (..),
    parseRanges,
    parseLoc,
    RangeEnd (..),
    Data.Dwarf.CFA.DW_CFA (..),
    Data.Dwarf.CFA.CallFrameAddr,
    Data.Dwarf.CFA.CallFrameExpr,
    Data.Dwarf.CFA.CallFrameReg,
    Data.Dwarf.CFA.CallFramePPCtx (..),
    Data.Dwarf.CFA.ppCFA,
    Data.Dwarf.CFA.parseCallFrameInstructions,
    Data.Dwarf.CFA.ppX86CallFrameReg,
    DW_MACINFO (..),
    parseMacInfo,
    DW_OP (..),
    parseDW_OP,
    parseDW_OPs,
    module Data.Dwarf.AT,
    module Data.Dwarf.ATE,
    module Data.Dwarf.TAG,
    module Data.Dwarf.Types,
    DW_LNE (..),
    parseLNE,
    getLNE,
  )
where

import Control.Monad (forM)
import Data.Binary (Get)
import Data.Binary.Get (getWord8)
import qualified Data.Binary.Get as Get
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as L
import Data.Dwarf.AT
import Data.Dwarf.ATE
import Data.Dwarf.CFA
import Data.Dwarf.Form
import Data.Dwarf.Frame
import Data.Dwarf.Internals
import Data.Dwarf.LNI
import Data.Dwarf.OP
import Data.Dwarf.Reader
import Data.Dwarf.TAG
import Data.Dwarf.Types
import qualified Data.Map.Strict as M
import Data.Word (Word64)

-- | The offset of a compile unit in a file from
-- the start of the file.
newtype CUOffset = CUOffset Word64
  deriving (Eq, Ord, Read, Show)

-- Don't export a constructor, so users can only read DieID's, not
-- create fake ones, which is slightly safer.
dieID :: DieID -> Word64
dieID (DieID x) = x

inCU :: Integral a => CUOffset -> a -> DieID
inCU (CUOffset base) x = DieID (base + fromIntegral x)

-- | Sections to retrieve dwarf information.
data Sections = Sections
  { -- | @.debug_info@ contents
    dsInfoSection :: B.ByteString,
    -- | @.debug_abbrev@ contents
    dsAbbrevSection :: B.ByteString,
    -- | @.debug_aranges@ contents
    dsArangesSection :: !B.ByteString,
    -- | @.debug_line@ contents
    dsLineSection :: !B.ByteString,
    -- | @.debug_loc@ contents
    dsLocSection :: !B.ByteString,
    -- | @.debug_ranges@ contents
    dsRangesSection :: !B.ByteString,
    -- | @.debug_str@ contents
    dsStrSection :: B.ByteString
  }

-- | Create dwarf buffers from function that looks up section names.
mkSections ::
  Applicative m =>
  -- | Function that looks up contents given section name.
  (B.ByteString -> m B.ByteString) ->
  m Sections
mkSections f =
  let mk info aranges abbrev lne loc ranges str =
        Sections
          { dsInfoSection = info,
            dsArangesSection = aranges,
            dsAbbrevSection = abbrev,
            dsLineSection = lne,
            dsLocSection = loc,
            dsRangesSection = ranges,
            dsStrSection = str
          }
   in mk <$> f ".debug_info"
        <*> f ".debug_aranges"
        <*> f ".debug_abbrev"
        <*> f ".debug_line"
        <*> f ".debug_loc"
        <*> f ".debug_ranges"
        <*> f ".debug_str"

newtype DIEOffset = DIEOffset Word64
-- ^ Offset in .debug_info of DIE relative from start of bufer.

data CUContext = CUContext
  { -- | Offset in .debug_info section of compile unit
    cuOffset :: !CUOffset,
    cuAbbrevMap :: !(M.Map AbbrevId DW_ABBREV),
    cuSize :: !Word64,
    cuReader :: !Reader,
    cuSections :: !Sections,
    cuDieOffset :: !DIEOffset,
    cuNextOffset :: !CUOffset,
    cuNextAbbrevCache :: !(M.Map Word64 (M.Map AbbrevId DW_ABBREV))
  }

---------------------------------------------------------------------------------------------------------------------------------------------------------------
-- Abbreviation and form parsing
---------------------------------------------------------------------------------------------------------------------------------------------------------------
newtype AbbrevId = AbbrevId Word64
  deriving (Eq, Ord, Read, Show)

data DW_ABBREV = DW_ABBREV
  { abbrevId :: AbbrevId,
    abbrevTag :: DW_TAG,
    abbrevChildren :: Bool,
    abbrevAttrForms :: [(DW_AT, DW_FORM)]
  }

getAttrFormList' :: [(DW_AT, DW_FORM)] -> Get [(DW_AT, DW_FORM)]
getAttrFormList' prev = do
  at <- getULEB128
  f <- getULEB128
  if (at, f) == (0, 0)
    then pure (reverse prev)
    else getAttrFormList' ((DW_AT at, DW_FORM f) : prev)

getAbbrevList' :: M.Map AbbrevId DW_ABBREV -> Get (M.Map AbbrevId DW_ABBREV)
getAbbrevList' m = do
  abbrevI <- getULEB128
  if abbrevI == 0
    then pure $! m
    else do
      tag <- getDW_TAG
      children <- getWord8
      attrForms <- getAttrFormList' []
      let a =
            DW_ABBREV
              { abbrevId = AbbrevId abbrevI,
                abbrevTag = tag,
                abbrevChildren = children == 1,
                abbrevAttrForms = attrForms
              }
      getAbbrevList' $! M.insert (AbbrevId abbrevI) a m

getAbbrevMap :: Word64 -> B.ByteString -> Either String (M.Map AbbrevId DW_ABBREV)
getAbbrevMap off s = do
  let bsl = L.fromChunks [B.drop (fromIntegral off) s]
  case Get.runGetOrFail (getAbbrevList' M.empty) bsl of
    Left (_, _, e) -> Left e
    Right (_, _, r) -> Right r

---------------------------------------------------------------------------------------------------------------------------------------------------------------
-- DWARF information entry and .debug_info section parsing.
---------------------------------------------------------------------------------------------------------------------------------------------------------------

-- | Utility function for retrieving the list of values for a
-- specified attribute from a DWARF information entry.
(!?) :: DIE -> DW_AT -> [DW_ATVAL]
(!?) die at = map snd $ filter ((== at) . fst) $ dieAttributes die

getNonZeroOffset :: Endianess -> Encoding -> Get (Maybe Word64)
getNonZeroOffset end enc = do
  offset <- desrGetOffset end enc
  pure $ if offset == 0 then Nothing else Just offset

-- Section 7.19 - Name Lookup Tables
getNameLookupEntries :: Endianess -> Encoding -> CUOffset -> Get [(B.ByteString, [DieID])]
getNameLookupEntries end enc off = do
  whileJust $ traverse getEntry =<< getNonZeroOffset end enc
  where
    getEntry dieOffset = do
      name <- getByteStringNul
      pure (name, [inCU off dieOffset])

-- The headers for "Section 7.19 Name Lookup Table", and "Section 7.20
-- Address Range Table" are very similar, this is the common format:
getTableHeader :: Endianess -> Get (Encoding, CUOffset)
getTableHeader endianess = do
  (enc, _) <- getDwarfSize endianess
  _version <- derGetW16 endianess
  cuOff <- desrGetOffset endianess enc
  return (enc, CUOffset cuOff)

getNameLookupTable :: Endianess -> Get [M.Map B.ByteString [DieID]]
getNameLookupTable endianess = getWhileNotEmpty $ do
  (enc, cu_offset) <- getTableHeader endianess
  _debug_info_length <- desrGetOffset endianess enc
  M.fromListWith (++) <$> getNameLookupEntries endianess enc cu_offset

parsePubSection :: Endianess -> B.ByteString -> M.Map B.ByteString [DieID]
parsePubSection endianess section =
  M.unionsWith (++) $ strictGet (getNameLookupTable endianess) section

-- | Parses the .debug_pubnames section (as ByteString) into a map from a value name to a DieID
parsePubnames :: Endianess -> B.ByteString -> M.Map B.ByteString [DieID]
parsePubnames = parsePubSection

-- | Parses the .debug_pubtypes section (as ByteString) into a map from a type name to a DieID
parsePubtypes :: Endianess -> B.ByteString -> M.Map B.ByteString [DieID]
parsePubtypes = parsePubSection

align :: Integral a => a -> Get ()
align alignment = do
  pos <- Get.bytesRead
  Get.skip . fromIntegral $ (- pos) `mod` fromIntegral alignment

data Range = Range
  { rangeBegin :: !Word64,
    rangeEnd :: !Word64
  }
  deriving (Eq, Ord, Read, Show)

-- Section 7.20 - Address Range Table
-- Returns the ranges that belong to a CU
getAddressRangeTable :: Endianess -> Get [([Range], CUOffset)]
getAddressRangeTable endianess = getWhileNotEmpty $ do
  (_enc, cu_offset) <- getTableHeader endianess
  address_size <- getWord8
  let readAddress =
        case address_size of
          4 -> fromIntegral <$> derGetW32 endianess
          8 -> derGetW64 endianess
          n -> fail $ "Unrecognized address size " ++ show n ++ " in .debug_aranges section."
  _segment_size <- getWord8
  align $ 2 * address_size
  address_ranges <- whileM (/= Range 0 0) $ Range <$> readAddress <*> readAddress
  pure (address_ranges, cu_offset)

-- | Parses the .debug_aranges section (as ByteString) into a map from
-- an address range to a DieID that indexes the Info.
parseAranges :: Endianess -> B.ByteString -> [([Range], CUOffset)]
parseAranges endianess aranges_section =
  strictGet (getAddressRangeTable endianess) aranges_section

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}

-- Section 7.21 - Macro Information
data DW_MACINFO
  = -- | Line number and defined symbol with definition
    DW_MACINFO_define !Word64 !B.ByteString
  | -- | Line number and undefined symbol
    DW_MACINFO_undef !Word64 !B.ByteString
  | -- | Marks start of file with the line where the file was
    -- included from and a source file index
    DW_MACINFO_start_file Word64 Word64
  | -- | Marks end of file
    DW_MACINFO_end_file
  | -- | Implementation defined
    DW_MACINFO_vendor_ext Word64 !B.ByteString
  deriving (Eq, Ord, Read, Show)

-- | Retrieves the macro information for a compilation unit from a given substring of the .debug_macinfo section. The offset
-- into the .debug_macinfo section is obtained from the DW_AT_macro_info attribute of a compilation unit DIE.
parseMacInfo :: B.ByteString -> [DW_MACINFO]
parseMacInfo = strictGet getMacInfo

getMacInfo :: Get [DW_MACINFO]
getMacInfo = go []
  where
    go prev = do
      x <- getWord8
      case x of
        0x00 -> pure (reverse prev)
        0x01 -> do
          mi <- DW_MACINFO_define <$> getULEB128 <*> getByteStringNul
          go (mi : prev)
        0x02 -> do
          mi <- DW_MACINFO_undef <$> getULEB128 <*> getByteStringNul
          go (mi : prev)
        0x03 -> do
          mi <- DW_MACINFO_start_file <$> getULEB128 <*> getULEB128
          go (mi : prev)
        0x04 -> do
          go (DW_MACINFO_end_file : prev)
        0xff -> do
          mi <- DW_MACINFO_vendor_ext <$> getULEB128 <*> getByteStringNul
          go (mi : prev)
        _ -> fail $ "Invalid MACINFO id: " ++ show x

newtype RangeEnd = RangeEnd Word64
  deriving (Show)

-- Section 7.23 - Non-contiguous Address Ranges

-- | Retrieves the non-contiguous address ranges for a compilation unit from a given substring of the .debug_ranges section. The offset
-- into the .debug_ranges section is obtained from the DW_AT_ranges attribute of a compilation unit DIE.
-- Left results are base address entries. Right results are address ranges.
parseRanges :: Reader -> B.ByteString -> [Either RangeEnd Range]
parseRanges = strictGet . getRanges

getMRange :: Endianess -> TargetSize -> Get (Maybe (Either RangeEnd Range))
getMRange endian tgt = do
  begin <- getTargetAddress endian tgt
  end <- getTargetAddress endian tgt
  pure $
    if begin == 0 && end == 0
      then Nothing
      else
        Just $
          if begin == largestTargetAddress tgt
            then Left $ RangeEnd end
            else Right $ Range begin end

getRanges :: Reader -> Get [Either RangeEnd Range]
getRanges dr = whileJust $ getMRange (drEndianess dr) (drTarget64 dr)

-- Section 7.7.3

-- | Retrieves the location list expressions from a given substring of the .debug_loc section. The offset
-- into the .debug_loc section is obtained from an attribute of class loclistptr for a given DIE.
-- Left results are base address entries. Right results are address ranges and a location expression.
parseLoc :: Reader -> B.ByteString -> [Either RangeEnd (Range, B.ByteString)]
parseLoc dr = strictGet (getLoc (drEndianess dr) (drTarget64 dr))

getLoc :: Endianess -> TargetSize -> Get [Either RangeEnd (Range, B.ByteString)]
getLoc endian tgt = whileJust $ traverse mkRange =<< getMRange endian tgt
  where
    mkRange (Left end) = pure $ Left end
    mkRange (Right range) =
      Right . (,) range <$> getByteStringLen (derGetW16 endian)

data DIERefs = DIERefs
  { -- | Unique identifier of this entry's parent.
    dieRefsParent :: Maybe DieID,
    -- | Unique identifier of the left sibling
    dieRefsSiblingLeft :: Maybe DieID,
    -- | Unique identifier of the right sibling
    dieRefsSiblingRight :: Maybe DieID,
    dieRefsDIE :: DIE
  }
  deriving (Show)

type DIEMap = M.Map DieID DIERefs

-- | The dwarf information entries form a graph of nodes tagged with attributes. Please refer to the DWARF specification
-- for semantics. Although it looks like a tree, there can be attributes which have adjacency information which will
-- introduce cross-branch edges.
data DIE = DIE
  { -- | Unique identifier for this entry.
    dieId :: DieID,
    -- | Type tag.
    dieTag :: DW_TAG,
    -- | Attribute tag and value pairs.
    dieAttributes :: [(DW_AT, DW_ATVAL)],
    dieChildren :: [DIE],
    -- | Decoder used to decode this entry. May be needed to further parse attribute values.
    dieReader :: Reader
  }

instance Show DIE where
  show (DIE (DieID i) tag attrs children _) =
    concat $
      ["DIE@", show i, "{", show tag, " (", show (length children), " children)"]
        ++ concat
          [ [" ", show attr, "=(", show val, ")"]
            | (attr, val) <- attrs
          ]
        ++ ["}"]

-- Decode a non-compilation unit DWARF information entry, its children and its siblings.
getDieAndSiblings :: CUContext -> Get [DIE]
getDieAndSiblings cuContext = do
  whileJust $ do
    let DIEOffset off = cuDieOffset cuContext
    br <- Get.bytesRead
    getDIEAndDescendants cuContext (DieID (off + fromIntegral br))

unimplForm :: DW_FORM -> Get a
unimplForm f = fail $ "Unimplemented attribute parser: " ++ show f

getForm :: CUContext -> DW_FORM -> Get DW_ATVAL
getForm cuContext form = do
  let dr = cuReader cuContext
  let cu = cuOffset cuContext
  let dc = cuSections cuContext
  let end = drEndianess dr
      enc = drEncoding dr
      tgt = drTarget64 dr
  case form of
    DW_FORM_addr -> DW_ATVAL_UINT . fromIntegral <$> getTargetAddress end tgt
    DW_FORM_block2 -> DW_ATVAL_BLOB <$> getByteStringLen (derGetW16 end)
    DW_FORM_block4 -> DW_ATVAL_BLOB <$> getByteStringLen (derGetW32 end)
    DW_FORM_data2 -> DW_ATVAL_UINT . fromIntegral <$> derGetW16 end
    DW_FORM_data4 -> DW_ATVAL_UINT . fromIntegral <$> derGetW32 end
    DW_FORM_data8 -> DW_ATVAL_UINT . fromIntegral <$> derGetW64 end
    DW_FORM_string -> DW_ATVAL_STRING <$> getByteStringNul
    DW_FORM_block -> DW_ATVAL_BLOB <$> getByteStringLen getULEB128
    DW_FORM_block1 -> DW_ATVAL_BLOB <$> getByteStringLen getWord8
    DW_FORM_data1 -> DW_ATVAL_UINT . fromIntegral <$> getWord8
    DW_FORM_flag -> DW_ATVAL_BOOL . (/= 0) <$> getWord8
    DW_FORM_sdata -> DW_ATVAL_INT <$> getSLEB128
    DW_FORM_strp -> do
      offset <- desrGetOffset end (drEncoding dr)
      let str = B.drop (fromIntegral offset) (dsStrSection dc)
      pure $! DW_ATVAL_STRING (B.takeWhile (/= 0) str)
    DW_FORM_udata -> DW_ATVAL_UINT <$> getULEB128
    DW_FORM_ref_addr -> DW_ATVAL_UINT <$> desrGetOffset end enc
    DW_FORM_ref1 -> DW_ATVAL_REF . inCU cu <$> getWord8
    DW_FORM_ref2 -> DW_ATVAL_REF . inCU cu <$> derGetW16 end
    DW_FORM_ref4 -> DW_ATVAL_REF . inCU cu <$> derGetW32 end
    DW_FORM_ref8 -> DW_ATVAL_REF . inCU cu <$> derGetW64 end
    DW_FORM_ref_udata -> DW_ATVAL_REF . inCU cu <$> getULEB128
    DW_FORM_indirect -> getForm cuContext . DW_FORM =<< getULEB128
    -- new in Dwarf version 4
    DW_FORM_sec_offset -> DW_ATVAL_UINT <$> desrGetOffset end enc
    DW_FORM_exprloc -> DW_ATVAL_BLOB <$> getByteStringLen getULEB128
    DW_FORM_flag_present -> pure $ DW_ATVAL_BOOL True
    DW_FORM_ref_sig8 -> DW_ATVAL_UINT . fromIntegral <$> derGetW64 end
    DW_FORM_strx -> unimplForm form
    DW_FORM_addrx -> unimplForm form
    DW_FORM_ref_sup4 -> unimplForm form
    DW_FORM_strp_sup -> unimplForm form
    DW_FORM_data16 -> unimplForm form
    DW_FORM_line_strp -> unimplForm form
    DW_FORM_implicit_const -> unimplForm form
    DW_FORM_loclistx -> unimplForm form
    DW_FORM_rnglistx -> undefined
    DW_FORM_ref_sup8 -> undefined
    DW_FORM_strx1 -> unimplForm form
    DW_FORM_strx2 -> unimplForm form
    DW_FORM_strx3 -> unimplForm form
    DW_FORM_strx4 -> unimplForm form
    DW_FORM_addrx1 -> unimplForm form
    DW_FORM_addrx2 -> unimplForm form
    DW_FORM_addrx3 -> unimplForm form
    DW_FORM_addrx4 -> unimplForm form
    _ -> unimplForm form

getDIEAndDescendants :: CUContext -> DieID -> Get (Maybe DIE)
getDIEAndDescendants cuContext thisId = do
  abbrid <- getULEB128
  if abbrid == 0
    then pure Nothing
    else do
      let abbrev = cuAbbrevMap cuContext M.! AbbrevId abbrid
          tag = abbrevTag abbrev
      values <-
        forM (abbrevAttrForms abbrev) $ \(attr, form) -> do
          (attr,) <$> getForm cuContext form
      children <-
        if abbrevChildren abbrev
          then getDieAndSiblings cuContext
          else pure []
      pure $
        Just $
          DIE
            { dieId = thisId,
              dieTag = tag,
              dieAttributes = values,
              dieChildren = children,
              dieReader = cuReader cuContext
            }

getCUHeader ::
  (Endianess, Sections) ->
  -- | Map from previously seen .debug_abbrev offset to map.
  M.Map Word64 (M.Map AbbrevId DW_ABBREV) ->
  -- | Offset of this entry
  CUOffset ->
  Get CUContext
getCUHeader (endian, dwarfSections) abbrevMapCache (CUOffset cuOff) = do
  start <- Get.bytesRead
  (enc, unitLength) <- getDwarfSize endian
  postLength <- Get.bytesRead
  let totalLength = fromIntegral (postLength - start) + unitLength
  _version <- derGetW16 endian
  abbrevOffset <- desrGetOffset endian enc
  addr_size <- getWord8
  postHeader <- Get.bytesRead
  tgt <- case addr_size of
    4 -> pure TargetSize32
    8 -> pure TargetSize64
    _ -> fail $ "Invalid address size: " ++ show addr_size
  (abbrevMap, nextAbbrevMapCache) <-
    case M.lookup abbrevOffset abbrevMapCache of
      Just r -> pure (r, abbrevMapCache)
      Nothing ->
        case getAbbrevMap abbrevOffset (dsAbbrevSection dwarfSections) of
          Left e -> fail e
          Right m -> pure (m, M.insert abbrevOffset m abbrevMapCache)
  let ctx =
        CUContext
          { cuReader = reader endian enc tgt,
            cuAbbrevMap = abbrevMap,
            cuOffset = CUOffset cuOff,
            cuSize = totalLength,
            cuSections = dwarfSections,
            cuDieOffset = DIEOffset (cuOff + fromIntegral (postHeader - start)),
            cuNextOffset = CUOffset (cuOff + totalLength),
            cuNextAbbrevCache = nextAbbrevMapCache
          }
  pure $! ctx

getCUContext ::
  Endianess ->
  Sections ->
  M.Map Word64 (M.Map AbbrevId DW_ABBREV) ->
  CUOffset ->
  Maybe (Either String CUContext)
getCUContext end s m (CUOffset off) = do
  let bs = B.drop (fromIntegral off) (dsInfoSection s)
  if B.null bs
    then Nothing
    else case Get.runGetOrFail (getCUHeader (end, s) m (CUOffset off)) (L.fromChunks [bs]) of
      Left (_, _, msg) -> Just (Left msg)
      Right (_, _, cu) -> Just (Right cu)

dieAndDescendants ::
  CUContext ->
  DIEOffset ->
  Either String (Maybe DIE)
dieAndDescendants ctx (DIEOffset off) = do
  let sec = dsInfoSection (cuSections ctx)

  let bs = L.fromChunks [B.drop (fromIntegral off) sec]
  let thisID = DieID off
  case Get.runGetOrFail (getDIEAndDescendants ctx thisID) bs of
    Left (_, _, msg) -> Left msg
    Right (_, _, v) -> Right v

-- | Get first DIE for context
cuFirstDie :: CUContext -> Either String DIE
cuFirstDie cu =
  case dieAndDescendants cu (cuDieOffset cu) of
    Left e -> Left e
    Right Nothing -> Left "Compilation unit lacks a DIE"
    Right (Just d) -> Right d

-- | Get next compile unit
nextCUContext :: CUContext -> Maybe (Either String CUContext)
nextCUContext cu =
  let end = desrEndianess (drDesr (cuReader cu))
   in getCUContext end (cuSections cu) (cuNextAbbrevCache cu) (cuNextOffset cu)

-- | Get first compile unit in .debug_info
firstCUContext :: Endianess -> Sections -> Maybe (Either String CUContext)
firstCUContext end sec = getCUContext end sec M.empty (CUOffset 0)

-- Decode the compilation unit DWARF information entries.
getDieCus ::
  [(CUContext, DIE)] ->
  Maybe (Either String CUContext) ->
  [(CUContext, DIE)]
getDieCus prev Nothing = reverse prev
getDieCus _prev (Just (Left e)) = error e
getDieCus prev (Just (Right cu)) =
  case cuFirstDie cu of
    Left e -> error e
    Right d -> getDieCus ((cu, d) : prev) (nextCUContext cu)

{-# DEPRECATED parseInfo "Use firstCompileUnit, cuFirstDie and cuNextCompileUnit" #-}

-- | Parses the .debug_info section (as ByteString) using the .debug_abbrev and .debug_str sections.
parseInfo ::
  Endianess ->
  Sections ->
  -- | The die list is of compilation unit dies
  [(CUContext, DIE)]
parseInfo end sec = getDieCus [] (firstCUContext end sec)
