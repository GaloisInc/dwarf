{-# LANGUAGE OverloadedStrings #-}

module Data.Dwarf.Internals
  ( getSLEB128
  , getULEB128
  , getByteStringLen
  , tryGetUntilDone
  , tryStrictGet
  , whileM
  , getByteStringNul
  , whileJust
  , strictGet
  , getWhileNotEmpty
  , Sections(SectionContents)
  , requiredSection
  , dsStrSection,
  dsAbbrevSection,
  dsInfoSection,
  dsRangesSection,
  dsLineSection,
  dsLineStrSection,
  dsStrOffsets,
  dsAddr
  ) where

import           Data.Binary.Get (getByteString, getWord8, Get, runGet)
import qualified Data.Binary.Get as Get
import           Data.Bits ((.|.), shiftL, clearBit, testBit)
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as L
import           Data.Int (Int64)
import           Data.Word (Word64)


-- | Sections to retrieve dwarf information from, maps section names to 'B.ByteString'
newtype Sections = SectionContents (B.ByteString -> Maybe B.ByteString)


-- | Fails if a section is not present in the mapping
requiredSection :: (MonadFail m) => B.ByteString -> Sections -> m B.ByteString
requiredSection nm (SectionContents sections) =
  maybe (fail $ "Required section: " ++  show nm) pure (sections nm)

-- | The DWARF string section (a section populated by null terminated strings)
dsStrSection :: (MonadFail m) => Sections -> m B.ByteString
dsStrSection = requiredSection ".debug_str"

-- | The DWARF abbrev table describing attributes and tags
dsAbbrevSection :: (MonadFail m) => Sections -> m B.ByteString
dsAbbrevSection = requiredSection ".debug_abbrev"

-- | The core DWARF info section containing DIEs
dsInfoSection :: (MonadFail m) => Sections -> m B.ByteString
dsInfoSection = requiredSection ".debug_info"

-- | The DWARF line program section containing the line program and its header
dsLineSection :: (MonadFail m) => Sections -> m B.ByteString
dsLineSection = requiredSection ".debug_line"

-- | Another DWARF string section like debug_str except for the line program
dsLineStrSection :: (MonadFail m) => Sections -> m B.ByteString
dsLineStrSection = requiredSection ".debug_line_str"

-- | Section containing the range list
dsRangesSection :: (MonadFail m) => Sections -> m B.ByteString
dsRangesSection = requiredSection ".debug_ranges"

-- | An array of offsets into the string stable for strx operations.
dsStrOffsets :: (MonadFail m) => Sections -> m B.ByteString
dsStrOffsets = requiredSection ".debug_str_offsets"

-- | An array of addresses accessed by addrx operations.
dsAddr :: (MonadFail m) => Sections -> m B.ByteString
dsAddr = requiredSection ".debug_addr"


whileJust :: (Applicative m, Monad m) => m (Maybe a) -> m [a]
whileJust act =
  let go p = do
        res <- act
        case res of
          Nothing -> pure (reverse p)
          Just x -> go (x:p)
   in go []

-- Repeatedly perform the get operation until the boolean fails.
whileM :: (Applicative m, Monad m) => (a -> Bool) -> m a -> m [a]
whileM cond act =
  let go p = do
        x <- act
        case cond x of
          False -> pure (reverse p)
          True ->  go (x:p)
   in go []

getWhileNotEmpty :: Get a -> Get [a]
getWhileNotEmpty act =
  let go p = do
        e <- Get.isEmpty
        case e of
          True -> pure (reverse p)
          False -> act >>= \x -> go (x:p)
   in go []

getByteStringLen :: Integral a => Get a -> Get B.ByteString
getByteStringLen lenGetter = getByteString =<< fromIntegral <$> lenGetter

getByteStringNul :: Get B.ByteString
getByteStringNul = L.toStrict <$> Get.getLazyByteStringNul

-- | Decode a signed little-endian base 128 encoded integer.
getSLEB128 :: Get Int64
getSLEB128 = go 0 0
  where go :: Word64 -> Int -> Get Int64
        go acc bitCount = do
          byte <- fromIntegral <$> getWord8 :: Get Word64
          let temp = (clearBit byte 7 `shiftL` bitCount) .|. acc
          if testBit byte 7 then
            go temp (bitCount + 7)
           -- If last byte is negative
           else if testBit byte 6 then
            pure $ fromIntegral $ temp .|. (maxBound `shiftL` (bitCount + 7))
           else
            pure $ fromIntegral temp

-- Decode an unsigned little-endian base 128 encoded integer.
getULEB128 :: Get Word64
getULEB128 =
    let go acc shift = do
        byte <- fromIntegral <$> getWord8 :: Get Word64
        let temp = acc .|. (clearBit byte 7 `shiftL` shift)
        if testBit byte 7 then
            go temp (shift + 7)
         else
            pure temp
    in go 0 0

strictGet :: Get a -> B.ByteString -> a
strictGet action bs = runGet action $ L.fromChunks [bs]

-- | Run get action and return either offset error message pair or
-- remaining bytes, offset and result.
tryStrictGet :: Get a
             -> B.ByteString
             -> Either (Int64, String) (B.ByteString, Int64, a)
tryStrictGet m bs =
  case Get.pushEndOfInput (Get.pushChunk (Get.runGetIncremental m) bs) of
    Get.Fail _rest off msg -> Left (off, msg)
    Get.Partial _cont -> error $ "internal error: Get partial failed."
    Get.Done rest off r -> Right (rest, off, r)

-- | Run a parse until we reach the end of a byte string.
tryGetUntilDone
  :: Get a
  -> B.ByteString
  -> Either ([a], Int64, String) [a]
tryGetUntilDone = go [] 0
  where go :: [a]
           -> Int64
           -> Get a
           -> B.ByteString
           -> Either ([a], Int64, String) [a]
        go prev off m bs =
          if B.null bs then
            Right (reverse prev)
           else
            case Get.pushEndOfInput (Get.pushChunk (Get.runGetIncremental m) bs) of
              Get.Fail _rest _ msg -> Left (reverse prev, off, msg)
              Get.Partial _cont -> error $ "internal error: Get partial failed."
              Get.Done bs' o r ->
                let nextPrev = seq r (r : prev)
                    nextOff  = off + o
                 in seq nextPrev $ seq nextOff $ seq bs' $ go nextPrev nextOff m bs'
