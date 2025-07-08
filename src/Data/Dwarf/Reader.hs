module Data.Dwarf.Reader
  ( Reader
  , reader
  , EndianSizeReader
  , drDesr
  , desrEndianess
  , drEncoding
  , Endianess(..)
  , Encoding(..)
  , encodingByteSize
  , TargetSize(..)
  , largestTargetAddress
  , targetPtrByteSize
  , getDwarfSize
  , sizeHeaderByteCount
  , desrGetOffset
  , getTargetAddress
  , derGetW16
  , derGetW32
  , derGetW24
  , derGetW64
  , derGetI16
  , derGetI32
  , derGetI64
  , drEndianess
  , drTarget64
  ) where

import           Data.Binary.Get  ( Get
  , getWord16be, getWord32be, getWord64be
  , getWord16le, getWord32le, getWord64le
  )

import           qualified Data.Binary.Get.Internal as GI

import           Data.Int (Int16, Int32, Int64)
import           qualified Data.ByteString as B
import           qualified Data.ByteString.Unsafe as B
import           qualified Data.Bits as Bits

import           Data.Word (Word16, Word32, Word64)
import Debug.Trace (trace)

-- TODO: Use a type with 24 bits
word24le :: B.ByteString -> Word32
word24le s = fromIntegral (s `B.unsafeIndex` 0) Bits..|. (fromIntegral (s `B.unsafeIndex` 1) `Bits.unsafeShiftL` 8) Bits..|. (fromIntegral (s `B.unsafeIndex` 2) `Bits.unsafeShiftL` 16)

word24be :: B.ByteString -> Word32
word24be s = fromIntegral (s `B.unsafeIndex` 2) Bits..|. (fromIntegral (s `B.unsafeIndex` 1) `Bits.unsafeShiftL` 1) Bits..|. (fromIntegral (s `B.unsafeIndex` 0) `Bits.unsafeShiftL` 16)

getWord24be :: Get Word32
getWord24be = GI.readN 3 word24be

getWord24le :: Get Word32
getWord24le = GI.readN 3 word24le


-- | Ordering bytes are encoded in buffers.
data Endianess = LittleEndian | BigEndian
  deriving (Eq, Ord, Read, Show)

-- | Encoding of buffers
data Encoding = Encoding32 | Encoding64
  deriving (Eq, Ord, Read, Show)

-- | Width of pointers in target.
data TargetSize = TargetSize32 | TargetSize64
  deriving (Eq, Ord, Read, Show)

targetPtrByteSize :: TargetSize -> Word64
targetPtrByteSize TargetSize64 = 8
targetPtrByteSize TargetSize32 = 4

derGetW16 :: Endianess -> Get Word16
derGetW16 end =
  case end of
    LittleEndian -> getWord16le
    BigEndian    -> getWord16be

derGetW32 :: Endianess -> Get Word32
derGetW32 end =
  case end of
    LittleEndian -> getWord32le
    BigEndian    -> getWord32be

derGetW64 :: Endianess -> Get Word64
derGetW64 end =
  case end of
    LittleEndian -> getWord64le
    BigEndian    -> getWord64be


derGetW24 :: Endianess -> Get Word32
derGetW24 end =
  case end of
    LittleEndian -> getWord24le
    BigEndian    -> getWord24be


derGetI16 :: Endianess -> Get Int16
derGetI16 end = fromIntegral <$> derGetW16 end

derGetI32 :: Endianess -> Get Int32
derGetI32 end = fromIntegral <$> derGetW32 end

derGetI64 :: Endianess -> Get Int64
derGetI64 end = fromIntegral <$> derGetW32 end

-- Intermediate data structure for a partial Reader.
data EndianSizeReader = EndianSizeReader
  { desrEndianess  :: !Endianess
  , desrEncoding :: !Encoding
  }


encodingByteSize :: Encoding -> Word64
encodingByteSize Encoding64 = 8
encodingByteSize Encoding32 = 4

desrGetOffset :: Endianess -> Encoding -> Get Word64
desrGetOffset endianess enc =
  case enc of
    Encoding64 -> derGetW64 endianess
    Encoding32 -> fromIntegral <$> derGetW32 endianess

instance Show EndianSizeReader where
    show desr = "EndianSizeReader " ++ show (desrEndianess desr) ++ " " ++ show (desrEncoding desr)

-- | Type containing functions and data needed for decoding DWARF information.
data Reader = Reader
    { drDesr                  :: !EndianSizeReader
    , drTarget64              :: !TargetSize
    }

instance Show Reader where
    show dr = "Reader " ++ show (drDesr dr) ++ " " ++ show (drTarget64 dr)

reader :: Endianess -> Encoding -> TargetSize -> Reader
reader endianess enc tgt =
  let esr = EndianSizeReader { desrEndianess = endianess
                             , desrEncoding = enc
                             }
   in Reader { drDesr = esr
             , drTarget64 = tgt
             }

-- | Largest permissible target address.
largestTargetAddress :: TargetSize -> Word64
largestTargetAddress tgt =
  case tgt of
    TargetSize64 -> 0xffffffffffffffff
    TargetSize32 -> 0xffffffff

-- | Action for reading a pointer for the target machine.
getTargetAddress :: Endianess -> TargetSize -> Get Word64
getTargetAddress end tgt =
  trace "Getting target address" (case tgt of
    TargetSize64 -> derGetW64 end
    TargetSize32 -> fromIntegral <$> derGetW32 end)

drEndianess :: Reader -> Endianess
drEndianess = desrEndianess . drDesr

drEncoding :: Reader -> Encoding
drEncoding = desrEncoding . drDesr

-- | Return the number of bytes in a DWARF size header with the given encoding.
--
-- See @getDwarfSize@ to read a size header.
sizeHeaderByteCount  :: Encoding -> Int
sizeHeaderByteCount Encoding32 =  4
sizeHeaderByteCount Encoding64 = 12

-- | Decode the DWARF size header entry, which specifies the encoding
-- and the size of a DWARF subsection.
--
-- See @sizeHeaderByteCount@ to get the size of an encoding.
getDwarfSize :: Endianess -> Get (Encoding, Word64)
getDwarfSize endianess = do
  size <- derGetW32 endianess
  if size == 0xffffffff then do
    size64 <- derGetW64 endianess
    pure (Encoding64, size64)
   else if size < 0xffffff00 then do
    pure (Encoding32, fromIntegral size)
   else
    fail $ "Invalid DWARF size: " ++ show size
