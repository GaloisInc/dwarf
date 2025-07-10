{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -fno-warn-missing-pattern-synonym-signatures #-}
-- We currently disable -Wmissing-signatures as a way to avoid warnings on
-- GHC 9.2, which emits -Wmissing-signatures warnings related to pattern
-- synonyms even if -Wmissing-pattern-synonym-signatures is disabled. See
-- https://gitlab.haskell.org/ghc/ghc/-/issues/14794#note_424553. If that
-- issue is resolved in a subsequent minor release of GHC 9.2, we can remove
-- this workaround.
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
module Data.Dwarf.Form where

import           Control.Monad (replicateM)
import           Data.Binary.Get
import           Data.Dwarf.AT
import           Data.Dwarf.Internals
import           Data.Dwarf.Reader
import           Data.Word (Word64)
import           Numeric (showHex)
import qualified Data.ByteString as B
import qualified Data.Map.Strict as Map

newtype DW_FORM = DW_FORM Word64
  deriving (Eq,Ord)


pattern DW_FORM_addr = DW_FORM 0x01
pattern DW_FORM_block2 = DW_FORM 0x03
pattern DW_FORM_block4 = DW_FORM 0x04
pattern DW_FORM_data2 = DW_FORM 0x05
pattern DW_FORM_data4 = DW_FORM 0x06
pattern DW_FORM_data8 = DW_FORM 0x07
pattern DW_FORM_string = DW_FORM 0x08

pattern DW_FORM_block = DW_FORM 0x09
pattern DW_FORM_block1 = DW_FORM 0x0a
pattern DW_FORM_data1 = DW_FORM 0x0b
pattern DW_FORM_flag = DW_FORM 0x0c
pattern DW_FORM_sdata = DW_FORM 0x0d
pattern DW_FORM_strp = DW_FORM 0x0e
pattern DW_FORM_udata = DW_FORM 0x0f
pattern DW_FORM_ref_addr = DW_FORM 0x10

pattern DW_FORM_ref1 = DW_FORM 0x11
pattern DW_FORM_ref2 = DW_FORM 0x12
pattern DW_FORM_ref4 = DW_FORM 0x13
pattern DW_FORM_ref8 = DW_FORM 0x14
pattern DW_FORM_ref_udata = DW_FORM 0x15
pattern DW_FORM_indirect = DW_FORM 0x16

-- New in DWARF version 4
pattern DW_FORM_sec_offset = DW_FORM 0x17
pattern DW_FORM_exprloc = DW_FORM 0x18
pattern DW_FORM_flag_present = DW_FORM 0x19
pattern DW_FORM_ref_sig8 = DW_FORM 0x20

-- New in DWARF version 5
pattern DW_FORM_strx = DW_FORM 0x1a
pattern DW_FORM_addrx = DW_FORM 0x1b
pattern DW_FORM_ref_sup4 = DW_FORM 0x1c
pattern DW_FORM_strp_sup = DW_FORM 0x1d
pattern DW_FORM_data16 = DW_FORM 0x1e
pattern DW_FORM_line_strp = DW_FORM 0x1f

pattern DW_FORM_implicit_const = DW_FORM 0x21
pattern DW_FORM_loclistx = DW_FORM 0x22
pattern DW_FORM_rnglistx = DW_FORM 0x23
pattern DW_FORM_ref_sup8 = DW_FORM 0x24
pattern DW_FORM_strx1 = DW_FORM 0x25
pattern DW_FORM_strx2 = DW_FORM 0x26
pattern DW_FORM_strx3 = DW_FORM 0x27
pattern DW_FORM_strx4 = DW_FORM 0x28
pattern DW_FORM_addrx1 = DW_FORM 0x29
pattern DW_FORM_addrx2 = DW_FORM 0x2a
pattern DW_FORM_addrx3 = DW_FORM 0x2b
pattern DW_FORM_addrx4 = DW_FORM 0x2c

pattern DW_FORM_GNU_addr_index = DW_FORM 0x1f01
pattern DW_FORM_GNU_str_index = DW_FORM 0x1f02

pattern DW_FORM_GNU_ref_alt = DW_FORM 0x1f20
pattern DW_FORM_GNU_strp_alt = DW_FORM 0x1f21

dwFormNamePairs :: [(DW_FORM, String)]
dwFormNamePairs =
  [ (DW_FORM_addr, "DW_FORM_addr")
  , (DW_FORM_block2, "DW_FORM_block2")
  , (DW_FORM_block4, "DW_FORM_block4")
  , (DW_FORM_data2, "DW_FORM_data2")
  , (DW_FORM_data4, "DW_FORM_data4")
  , (DW_FORM_data8, "DW_FORM_data8")
  , (DW_FORM_string, "DW_FORM_string")
  , (DW_FORM_block, "DW_FORM_block")
  , (DW_FORM_block1, "DW_FORM_block1")
  , (DW_FORM_data1, "DW_FORM_data1")
  , (DW_FORM_flag, "DW_FORM_flag")
  , (DW_FORM_sdata, "DW_FORM_sdata")
  , (DW_FORM_strp, "DW_FORM_strp")
  , (DW_FORM_udata, "DW_FORM_udata")
  , (DW_FORM_ref_addr, "DW_FORM_ref_addr")
  , (DW_FORM_ref1, "DW_FORM_ref1")
  , (DW_FORM_ref2, "DW_FORM_ref2")
  , (DW_FORM_ref4, "DW_FORM_ref4")
  , (DW_FORM_ref8, "DW_FORM_ref8")
  , (DW_FORM_ref_udata, "DW_FORM_ref_udata")
  , (DW_FORM_indirect, "DW_FORM_indirect")

  , (DW_FORM_sec_offset, "DW_FORM_sec_offset")
  , (DW_FORM_exprloc, "DW_FORM_exprloc")
  , (DW_FORM_flag_present, "DW_FORM_flag_present")

  , (DW_FORM_ref_sig8, "DW_FORM_ref_sig8")

  , (DW_FORM_strx, "DW_FORM_strx")
  , (DW_FORM_addrx, "DW_FORM_addrx")
  , (DW_FORM_ref_sup4, "DW_FORM_ref_sup4")
  , (DW_FORM_strp_sup, "DW_FORM_strp_sup")
  , (DW_FORM_data16, "DW_FORM_data16")
  , (DW_FORM_line_strp, "DW_FORM_line_strp")
  , (DW_FORM_implicit_const, "DW_FORM_implicit_const")
  , (DW_FORM_loclistx, "DW_FORM_loclistx")
  , (DW_FORM_rnglistx, "DW_FORM_rnglistx")
  , (DW_FORM_ref_sup8, "DW_FORM_ref_sup8")
  , (DW_FORM_strx1, "DW_FORM_strx1")
  , (DW_FORM_strx2, "DW_FORM_strx2")
  , (DW_FORM_strx3, "DW_FORM_strx3")
  , (DW_FORM_strx4, "DW_FORM_strx4")
  , (DW_FORM_addrx1, "DW_FORM_addrx1")
  , (DW_FORM_addrx2, "DW_FORM_addrx2")
  , (DW_FORM_addrx3, "DW_FORM_addrx3")
  , (DW_FORM_addrx4, "DW_FORM_addrx4")

  , (DW_FORM_GNU_addr_index, "DW_FORM_GNU_addr_index")
  , (DW_FORM_GNU_str_index, "DW_FORM_GNU_str_index")

  , (DW_FORM_GNU_ref_alt, "DW_FORM_GNU_ref_alt")
  , (DW_FORM_GNU_strp_alt, "DW_FORM_GNU_strp_alt")
  ]

dwFormNameMap :: Map.Map DW_FORM String
dwFormNameMap = Map.fromList dwFormNamePairs

instance Show DW_FORM where
  showsPrec p (DW_FORM x) =
    case Map.lookup (DW_FORM x) dwFormNameMap of
      Just r -> showString r
      Nothing -> showParen (p > 10) $ showString "DW_FORM 0x" . showHex x

getStringAttrWithSection :: (MonadFail m) => Word64 -> Sections -> (Sections -> m B.ByteString) -> m DW_ATVAL
getStringAttrWithSection offset secs section =
  do
      strsec <- section secs
      let str = B.drop (fromIntegral offset) strsec
      pure $! DW_ATVAL_STRING (B.takeWhile (/= 0) str)

getStringAttr :: (MonadFail m) => Word64 -> Sections -> m DW_ATVAL
getStringAttr offset secs =
  getStringAttrWithSection offset secs dsStrSection

unimplForm :: DW_FORM -> Get a
unimplForm f = fail $ "Unimplemented attribute parser: " ++ show f

-- | Evaluates attributes that are "directly" evaluable, that is they do not require the Compilation Unit Context
-- These types of operations are evaluable in the line program header context as well.
getEvaluableForm :: Sections -> Endianess -> Encoding -> TargetSize -> DW_FORM -> Get DW_ATVAL
getEvaluableForm  secs end enc tgt form = do  
  case form of
    DW_FORM_addr ->  DW_ATVAL_UINT . fromIntegral <$> getTargetAddress end tgt
    DW_FORM_block2 ->  DW_ATVAL_BLOB <$> getByteStringLen (derGetW16 end)
    DW_FORM_block4 ->  DW_ATVAL_BLOB <$> getByteStringLen (derGetW32 end)
    DW_FORM_data2 ->  DW_ATVAL_UINT . fromIntegral <$> derGetW16 end
    DW_FORM_data4 ->  DW_ATVAL_UINT . fromIntegral <$> derGetW32 end
    DW_FORM_data8 ->  DW_ATVAL_UINT . fromIntegral <$> derGetW64 end
    DW_FORM_string ->  DW_ATVAL_STRING <$> getByteStringNul
    DW_FORM_block ->  DW_ATVAL_BLOB <$> getByteStringLen getULEB128
    DW_FORM_block1 -> DW_ATVAL_BLOB <$> getByteStringLen getWord8
    DW_FORM_data1 ->  DW_ATVAL_UINT . fromIntegral <$> getWord8
    DW_FORM_flag ->  DW_ATVAL_BOOL . (/= 0) <$> getWord8
    DW_FORM_sdata ->  DW_ATVAL_INT <$> getSLEB128
    DW_FORM_strp -> do
      offset <- desrGetOffset end enc
      getStringAttr offset secs
    DW_FORM_udata ->  DW_ATVAL_UINT <$> getULEB128
    -- new in Dwarf version 4
    DW_FORM_sec_offset ->  DW_ATVAL_UINT <$> desrGetOffset end enc
    DW_FORM_exprloc ->  DW_ATVAL_BLOB <$> getByteStringLen getULEB128
    DW_FORM_flag_present -> pure ( DW_ATVAL_BOOL True)
    DW_FORM_ref_sig8 ->  DW_ATVAL_UINT . fromIntegral <$> derGetW64 end
    DW_FORM_ref_sup4 -> unimplForm form
    DW_FORM_strp_sup -> unimplForm form
    DW_FORM_data16 -> do
      lst <- replicateM 16 getWord8
      pure $ DW_ATVAL_BLOB $ B.pack lst
    DW_FORM_line_strp -> do
      offset <- desrGetOffset end enc
      getStringAttrWithSection offset secs dsLineStrSection
    DW_FORM_implicit_const -> unimplForm form
    DW_FORM_loclistx -> unimplForm form
    DW_FORM_rnglistx -> undefined
    DW_FORM_ref_sup8 -> undefined
    _ -> unimplForm form
