{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module PrettyPrint
  ( ppDebugInfo
  , ppDIE
  ) where

import           Data.Bits (shiftR)
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as BC
import qualified Data.Dwarf as Dwarf
import qualified Data.Map.Strict as Map
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.Builder as TLB
import qualified Data.Text.Lazy.Builder.Int as TLBI
import           Data.Word (Word8, Word64)

import           Data.Dwarf (Reader(..), TargetSize(..))

-- | Map from DieID to DW_AT_name, for resolving type references.
type NameMap = Map.Map Dwarf.DieID String

-- | Pretty-print the entire .debug_info section
ppDebugInfo :: Dwarf.Endianess -> Dwarf.Sections -> TL.Text
ppDebugInfo endian sections =
  let header = ".debug_info contents:\n"
      body   = case getAllCUs endian sections of
        Left err  -> TLB.fromString ("Error: " ++ err)
        Right cus -> foldMap (ppCU endian) cus
      text = TLB.toLazyText (header <> body)
  -- llvm-dwarfdump does not add a blank line after the very last NULL entry
  in if "\n\n" `TL.isSuffixOf` text then TL.init text else text

-- | Get all compilation units from the sections
getAllCUs :: Dwarf.Endianess -> Dwarf.Sections -> Either String [Dwarf.CUContext]
getAllCUs endian sections =
  case Dwarf.firstCUContext endian sections of
    Nothing -> Right []
    Just (Left err) -> Left err
    Just (Right cu) -> collectCUs cu
  where
    collectCUs cu = case Dwarf.nextCUContext cu of
      Nothing -> Right [cu]
      Just (Left err) -> Left err
      Just (Right nextCu) -> fmap (cu :) (collectCUs nextCu)

-- | Pretty-print a compilation unit
ppCU :: Dwarf.Endianess -> Dwarf.CUContext -> TLB.Builder
ppCU _endian cu =
  let reader   = Dwarf.cuReader cu
      addrSize = case drTarget64 reader of { TargetSize64 -> 8 :: Word64; TargetSize32 -> 4 }
      cuSize'  = Dwarf.cuSize cu
      Dwarf.CUOffset cuOff = Dwarf.cuOffset cu
      unitLength = cuSize' - 4
      nextUnit   = cuOff + cuSize'
      afterCU    = cuOff + cuSize'
  in hexPad 8 cuOff <> ": Compile Unit: length = " <> hexPad 8 unitLength
     <> ", format = DWARF32, version = 0x0004, abbr_offset = 0x0000, addr_size = "
     <> hexPad 2 addrSize <> " (next unit at " <> hexPad 8 nextUnit <> ")\n\n"
  <> case Dwarf.cuFirstDie cu of
       Left err  -> TLB.fromString ("Error parsing CU DIE: " ++ err ++ "\n")
       Right die ->
         let nameMap = buildNameMap die
         in ppDIE reader nameMap 0 afterCU die

-- | Build a map from DieID to name for the entire subtree.
buildNameMap :: Dwarf.DIE -> NameMap
buildNameMap die =
  let myEntry = case lookup (Dwarf.DW_AT 0x03) (Dwarf.dieAttributes die) of
        Just (Dwarf.DW_ATVAL_STRING n) -> [(Dwarf.dieId die, BC.unpack n)]
        _                              -> []
  in Map.fromList myEntry `Map.union`
     Map.unions (map buildNameMap (Dwarf.dieChildren die))

-- | Pretty-print a DIE and its subtree.
--
-- @afterThis@ is the offset of the first byte after this DIE's complete
-- subtree (including its own children's null terminator). Used to compute
-- the offset of null terminators within child lists.
ppDIE :: Reader -> NameMap -> Int -> Word64 -> Dwarf.DIE -> TLB.Builder
ppDIE dr nameMap indent afterThis die =
  let Dwarf.DieID dieOff = Dwarf.dieId die
      tagIndent = ' ' : replicate (indent * 2) ' '
      children  = Dwarf.dieChildren die
      childAfters =
        [ if i < length children - 1
            then let Dwarf.DieID nextOff = Dwarf.dieId (children !! (i + 1))
                 in nextOff
            else afterThis - 1
        | i <- [0 .. length children - 1]
        ]
  in hexPad 8 dieOff <> ":" <> TLB.fromString tagIndent <> ppTag (Dwarf.dieTag die) <> "\n"
  <> foldMap (ppAttribute dr nameMap (indent + 1)) (Dwarf.dieAttributes die)
  <> "\n"
  <> if null children
       then mempty
       else mconcat (zipWith (ppDIE dr nameMap (indent + 1)) childAfters children)
            <> ppNull (indent + 1) (afterThis - 1)

-- | Print a DWARF null terminator entry (with a trailing blank line).
ppNull :: Int -> Word64 -> TLB.Builder
ppNull indent offset =
  hexPad 8 offset <> ":" <> TLB.fromString (' ' : replicate (indent * 2) ' ') <> "NULL\n\n"

-- | Pretty-print an attribute
ppAttribute :: Reader -> NameMap -> Int -> (Dwarf.DW_AT, Dwarf.DW_ATVAL) -> TLB.Builder
ppAttribute dr nameMap indent (at, val) =
  TLB.fromString (replicate (indent * 2 + 12) ' ')
  <> ppDW_AT at
  <> "\t"
  <> ppDW_ATVAL dr nameMap at val
  <> "\n"

-- | Format attribute name
ppDW_AT :: Dwarf.DW_AT -> TLB.Builder
ppDW_AT at@(Dwarf.DW_AT w) = case Dwarf.atName at of
  Just name -> TLB.fromString name
  Nothing   -> "DW_AT_0x" <> TLBI.hexadecimal w

-- | Format attribute value (context-aware)
ppDW_ATVAL :: Reader -> NameMap -> Dwarf.DW_AT -> Dwarf.DW_ATVAL -> TLB.Builder
ppDW_ATVAL dr nameMap at = \case
  Dwarf.DW_ATVAL_UINT w   -> formatUint at w
  Dwarf.DW_ATVAL_UDATA w  -> "(" <> TLBI.decimal w <> ")"
  Dwarf.DW_ATVAL_INT i    -> "(" <> TLBI.decimal i <> ")"
  Dwarf.DW_ATVAL_STRING n -> TLB.fromString ("(" ++ show (BC.unpack n) ++ ")")
  Dwarf.DW_ATVAL_REF did  -> formatRef at did nameMap
  Dwarf.DW_ATVAL_BLOB b   -> formatBlob dr b
  Dwarf.DW_ATVAL_BOOL b   -> if b then "(true)" else "(false)"

-- | Format a reference value.  DW_AT_type includes the referenced type name;
-- all other reference attributes show only the offset.
formatRef :: Dwarf.DW_AT -> Dwarf.DieID -> NameMap -> TLB.Builder
formatRef at did nameMap =
  let Dwarf.DieID offset = did
      base = "(" <> hexPad 8 offset
  in case at of
       Dwarf.DW_AT_type ->
         case Map.lookup did nameMap of
           Just n  -> base <> TLB.fromString (" \"" ++ n ++ "\")")
           Nothing -> base <> ")"
       _ -> base <> ")"

-- | Context-aware uint formatting
formatUint :: Dwarf.DW_AT -> Word64 -> TLB.Builder
formatUint at w = case at of
  Dwarf.DW_AT_low_pc -> "(" <> hexPad 16 w <> ")"
  Dwarf.DW_AT_high_pc -> "(" <> hexPad 16 w <> ")"
  Dwarf.DW_AT_entry_pc -> "(" <> hexPad 16 w <> ")"
  Dwarf.DW_AT_byte_size -> "(" <> hexPad 2 w <> ")"
  Dwarf.DW_AT_byte_stride -> "(" <> hexPad 2 w <> ")"
  Dwarf.DW_AT_language -> "(" <> languageName w <> ")"
  Dwarf.DW_AT_encoding -> "(" <> ateName w <> ")"
  Dwarf.DW_AT_stmt_list -> "(" <> hexPad 8 w <> ")"
  Dwarf.DW_AT_decl_file -> "(" <> TLBI.decimal w <> ")"
  Dwarf.DW_AT_decl_line -> "(" <> TLBI.decimal w <> ")"
  Dwarf.DW_AT_decl_column -> "(" <> TLBI.decimal w <> ")"
  Dwarf.DW_AT_const_value -> "(" <> hexPad 2 w <> ")"
  Dwarf.DW_AT_data_member_location -> "(" <> hexPad 2 w <> ")"
  _ -> "(" <> hexPad 1 w <> ")"

-- | Map DW_LANG codes to names
languageName :: Word64 -> TLB.Builder
languageName = \case
  0x0001 -> "DW_LANG_C89"
  0x0002 -> "DW_LANG_C"
  0x0004 -> "DW_LANG_C_plus_plus"
  0x000c -> "DW_LANG_C99"
  0x001c -> "DW_LANG_C_plus_plus_14"
  0x001d -> "DW_LANG_C11"
  w      -> "DW_LANG_0x" <> TLBI.hexadecimal w

-- | Map DW_ATE encoding codes to names
ateName :: Word64 -> TLB.Builder
ateName = \case
  0x01 -> "DW_ATE_address"
  0x02 -> "DW_ATE_boolean"
  0x03 -> "DW_ATE_complex_float"
  0x04 -> "DW_ATE_float"
  0x05 -> "DW_ATE_signed"
  0x06 -> "DW_ATE_signed_char"
  0x07 -> "DW_ATE_unsigned"
  0x08 -> "DW_ATE_unsigned_char"
  0x09 -> "DW_ATE_imaginary_float"
  0x0a -> "DW_ATE_packed_decimal"
  0x0b -> "DW_ATE_numeric_string"
  0x0c -> "DW_ATE_edited"
  0x0d -> "DW_ATE_signed_fixed"
  0x0e -> "DW_ATE_unsigned_fixed"
  0x0f -> "DW_ATE_decimal_float"
  0x10 -> "DW_ATE_UTF"
  w    -> "DW_ATE_0x" <> TLBI.hexadecimal w

-- | Format a blob (raw hex bytes, for location expressions etc.)
-- These attributes are sanitized in the golden comparison.
formatBlob :: Reader -> B.ByteString -> TLB.Builder
formatBlob _dr b = case B.unpack b of
  []     -> mempty
  (x:xs) -> hexByte x <> foldMap (\w -> " " <> hexByte w) xs

-- | Format DW_TAG
ppTag :: Dwarf.DW_TAG -> TLB.Builder
ppTag (Dwarf.DW_TAG w) = case tagNameMap w of
  Just name -> TLB.fromString name
  Nothing   -> "DW_TAG_0x" <> TLBI.hexadecimal w

-- | Map DW_TAG codes to names
tagNameMap :: Word64 -> Maybe String
tagNameMap = \case
  0x01 -> Just "DW_TAG_array_type"
  0x02 -> Just "DW_TAG_class_type"
  0x03 -> Just "DW_TAG_entry_point"
  0x04 -> Just "DW_TAG_enumeration_type"
  0x05 -> Just "DW_TAG_formal_parameter"
  0x08 -> Just "DW_TAG_imported_declaration"
  0x0a -> Just "DW_TAG_label"
  0x0b -> Just "DW_TAG_lexical_block"
  0x0d -> Just "DW_TAG_member"
  0x0f -> Just "DW_TAG_pointer_type"
  0x10 -> Just "DW_TAG_reference_type"
  0x11 -> Just "DW_TAG_compile_unit"
  0x12 -> Just "DW_TAG_string_type"
  0x13 -> Just "DW_TAG_structure_type"
  0x15 -> Just "DW_TAG_subroutine_type"
  0x16 -> Just "DW_TAG_typedef"
  0x17 -> Just "DW_TAG_union_type"
  0x18 -> Just "DW_TAG_unspecified_parameters"
  0x19 -> Just "DW_TAG_variant"
  0x1a -> Just "DW_TAG_common_block"
  0x1b -> Just "DW_TAG_common_inclusion"
  0x1c -> Just "DW_TAG_inheritance"
  0x1d -> Just "DW_TAG_inlined_subroutine"
  0x1e -> Just "DW_TAG_module"
  0x1f -> Just "DW_TAG_ptr_to_member_type"
  0x20 -> Just "DW_TAG_set_type"
  0x21 -> Just "DW_TAG_subrange_type"
  0x22 -> Just "DW_TAG_with_stmt"
  0x23 -> Just "DW_TAG_access_declaration"
  0x24 -> Just "DW_TAG_base_type"
  0x25 -> Just "DW_TAG_catch_block"
  0x26 -> Just "DW_TAG_const_type"
  0x27 -> Just "DW_TAG_constant"
  0x28 -> Just "DW_TAG_enumerator"
  0x29 -> Just "DW_TAG_file_type"
  0x2a -> Just "DW_TAG_friend"
  0x2b -> Just "DW_TAG_namelist"
  0x2c -> Just "DW_TAG_namelist_item"
  0x2d -> Just "DW_TAG_packed_type"
  0x2e -> Just "DW_TAG_subprogram"
  0x2f -> Just "DW_TAG_template_type_parameter"
  0x30 -> Just "DW_TAG_template_value_parameter"
  0x31 -> Just "DW_TAG_thrown_type"
  0x32 -> Just "DW_TAG_try_block"
  0x33 -> Just "DW_TAG_variant_part"
  0x34 -> Just "DW_TAG_variable"
  0x35 -> Just "DW_TAG_volatile_type"
  0x36 -> Just "DW_TAG_dwarf_procedure"
  0x37 -> Just "DW_TAG_restrict_type"
  0x38 -> Just "DW_TAG_interface_type"
  0x39 -> Just "DW_TAG_namespace"
  0x3a -> Just "DW_TAG_imported_module"
  0x3b -> Just "DW_TAG_unspecified_type"
  0x3c -> Just "DW_TAG_partial_unit"
  0x3d -> Just "DW_TAG_imported_unit"
  0x3f -> Just "DW_TAG_condition"
  0x40 -> Just "DW_TAG_shared_type"
  0x4109 -> Just "DW_TAG_GNU_call_site"
  _    -> Nothing

-- | Zero-pad a hex number to at least @width@ digits, with @0x@ prefix.
hexPad :: Int -> Word64 -> TLB.Builder
hexPad width w = "0x" <> TLB.fromLazyText zeros <> TLBI.hexadecimal w
  where zeros = TL.replicate (fromIntegral $ max 0 (width - numHexDigits w)) "0"

-- | Two-digit lowercase hex without prefix, for blob bytes.
hexByte :: Word8 -> TLB.Builder
hexByte w
  | w < 16    = "0" <> TLBI.hexadecimal w
  | otherwise = TLBI.hexadecimal w

-- | Number of lowercase hex digits needed to represent @w@ (minimum 1).
numHexDigits :: Word64 -> Int
numHexDigits 0 = 1
numHexDigits w = go 0 w
  where
    go n 0 = n
    go n x = go (n + 1) (x `shiftR` 4)
