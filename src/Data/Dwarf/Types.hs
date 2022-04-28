{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -fno-warn-missing-pattern-synonym-signatures #-}
-- We currently disable -Wmissing-signatures as a way to avoid warnings on
-- GHC 9.2, which emits -Wmissing-signatures warnings related to pattern
-- synonyms even if -Wmissing-pattern-synonym-signatures is disabled. See
-- https://gitlab.haskell.org/ghc/ghc/-/issues/14794#note_424553. If that
-- issue is resolved in a subsequent minor release of GHC 9.2, we can remove
-- this workaround.
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module Data.Dwarf.Types
  ( module Data.Dwarf.Types
  )
where

import Data.List (stripPrefix)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Word (Word64)
import Numeric (readHex, showHex)
import qualified Text.ParserCombinators.ReadP as RP
import Text.Read

-- | The offset of a DWARF DIE entry from the dwarf info file.
newtype DieID = DieID Word64
  deriving (Eq, Ord)

instance Show DieID where
  showsPrec _ (DieID x) = showString "DIE@" . showHex x

instance Read DieID where
  readsPrec _ str =
    case stripPrefix "DIE@" str of
      Just rest -> [(DieID x, y) | (x, y) <- readHex rest]
      Nothing -> []

data DW_DS
  = DW_DS_unsigned
  | DW_DS_leading_overpunch
  | DW_DS_trailing_overpunch
  | DW_DS_leading_separate
  | DW_DS_trailing_separate
  deriving (Eq, Ord, Read, Show)

dw_ds :: Word64 -> DW_DS
dw_ds 0x01 = DW_DS_unsigned
dw_ds 0x02 = DW_DS_leading_overpunch
dw_ds 0x03 = DW_DS_trailing_overpunch
dw_ds 0x04 = DW_DS_leading_separate
dw_ds 0x05 = DW_DS_trailing_separate
dw_ds tag = error $ "Invalid DW_DS tag: " ++ show tag

data DW_END
  = DW_END_default
  | DW_END_big
  | DW_END_little
  deriving (Eq, Ord, Read, Show)

dw_end :: Word64 -> DW_END
dw_end 0x00 = DW_END_default
dw_end 0x01 = DW_END_big
dw_end 0x02 = DW_END_little
dw_end n = error $ "Unrecognized DW_END value " ++ show n

data DW_ACCESS
  = DW_ACCESS_public
  | DW_ACCESS_protected
  | DW_ACCESS_private
  deriving (Eq, Ord, Read, Show)

dw_access :: Word64 -> DW_ACCESS
dw_access 0x01 = DW_ACCESS_public
dw_access 0x02 = DW_ACCESS_protected
dw_access 0x03 = DW_ACCESS_private
dw_access tag = error $ "Invalid dw_access tag: " ++ show tag

data DW_VIS
  = DW_VIS_local
  | DW_VIS_exported
  | DW_VIS_qualified
  deriving (Eq, Ord, Read, Show)

dw_vis :: Word64 -> DW_VIS
dw_vis 0x01 = DW_VIS_local
dw_vis 0x02 = DW_VIS_exported
dw_vis 0x03 = DW_VIS_qualified
dw_vis tag = error $ "Invalid DW_VIS tag: " ++ show tag

data DW_VIRTUALITY
  = DW_VIRTUALITY_none
  | DW_VIRTUALITY_virtual
  | DW_VIRTUALITY_return_virtual
  deriving (Eq, Ord, Read, Show)

dw_virtuality :: Word64 -> DW_VIRTUALITY
dw_virtuality 0x00 = DW_VIRTUALITY_none
dw_virtuality 0x01 = DW_VIRTUALITY_virtual
dw_virtuality 0x02 = DW_VIRTUALITY_return_virtual
dw_virtuality tag = error $ "Invalid tag for DW_VIRTUALITY: " ++ show tag

data DW_LANG = DW_LANG Word64
  deriving (Eq, Ord)

pattern DW_LANG_C89 = DW_LANG 0x0001

pattern DW_LANG_C = DW_LANG 0x0002

pattern DW_LANG_Ada83 = DW_LANG 0x0003

pattern DW_LANG_C_plus_plus = DW_LANG 0x0004

pattern DW_LANG_Cobol74 = DW_LANG 0x0005

pattern DW_LANG_Cobol85 = DW_LANG 0x0006

pattern DW_LANG_Fortran77 = DW_LANG 0x0007

pattern DW_LANG_Fortran90 = DW_LANG 0x0008

pattern DW_LANG_Pascal83 = DW_LANG 0x0009

pattern DW_LANG_Modula2 = DW_LANG 0x000a

pattern DW_LANG_Java = DW_LANG 0x000b

pattern DW_LANG_C99 = DW_LANG 0x000c

pattern DW_LANG_Ada95 = DW_LANG 0x000d

pattern DW_LANG_Fortran95 = DW_LANG 0x000e

pattern DW_LANG_PLI = DW_LANG 0x000f

pattern DW_LANG_ObjC = DW_LANG 0x0010

pattern DW_LANG_ObjC_plus_plus = DW_LANG 0x0011

pattern DW_LANG_UPC = DW_LANG 0x0012

pattern DW_LANG_D = DW_LANG 0x0013

dw_lang_name_map :: Map DW_LANG String
dw_lang_name_map =
  Map.fromList
    [ (DW_LANG_C89, "DW_LANG_C89"),
      (DW_LANG_C, "DW_LANG_C"),
      (DW_LANG_Ada83, "DW_LANG_Ada83"),
      (DW_LANG_C_plus_plus, "DW_LANG_C_plus_plus"),
      (DW_LANG_Cobol74, "DW_LANG_Cobol74"),
      (DW_LANG_Cobol85, "DW_LANG_Cobol85"),
      (DW_LANG_Fortran77, "DW_LANG_Fortran77"),
      (DW_LANG_Fortran90, "DW_LANG_Fortran90"),
      (DW_LANG_Pascal83, "DW_LANG_Pascal83"),
      (DW_LANG_Modula2, "DW_LANG_Modula2"),
      (DW_LANG_Java, "DW_LANG_Java"),
      (DW_LANG_C99, "DW_LANG_C99"),
      (DW_LANG_Ada95, "DW_LANG_Ada95"),
      (DW_LANG_Fortran95, "DW_LANG_Fortran95"),
      (DW_LANG_PLI, "DW_LANG_PLI"),
      (DW_LANG_ObjC, "DW_LANG_ObjC"),
      (DW_LANG_ObjC_plus_plus, "DW_LANG_ObjC_plus_plus"),
      (DW_LANG_UPC, "DW_LANG_UPC"),
      (DW_LANG_D, "DW_LANG_D")
    ]

instance Show DW_LANG where
  showsPrec p (DW_LANG w) =
    case Map.lookup (DW_LANG w) dw_lang_name_map of
      Just r -> showString r
      Nothing -> showParen (p > 10) $ showString "DW_LANG " . showHex w

data DW_ID
  = DW_ID_case_sensitive
  | DW_ID_up_case
  | DW_ID_down_case
  | DW_ID_case_insensitive
  deriving (Eq, Ord, Read, Show)

dw_id :: Word64 -> DW_ID
dw_id 0x00 = DW_ID_case_sensitive
dw_id 0x01 = DW_ID_up_case
dw_id 0x02 = DW_ID_down_case
dw_id 0x03 = DW_ID_case_insensitive
dw_id n = error $ "Unrecognized DW_ID " ++ show n

data DW_CC
  = DW_CC_normal
  | DW_CC_program
  | DW_CC_nocall
  deriving (Eq, Ord, Read, Show)

dw_cc :: Word64 -> DW_CC
dw_cc 0x01 = DW_CC_normal
dw_cc 0x02 = DW_CC_program
dw_cc 0x03 = DW_CC_nocall
dw_cc n = error $ "Unrecognized calling convention " ++ show n

newtype DW_INL = DW_INL Word64

pattern DW_INL_not_inlined = DW_INL 0

pattern DW_INL_inlined = DW_INL 1

pattern DW_INL_declared_not_inlined = DW_INL 2

pattern DW_INL_declared_inlined = DW_INL 3

instance Show DW_INL where
  showsPrec _ DW_INL_not_inlined = (++) "DW_INL_not_inlined"
  showsPrec _ DW_INL_inlined = (++) "DW_INL_inlined"
  showsPrec _ DW_INL_declared_not_inlined = (++) "DW_INL_declared_not_inlined"
  showsPrec _ DW_INL_declared_inlined = (++) "DW_INL_declared_inlined"
  showsPrec p (DW_INL x) = showParen (p >= 10) $ ("DW_INL " ++) . shows x

matchConst :: String -> a -> ReadPrec a
matchConst s x = readP_to_Prec (\_ -> x <$ RP.string s)

instance Read DW_INL where
  readPrec =
    matchConst "DW_INL_not_inlined" DW_INL_not_inlined
      <++ matchConst "DW_INL_inlined" DW_INL_inlined
      <++ matchConst "DW_INL_declared_not_inlined" DW_INL_declared_not_inlined
      <++ matchConst "DW_INL_declared_inlined" DW_INL_declared_inlined

data DW_ORD
  = DW_ORD_row_major
  | DW_ORD_col_major
  deriving (Eq, Ord, Read, Show)

dw_ord :: Word64 -> DW_ORD
dw_ord 0x00 = DW_ORD_row_major
dw_ord 0x01 = DW_ORD_col_major
dw_ord n = error $ "Unrecognized DW_ORD " ++ show n

data DW_DSC
  = DW_DSC_label
  | DW_DSC_range
  deriving (Eq, Ord, Read, Show)

dw_dsc :: Word64 -> DW_DSC
dw_dsc 0x00 = DW_DSC_label
dw_dsc 0x01 = DW_DSC_range
dw_dsc n = error $ "Unrecognized DW_DSC " ++ show n
