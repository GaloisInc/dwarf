{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fno-warn-missing-pattern-synonym-signatures #-}
-- We currently disable -Wmissing-signatures as a way to avoid warnings on
-- GHC 9.2, which emits -Wmissing-signatures warnings related to pattern
-- synonyms even if -Wmissing-pattern-synonym-signatures is disabled. See
-- https://gitlab.haskell.org/ghc/ghc/-/issues/14794#note_424553. If that
-- issue is resolved in a subsequent minor release of GHC 9.2, we can remove
-- this workaround.
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
module Data.Dwarf.AT where

import qualified Data.ByteString as B
import           Data.Dwarf.AT.TH (makeAttrDefs)
import           Data.Dwarf.Types
import           Data.Int (Int64)
import           Data.Word (Word64)
import           Numeric (showHex)


data DW_ATVAL
    = DW_ATVAL_INT    Int64
    | DW_ATVAL_UINT   Word64
    -- ^ Fixed-width unsigned integer (DW_FORM_data1/data2/data4/data8).
    -- Pretty-printers should render this as hex with form-appropriate width.
    | DW_ATVAL_UDATA  Word64
    -- ^ Variable-length unsigned integer (DW_FORM_udata / ULEB128).
    -- Pretty-printers should render this as decimal.
    | DW_ATVAL_REF    DieID
    | DW_ATVAL_STRING B.ByteString
    | DW_ATVAL_BLOB   B.ByteString
    | DW_ATVAL_BOOL   Bool
    deriving (Eq, Ord, Show)

data DW_AT = DW_AT Word64
  deriving (Eq, Ord)

-- | Generate pattern synonyms (e.g. @pattern DW_AT_low_pc :: DW_AT@) and
-- @atName :: DW_AT -> Maybe String@ from the table in "Data.Dwarf.AT.TH".
$(makeAttrDefs)

instance Show DW_AT where
  showsPrec p at@(DW_AT a) =
    case atName at of
      Just name -> showString name
      Nothing   -> showParen (p > 10) $ showString "DW_AT 0x" . showHex a
