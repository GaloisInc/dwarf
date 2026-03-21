{-# LANGUAGE TemplateHaskell #-}
-- | Template Haskell splice that generates, for every named DW_TAG value:
--
-- * A bidirectional pattern synonym (e.g. @pattern DW_TAG_compile_unit :: DW_TAG@)
-- * A @tagName :: DW_TAG -> Maybe String@ lookup function
--
-- Intended to be used exactly once, inside 'Data.Dwarf.TAG':
--
-- > $(Data.Dwarf.TAG.TH.makeTagDefs)
--
-- The 'DW_TAG' type and its 'DW_TAG' constructor must already be in scope at
-- the splice site; they are referenced by name rather than imported here to
-- avoid a circular dependency.
module Data.Dwarf.TAG.TH (makeTagDefs) where

import Data.Word (Word64)
import Language.Haskell.TH

-- | Single source of truth: (numeric code, DWARF name) for every named DW_TAG.
tagTable :: [(Word64, String)]
tagTable =
  -- DWARF v2
  [ (0x01, "DW_TAG_array_type")
  , (0x02, "DW_TAG_class_type")
  , (0x03, "DW_TAG_entry_point")
  , (0x04, "DW_TAG_enumeration_type")
  , (0x05, "DW_TAG_formal_parameter")
  , (0x08, "DW_TAG_imported_declaration")
  , (0x0a, "DW_TAG_label")
  , (0x0b, "DW_TAG_lexical_block")
  , (0x0d, "DW_TAG_member")
  , (0x0f, "DW_TAG_pointer_type")
  , (0x10, "DW_TAG_reference_type")
  , (0x11, "DW_TAG_compile_unit")
  , (0x12, "DW_TAG_string_type")
  , (0x13, "DW_TAG_structure_type")
  , (0x15, "DW_TAG_subroutine_type")
  , (0x16, "DW_TAG_typedef")
  , (0x17, "DW_TAG_union_type")
  , (0x18, "DW_TAG_unspecified_parameters")
  , (0x19, "DW_TAG_variant")
  , (0x1a, "DW_TAG_common_block")
  , (0x1b, "DW_TAG_common_inclusion")
  , (0x1c, "DW_TAG_inheritance")
  , (0x1d, "DW_TAG_inlined_subroutine")
  , (0x1e, "DW_TAG_module")
  , (0x1f, "DW_TAG_ptr_to_member_type")
  , (0x20, "DW_TAG_set_type")
  , (0x21, "DW_TAG_subrange_type")
  , (0x22, "DW_TAG_with_stmt")
  , (0x23, "DW_TAG_access_declaration")
  , (0x24, "DW_TAG_base_type")
  , (0x25, "DW_TAG_catch_block")
  , (0x26, "DW_TAG_const_type")
  , (0x27, "DW_TAG_constant")
  , (0x28, "DW_TAG_enumerator")
  , (0x29, "DW_TAG_file_type")
  , (0x2a, "DW_TAG_friend")
  , (0x2b, "DW_TAG_namelist")
  , (0x2c, "DW_TAG_namelist_item")
  , (0x2d, "DW_TAG_packed_type")
  , (0x2e, "DW_TAG_subprogram")
  , (0x2f, "DW_TAG_template_type_parameter")
  , (0x30, "DW_TAG_template_value_parameter")
  , (0x31, "DW_TAG_thrown_type")
  , (0x32, "DW_TAG_try_block")
  , (0x33, "DW_TAG_variant_part")
  , (0x34, "DW_TAG_variable")
  , (0x35, "DW_TAG_volatile_type")
  , (0x36, "DW_TAG_dwarf_procedure")
  , (0x37, "DW_TAG_restrict_type")
  , (0x38, "DW_TAG_interface_type")
  , (0x39, "DW_TAG_namespace")
  , (0x3a, "DW_TAG_imported_module")
  , (0x3b, "DW_TAG_unspecified_type")
  , (0x3c, "DW_TAG_partial_unit")
  , (0x3d, "DW_TAG_imported_unit")
  , (0x3f, "DW_TAG_condition")
  , (0x40, "DW_TAG_shared_type")
  -- GNU extensions
  , (0x4109, "DW_TAG_GNU_call_site")
  ]

-- | Generate bidirectional pattern synonyms and 'tagName' from 'tagTable'.
makeTagDefs :: Q [Dec]
makeTagDefs = do
  patDecs <- fmap concat (mapM mkPatSyn tagTable)
  fnDecs  <- mkTagName tagTable
  return (patDecs ++ fnDecs)

-- | Generate a single bidirectional pattern synonym:
--
-- > pattern DW_TAG_foo :: DW_TAG
-- > pattern DW_TAG_foo = DW_TAG 0x..
mkPatSyn :: (Word64, String) -> Q [Dec]
mkPatSyn (code, name) = do
  let nm  = mkName name
      pat = conP (mkName "DW_TAG") [litP (integerL (fromIntegral code))]
  sig <- patSynSigD nm (conT (mkName "DW_TAG"))
  def <- patSynD nm (prefixPatSyn []) implBidir pat
  return [sig, def]

-- | Generate:
--
-- > tagName :: DW_TAG -> Maybe String
-- > tagName (DW_TAG w) = case w of
-- >   0x01 -> Just "DW_TAG_array_type"
-- >   ...
-- >   _    -> Nothing
mkTagName :: [(Word64, String)] -> Q [Dec]
mkTagName table = do
  let w       = mkName "w"
      dwTagT  = conT (mkName "DW_TAG")
      retT    = [t| Maybe String |]
      fnSigT  = arrowT `appT` dwTagT `appT` retT
      matches = [ match (litP (integerL (fromIntegral code)))
                        (normalB (appE (conE 'Just) (litE (stringL name))))
                        []
                | (code, name) <- table ]
                ++ [match wildP (normalB (conE 'Nothing)) []]
      body    = caseE (varE w) matches
  sig <- sigD (mkName "tagName") fnSigT
  dec <- funD (mkName "tagName")
           [clause [conP (mkName "DW_TAG") [varP w]] (normalB body) []]
  return [sig, dec]
