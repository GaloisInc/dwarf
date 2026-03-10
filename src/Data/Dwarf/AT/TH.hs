{-# LANGUAGE TemplateHaskell #-}
-- | Template Haskell splice that generates, for every named DW_AT value:
--
-- * A bidirectional pattern synonym (e.g. @pattern DW_AT_low_pc :: DW_AT@)
-- * An @atName :: DW_AT -> Maybe String@ lookup function
--
-- Intended to be used exactly once, inside 'Data.Dwarf.AT':
--
-- > $(Data.Dwarf.AT.TH.makeAttrDefs)
--
-- The 'DW_AT' type and its 'DW_AT' constructor must already be in scope at
-- the splice site; they are referenced by name rather than imported here to
-- avoid a circular dependency.
module Data.Dwarf.AT.TH (makeAttrDefs) where

import Data.Word (Word64)
import Language.Haskell.TH

-- | Single source of truth: (numeric code, DWARF name) for every named DW_AT.
attrTable :: [(Word64, String)]
attrTable =
  -- DWARF v2
  [ (0x01, "DW_AT_sibling")
  , (0x02, "DW_AT_location")
  , (0x03, "DW_AT_name")
  , (0x09, "DW_AT_ordering")
  , (0x0b, "DW_AT_byte_size")
  , (0x0c, "DW_AT_bit_offset")
  , (0x0d, "DW_AT_bit_size")
  , (0x10, "DW_AT_stmt_list")
  , (0x11, "DW_AT_low_pc")
  , (0x12, "DW_AT_high_pc")
  , (0x13, "DW_AT_language")
  , (0x15, "DW_AT_discr")
  , (0x16, "DW_AT_discr_value")
  , (0x17, "DW_AT_visibility")
  , (0x18, "DW_AT_import")
  , (0x19, "DW_AT_string_length")
  , (0x1a, "DW_AT_common_reference")
  , (0x1b, "DW_AT_comp_dir")
  , (0x1c, "DW_AT_const_value")
  , (0x1d, "DW_AT_containing_type")
  , (0x1e, "DW_AT_default_value")
  , (0x20, "DW_AT_inline")
  , (0x21, "DW_AT_is_optional")
  , (0x22, "DW_AT_lower_bound")
  , (0x25, "DW_AT_producer")
  , (0x27, "DW_AT_prototyped")
  , (0x2a, "DW_AT_return_addr")
  , (0x2c, "DW_AT_start_scope")
  , (0x2e, "DW_AT_bit_stride")
  , (0x2f, "DW_AT_upper_bound")
  , (0x31, "DW_AT_abstract_origin")
  , (0x32, "DW_AT_accessibility")
  , (0x33, "DW_AT_address_class")
  , (0x34, "DW_AT_artificial")
  , (0x35, "DW_AT_base_types")
  , (0x36, "DW_AT_calling_convention")
  , (0x37, "DW_AT_count")
  , (0x38, "DW_AT_data_member_location")
  , (0x39, "DW_AT_decl_column")
  , (0x3a, "DW_AT_decl_file")
  , (0x3b, "DW_AT_decl_line")
  , (0x3c, "DW_AT_declaration")
  , (0x3d, "DW_AT_discr_list")
  , (0x3e, "DW_AT_encoding")
  , (0x3f, "DW_AT_external")
  , (0x40, "DW_AT_frame_base")
  , (0x41, "DW_AT_friend")
  , (0x42, "DW_AT_identifier_case")
  , (0x43, "DW_AT_macro_info")
  , (0x44, "DW_AT_namelist_item")
  , (0x45, "DW_AT_priority")
  , (0x46, "DW_AT_segment")
  , (0x47, "DW_AT_specification")
  , (0x48, "DW_AT_static_link")
  , (0x49, "DW_AT_type")
  , (0x4a, "DW_AT_use_location")
  , (0x4b, "DW_AT_variable_parameter")
  , (0x4c, "DW_AT_virtuality")
  , (0x4d, "DW_AT_vtable_elem_location")
  , (0x4e, "DW_AT_allocated")
  , (0x4f, "DW_AT_associated")
  , (0x50, "DW_AT_data_location")
  , (0x51, "DW_AT_byte_stride")
  , (0x52, "DW_AT_entry_pc")
  , (0x53, "DW_AT_use_UTF8")
  , (0x54, "DW_AT_extension")
  , (0x55, "DW_AT_ranges")
  , (0x56, "DW_AT_trampoline")
  , (0x57, "DW_AT_call_column")
  , (0x58, "DW_AT_call_file")
  , (0x59, "DW_AT_call_line")
  , (0x5a, "DW_AT_description")
  , (0x5b, "DW_AT_binary_scale")
  , (0x5c, "DW_AT_decimal_scale")
  , (0x5d, "DW_AT_small")
  , (0x5e, "DW_AT_decimal_sign")
  , (0x5f, "DW_AT_digit_count")
  , (0x60, "DW_AT_picture_string")
  , (0x61, "DW_AT_mutable")
  , (0x62, "DW_AT_threads_scaled")
  , (0x63, "DW_AT_explicit")
  , (0x64, "DW_AT_object_pointer")
  , (0x65, "DW_AT_endianity")
  , (0x66, "DW_AT_elemental")
  , (0x67, "DW_AT_pure")
  , (0x68, "DW_AT_recursive")
  -- DWARF v4
  , (0x69, "DW_AT_signature")
  , (0x6a, "DW_AT_main_subprogram")
  , (0x6b, "DW_AT_data_bit_offset")
  , (0x6c, "DW_AT_const_expr")
  , (0x6d, "DW_AT_enum_class")
  , (0x6e, "DW_AT_linkage_name")
  -- DWARF v5
  , (0x6f, "DW_AT_string_length_bit_size")
  , (0x70, "DW_AT_string_length_byte_size")
  , (0x71, "DW_AT_rank")
  , (0x72, "DW_AT_str_offsets_base")
  , (0x73, "DW_AT_addr_base")
  , (0x74, "DW_AT_rnglists_base")
  , (0x75, "DW_AT_dwo_id")
  , (0x76, "DW_AT_dwo_name")
  , (0x77, "DW_AT_reference")
  , (0x78, "DW_AT_rvalue_reference")
  , (0x79, "DW_AT_macros")
  , (0x7a, "DW_AT_call_all_calls")
  , (0x7b, "DW_AT_call_all_source_calls")
  , (0x7c, "DW_AT_call_all_tail_calls")
  , (0x7d, "DW_AT_call_return_pc")
  , (0x7e, "DW_AT_call_value")
  , (0x7f, "DW_AT_call_origin")
  , (0x80, "DW_AT_call_parameter")
  , (0x81, "DW_AT_call_pc")
  , (0x82, "DW_AT_call_tail_call")
  , (0x83, "DW_AT_call_target")
  , (0x84, "DW_AT_call_target_clobbered")
  , (0x85, "DW_AT_call_data_location")
  , (0x86, "DW_AT_call_data_value")
  , (0x87, "DW_AT_noreturn")
  , (0x88, "DW_AT_alignment")
  , (0x89, "DW_AT_export_symbols")
  , (0x8a, "DW_AT_deleted")
  , (0x8b, "DW_AT_defaulted")
  , (0x8c, "DW_AT_loclists_base")
  -- MIPS
  , (0x2002, "DW_AT_MIPS_loop_begin")
  , (0x2003, "DW_AT_MIPS_tail_loop_begin")
  , (0x2004, "DW_AT_MIPS_epilog_begin")
  , (0x2005, "DW_AT_MIPS_loop_unroll_factor")
  , (0x2006, "DW_AT_MIPS_software_pipeline_depth")
  , (0x2007, "DW_AT_MIPS_linkage_name")
  , (0x2008, "DW_AT_MIPS_stride")
  , (0x2009, "DW_AT_MIPS_abstract_name")
  , (0x200a, "DW_AT_MIPS_clone_origin")
  , (0x200b, "DW_AT_MIPS_has_inlines")
  , (0x200c, "DW_AT_MIPS_stride_byte")
  , (0x200d, "DW_AT_MIPS_stride_elem")
  , (0x200e, "DW_AT_MIPS_ptr_dopetype")
  , (0x200f, "DW_AT_MIPS_allocatable_dopetype")
  , (0x2010, "DW_AT_MIPS_assumed_shape_dopetype")
  , (0x2011, "DW_AT_MIPS_assumed_size")
  -- SGI/IRIX
  , (0x2101, "DW_AT_sf_names")
  , (0x2102, "DW_AT_src_info")
  , (0x2103, "DW_AT_mac_info")
  , (0x2104, "DW_AT_src_coords")
  , (0x2105, "DW_AT_body_begin")
  , (0x2106, "DW_AT_body_end")
  -- GNU
  , (0x2107, "DW_AT_GNU_vector")
  , (0x210f, "DW_AT_GNU_odr_signature")
  , (0x2110, "DW_AT_GNU_template_name")
  , (0x2111, "DW_AT_GNU_call_site_value")
  , (0x2112, "DW_AT_GNU_call_site_data_value")
  , (0x2113, "DW_AT_GNU_call_site_target")
  , (0x2114, "DW_AT_GNU_call_site_target_clobbered")
  , (0x2115, "DW_AT_GNU_tail_call")
  , (0x2116, "DW_AT_GNU_all_tail_call_sites")
  , (0x2117, "DW_AT_GNU_all_call_sites")
  , (0x2118, "DW_AT_GNU_all_source_call_sites")
  , (0x2119, "DW_AT_GNU_macros")
  , (0x2130, "DW_AT_GNU_dwo_name")
  , (0x2131, "DW_AT_GNU_dwo_id")
  , (0x2132, "DW_AT_GNU_ranges_base")
  , (0x2133, "DW_AT_GNU_addr_base")
  , (0x2134, "DW_AT_GNU_pubnames")
  , (0x2135, "DW_AT_GNU_pubtypes")
  , (0x2136, "DW_AT_GNU_discriminator")
  -- Borland
  , (0x3b11, "DW_AT_BORLAND_property_read")
  , (0x3b12, "DW_AT_BORLAND_property_write")
  , (0x3b13, "DW_AT_BORLAND_property_implements")
  , (0x3b14, "DW_AT_BORLAND_property_index")
  , (0x3b15, "DW_AT_BORLAND_property_default")
  , (0x3b20, "DW_AT_BORLAND_Delphi_unit")
  , (0x3b21, "DW_AT_BORLAND_Delphi_class")
  , (0x3b22, "DW_AT_BORLAND_Delphi_record")
  , (0x3b23, "DW_AT_BORLAND_Delphi_metaclass")
  , (0x3b24, "DW_AT_BORLAND_Delphi_constructor")
  , (0x3b25, "DW_AT_BORLAND_Delphi_destructor")
  , (0x3b26, "DW_AT_BORLAND_Delphi_anonymous_method")
  , (0x3b27, "DW_AT_BORLAND_Delphi_interface")
  , (0x3b28, "DW_AT_BORLAND_Delphi_ABI")
  , (0x3b29, "DW_AT_BORLAND_Delphi_return")
  , (0x3b30, "DW_AT_BORLAND_Delphi_frameptr")
  , (0x3b31, "DW_AT_BORLAND_closure")
  -- LLVM
  , (0x3e00, "DW_AT_LLVM_include_path")
  , (0x3e01, "DW_AT_LLVM_config_macros")
  , (0x3e02, "DW_AT_LLVM_isysroot")
  , (0x3e03, "DW_AT_LLVM_tag_offset")
  -- Apple
  , (0x3fe1, "DW_AT_APPLE_optimized")
  , (0x3fe2, "DW_AT_APPLE_flags")
  , (0x3fe3, "DW_AT_APPLE_isa")
  , (0x3fe4, "DW_AT_APPLE_block")
  , (0x3fe5, "DW_AT_APPLE_major_runtime_vers")
  , (0x3fe6, "DW_AT_APPLE_runtime_class")
  , (0x3fe7, "DW_AT_APPLE_omit_frame_ptr")
  , (0x3fe8, "DW_AT_APPLE_property_name")
  , (0x3fe9, "DW_AT_APPLE_property_getter")
  , (0x3fea, "DW_AT_APPLE_property_setter")
  , (0x3feb, "DW_AT_APPLE_property_attribute")
  , (0x3fec, "DW_AT_APPLE_objc_complete_type")
  , (0x3fed, "DW_AT_APPLE_property")
  ]

-- | Generate bidirectional pattern synonyms and 'atName' from 'attrTable'.
makeAttrDefs :: Q [Dec]
makeAttrDefs = do
  patDecs <- fmap concat (mapM mkPatSyn attrTable)
  fnDecs  <- mkAtName attrTable
  return (patDecs ++ fnDecs)

-- | Generate a single bidirectional pattern synonym:
--
-- > pattern DW_AT_foo :: DW_AT
-- > pattern DW_AT_foo = DW_AT 0x..
mkPatSyn :: (Word64, String) -> Q [Dec]
mkPatSyn (code, name) = do
  let nm  = mkName name
      pat = conP (mkName "DW_AT") [litP (integerL (fromIntegral code))]
  sig <- patSynSigD nm (conT (mkName "DW_AT"))
  def <- patSynD nm (prefixPatSyn []) implBidir pat
  return [sig, def]

-- | Generate:
--
-- > atName :: DW_AT -> Maybe String
-- > atName (DW_AT w) = case w of
-- >   0x01 -> Just "DW_AT_sibling"
-- >   ...
-- >   _    -> Nothing
mkAtName :: [(Word64, String)] -> Q [Dec]
mkAtName table = do
  let w       = mkName "w"
      dwAtT   = conT (mkName "DW_AT")
      retT    = [t| Maybe String |]
      fnSigT  = arrowT `appT` dwAtT `appT` retT
      matches = [ match (litP (integerL (fromIntegral code)))
                        (normalB (appE (conE 'Just) (litE (stringL name))))
                        []
                | (code, name) <- table ]
                ++ [match wildP (normalB (conE 'Nothing)) []]
      body    = caseE (varE w) matches
  sig <- sigD (mkName "atName") fnSigT
  dec <- funD (mkName "atName")
           [clause [conP (mkName "DW_AT") [varP w]] (normalB body) []]
  return [sig, dec]
