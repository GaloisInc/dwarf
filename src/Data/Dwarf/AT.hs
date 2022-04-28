{-# LANGUAGE PatternSynonyms #-}
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
import           Data.Dwarf.Types
import           Data.Int (Int64)
import qualified Data.Map.Strict as Map
import           Data.Word (Word64)
import           Numeric (showHex)


data DW_ATVAL
    = DW_ATVAL_INT    Int64
    | DW_ATVAL_UINT   Word64
    | DW_ATVAL_REF    DieID
    | DW_ATVAL_STRING B.ByteString
    | DW_ATVAL_BLOB   B.ByteString
    | DW_ATVAL_BOOL   Bool
    deriving (Eq, Ord, Show)

data DW_AT = DW_AT Word64
  deriving (Eq, Ord)

pattern DW_AT_sibling = DW_AT 0x01
pattern DW_AT_location = DW_AT 0x02
pattern DW_AT_name = DW_AT 0x03
pattern DW_AT_ordering = DW_AT 0x09
pattern DW_AT_byte_size = DW_AT 0x0b

-- | Offset from left in a member
--
-- Defined in Dwarf v3 and earlier.
pattern DW_AT_bit_offset = DW_AT 0x0c

pattern DW_AT_bit_size = DW_AT 0x0d
pattern DW_AT_stmt_list = DW_AT 0x10
pattern DW_AT_low_pc = DW_AT 0x11
pattern DW_AT_high_pc = DW_AT 0x12
pattern DW_AT_language = DW_AT 0x13
pattern DW_AT_discr = DW_AT 0x15
pattern DW_AT_discr_value = DW_AT 0x16
pattern DW_AT_visibility = DW_AT 0x17
pattern DW_AT_import = DW_AT 0x18
pattern DW_AT_string_length = DW_AT 0x19
pattern DW_AT_common_reference = DW_AT 0x1a
pattern DW_AT_comp_dir = DW_AT 0x1b
pattern DW_AT_const_value = DW_AT 0x1c
pattern DW_AT_containing_type = DW_AT 0x1d
pattern DW_AT_default_value = DW_AT 0x1e
pattern DW_AT_inline = DW_AT 0x20
pattern DW_AT_is_optional = DW_AT 0x21
pattern DW_AT_lower_bound = DW_AT 0x22
pattern DW_AT_producer = DW_AT 0x25
pattern DW_AT_prototyped = DW_AT 0x27
pattern DW_AT_return_addr = DW_AT 0x2a
pattern DW_AT_start_scope = DW_AT 0x2c
pattern DW_AT_bit_stride = DW_AT 0x2e
pattern DW_AT_upper_bound = DW_AT 0x2f
pattern DW_AT_abstract_origin = DW_AT 0x31
pattern DW_AT_accessibility = DW_AT 0x32
pattern DW_AT_address_class = DW_AT 0x33
pattern DW_AT_artificial = DW_AT 0x34
pattern DW_AT_base_types = DW_AT 0x35
pattern DW_AT_calling_convention = DW_AT 0x36
pattern DW_AT_count = DW_AT 0x37
pattern DW_AT_data_member_location = DW_AT 0x38
pattern DW_AT_decl_column = DW_AT 0x39
pattern DW_AT_decl_file = DW_AT 0x3a
pattern DW_AT_decl_line = DW_AT 0x3b
pattern DW_AT_declaration = DW_AT 0x3c
pattern DW_AT_discr_list = DW_AT 0x3d
pattern DW_AT_encoding = DW_AT 0x3e
pattern DW_AT_external = DW_AT 0x3f
pattern DW_AT_frame_base = DW_AT 0x40
pattern DW_AT_friend = DW_AT 0x41
pattern DW_AT_identifier_case = DW_AT 0x42
pattern DW_AT_macro_info = DW_AT 0x43
pattern DW_AT_namelist_item = DW_AT 0x44
pattern DW_AT_priority = DW_AT 0x45
pattern DW_AT_segment = DW_AT 0x46
pattern DW_AT_specification = DW_AT 0x47
pattern DW_AT_static_link = DW_AT 0x48
pattern DW_AT_type = DW_AT 0x49
pattern DW_AT_use_location = DW_AT 0x4a
pattern DW_AT_variable_parameter = DW_AT 0x4b
pattern DW_AT_virtuality = DW_AT 0x4c
pattern DW_AT_vtable_elem_location = DW_AT 0x4d

pattern DW_AT_allocated = DW_AT 0x4e
pattern DW_AT_associated = DW_AT 0x4f
pattern DW_AT_data_location = DW_AT 0x50
pattern DW_AT_byte_stride = DW_AT 0x51
pattern DW_AT_entry_pc = DW_AT 0x52
pattern DW_AT_use_UTF8 = DW_AT 0x53
pattern DW_AT_extension = DW_AT 0x54
pattern DW_AT_ranges = DW_AT 0x55
pattern DW_AT_trampoline = DW_AT 0x56
pattern DW_AT_call_column = DW_AT 0x57
pattern DW_AT_call_file = DW_AT 0x58
pattern DW_AT_call_line = DW_AT 0x59
pattern DW_AT_description = DW_AT 0x5a
pattern DW_AT_binary_scale = DW_AT 0x5b
pattern DW_AT_decimal_scale = DW_AT 0x5c
pattern DW_AT_small = DW_AT 0x5d
pattern DW_AT_decimal_sign = DW_AT 0x5e
pattern DW_AT_digit_count = DW_AT 0x5f
pattern DW_AT_picture_string = DW_AT 0x60
pattern DW_AT_mutable = DW_AT 0x61
pattern DW_AT_threads_scaled = DW_AT 0x62
pattern DW_AT_explicit = DW_AT 0x63
pattern DW_AT_object_pointer = DW_AT 0x64
pattern DW_AT_endianity = DW_AT 0x65
pattern DW_AT_elemental = DW_AT 0x66
pattern DW_AT_pure = DW_AT 0x67
pattern DW_AT_recursive = DW_AT 0x68

pattern DW_AT_signature = DW_AT 0x69
pattern DW_AT_main_subprogram = DW_AT 0x6a
pattern DW_AT_data_bit_offset = DW_AT 0x6b
pattern DW_AT_const_expr = DW_AT 0x6c
pattern DW_AT_enum_class = DW_AT 0x6d
pattern DW_AT_linkage_name = DW_AT 0x6e

pattern DW_AT_string_length_bit_size = DW_AT 0x6f
pattern DW_AT_string_length_byte_size = DW_AT 0x70
pattern DW_AT_rank = DW_AT 0x71
pattern DW_AT_str_offsets_base = DW_AT 0x72
pattern DW_AT_addr_base = DW_AT 0x73
pattern DW_AT_rnglists_base = DW_AT 0x74
pattern DW_AT_dwo_id = DW_AT 0x75
pattern DW_AT_dwo_name = DW_AT 0x76
pattern DW_AT_reference = DW_AT 0x77
pattern DW_AT_rvalue_reference = DW_AT 0x78
pattern DW_AT_macros = DW_AT 0x79
pattern DW_AT_call_all_calls = DW_AT 0x7a
pattern DW_AT_call_all_source_calls = DW_AT 0x7b
pattern DW_AT_call_all_tail_calls = DW_AT 0x7c
pattern DW_AT_call_return_pc = DW_AT 0x7d
pattern DW_AT_call_value = DW_AT 0x7e
pattern DW_AT_call_origin = DW_AT 0x7f
pattern DW_AT_call_parameter = DW_AT 0x80
pattern DW_AT_call_pc = DW_AT 0x81
pattern DW_AT_call_tail_call = DW_AT 0x82
pattern DW_AT_call_target = DW_AT 0x83
pattern DW_AT_call_target_clobbered = DW_AT 0x84
pattern DW_AT_call_data_location = DW_AT 0x85
pattern DW_AT_call_data_value = DW_AT 0x86
pattern DW_AT_noreturn = DW_AT 0x87
pattern DW_AT_alignment = DW_AT 0x88
pattern DW_AT_export_symbols = DW_AT 0x89
pattern DW_AT_deleted = DW_AT 0x8a
pattern DW_AT_defaulted = DW_AT 0x8b
pattern DW_AT_loclists_base = DW_AT 0x8c

pattern DW_AT_MIPS_loop_begin = DW_AT 0x2002
pattern DW_AT_MIPS_tail_loop_begin = DW_AT 0x2003
pattern DW_AT_MIPS_epilog_begin = DW_AT 0x2004
pattern DW_AT_MIPS_loop_unroll_factor = DW_AT 0x2005
pattern DW_AT_MIPS_software_pipeline_depth = DW_AT 0x2006
pattern DW_AT_MIPS_linkage_name = DW_AT 0x2007
pattern DW_AT_MIPS_stride = DW_AT 0x2008
pattern DW_AT_MIPS_abstract_name = DW_AT 0x2009
pattern DW_AT_MIPS_clone_origin = DW_AT 0x200a
pattern DW_AT_MIPS_has_inlines = DW_AT 0x200b
pattern DW_AT_MIPS_stride_byte = DW_AT 0x200c
pattern DW_AT_MIPS_stride_elem = DW_AT 0x200d
pattern DW_AT_MIPS_ptr_dopetype = DW_AT 0x200e
pattern DW_AT_MIPS_allocatable_dopetype = DW_AT 0x200f
pattern DW_AT_MIPS_assumed_shape_dopetype = DW_AT 0x2010


pattern DW_AT_MIPS_assumed_size = DW_AT 0x2011

pattern DW_AT_sf_names = DW_AT 0x2101
pattern DW_AT_src_info = DW_AT 0x2102
pattern DW_AT_mac_info = DW_AT 0x2103
pattern DW_AT_src_coords = DW_AT 0x2104
pattern DW_AT_body_begin = DW_AT 0x2105
pattern DW_AT_body_end = DW_AT 0x2106
pattern DW_AT_GNU_vector = DW_AT 0x2107
pattern DW_AT_GNU_template_name = DW_AT 0x2110
pattern DW_AT_GNU_odr_signature = DW_AT 0x210f
pattern DW_AT_GNU_call_site_value = DW_AT 0x2111
pattern DW_AT_GNU_call_site_data_value = DW_AT 0x2112
pattern DW_AT_GNU_call_site_target = DW_AT 0x2113
pattern DW_AT_GNU_call_site_target_clobbered = DW_AT 0x2114
pattern DW_AT_GNU_tail_call = DW_AT 0x2115
pattern DW_AT_GNU_all_tail_call_sites = DW_AT 0x2116
pattern DW_AT_GNU_all_call_sites = DW_AT 0x2117
pattern DW_AT_GNU_all_source_call_sites = DW_AT 0x2118
pattern DW_AT_GNU_macros = DW_AT 0x2119

pattern DW_AT_GNU_dwo_name = DW_AT 0x2130
pattern DW_AT_GNU_dwo_id = DW_AT 0x2131
pattern DW_AT_GNU_ranges_base = DW_AT 0x2132
pattern DW_AT_GNU_addr_base = DW_AT 0x2133
pattern DW_AT_GNU_pubnames = DW_AT 0x2134
pattern DW_AT_GNU_pubtypes = DW_AT 0x2135
pattern DW_AT_GNU_discriminator = DW_AT 0x2136

pattern DW_AT_BORLAND_property_read = DW_AT 0x3b11
pattern DW_AT_BORLAND_property_write = DW_AT 0x3b12
pattern DW_AT_BORLAND_property_implements = DW_AT 0x3b13
pattern DW_AT_BORLAND_property_index = DW_AT 0x3b14
pattern DW_AT_BORLAND_property_default = DW_AT 0x3b15
pattern DW_AT_BORLAND_Delphi_unit = DW_AT 0x3b20
pattern DW_AT_BORLAND_Delphi_class = DW_AT 0x3b21
pattern DW_AT_BORLAND_Delphi_record = DW_AT 0x3b22
pattern DW_AT_BORLAND_Delphi_metaclass = DW_AT 0x3b23
pattern DW_AT_BORLAND_Delphi_constructor = DW_AT 0x3b24
pattern DW_AT_BORLAND_Delphi_destructor = DW_AT 0x3b25
pattern DW_AT_BORLAND_Delphi_anonymous_method = DW_AT 0x3b26
pattern DW_AT_BORLAND_Delphi_interface = DW_AT 0x3b27
pattern DW_AT_BORLAND_Delphi_ABI = DW_AT 0x3b28
pattern DW_AT_BORLAND_Delphi_return = DW_AT 0x3b29
pattern DW_AT_BORLAND_Delphi_frameptr = DW_AT 0x3b30
pattern DW_AT_BORLAND_closure = DW_AT 0x3b31

pattern DW_AT_LLVM_include_path = DW_AT 0x3e00
pattern DW_AT_LLVM_config_macros = DW_AT 0x3e01
pattern DW_AT_LLVM_isysroot = DW_AT 0x3e02
pattern DW_AT_LLVM_tag_offset = DW_AT 0x3e03

pattern DW_AT_APPLE_optimized = DW_AT 0x3fe1
pattern DW_AT_APPLE_flags = DW_AT 0x3fe2
pattern DW_AT_APPLE_isa = DW_AT 0x3fe3
pattern DW_AT_APPLE_block = DW_AT 0x3fe4
pattern DW_AT_APPLE_major_runtime_vers = DW_AT 0x3fe5
pattern DW_AT_APPLE_runtime_class = DW_AT 0x3fe6
pattern DW_AT_APPLE_omit_frame_ptr = DW_AT 0x3fe7
pattern DW_AT_APPLE_property_name = DW_AT 0x3fe8
pattern DW_AT_APPLE_property_getter = DW_AT 0x3fe9
pattern DW_AT_APPLE_property_setter = DW_AT 0x3fea
pattern DW_AT_APPLE_property_attribute = DW_AT 0x3feb
pattern DW_AT_APPLE_objc_complete_type = DW_AT 0x3fec
pattern DW_AT_APPLE_property = DW_AT 0x3fed

dw_at_names :: [(String, DW_AT)]
dw_at_names =
  [ ("DW_AT_sibling", DW_AT_sibling)
  , ("DW_AT_location", DW_AT_location)
  , ("DW_AT_name", DW_AT_name)
  , ("DW_AT_ordering", DW_AT_ordering)
  , ("DW_AT_byte_size", DW_AT_byte_size)
  , ("DW_AT_bit_offset", DW_AT_bit_offset)
  , ("DW_AT_bit_size", DW_AT_bit_size)
  , ("DW_AT_stmt_list", DW_AT_stmt_list)
  , ("DW_AT_low_pc", DW_AT_low_pc)
  , ("DW_AT_high_pc", DW_AT_high_pc)
  , ("DW_AT_language", DW_AT_language)
  , ("DW_AT_discr", DW_AT_discr)
  , ("DW_AT_discr_value", DW_AT_discr_value)
  , ("DW_AT_visibility", DW_AT_visibility)
  , ("DW_AT_import", DW_AT_import)
  , ("DW_AT_string_length", DW_AT_string_length)
  , ("DW_AT_common_reference", DW_AT_common_reference)
  , ("DW_AT_comp_dir", DW_AT_comp_dir)
  , ("DW_AT_const_value", DW_AT_const_value)
  , ("DW_AT_containing_type", DW_AT_containing_type)
  , ("DW_AT_default_value", DW_AT_default_value)
  , ("DW_AT_inline", DW_AT_inline)
  , ("DW_AT_is_optional", DW_AT_is_optional)
  , ("DW_AT_lower_bound", DW_AT_lower_bound)
  , ("DW_AT_producer", DW_AT_producer)
  , ("DW_AT_prototyped", DW_AT_prototyped)
  , ("DW_AT_return_addr", DW_AT_return_addr)
  , ("DW_AT_start_scope", DW_AT_start_scope)
  , ("DW_AT_bit_stride", DW_AT_bit_stride)
  , ("DW_AT_upper_bound", DW_AT_upper_bound)
  , ("DW_AT_abstract_origin", DW_AT_abstract_origin)
  , ("DW_AT_accessibility", DW_AT_accessibility)
  , ("DW_AT_address_class", DW_AT_address_class)
  , ("DW_AT_artificial", DW_AT_artificial)
  , ("DW_AT_base_types", DW_AT_base_types)
  , ("DW_AT_calling_convention", DW_AT_calling_convention)
  , ("DW_AT_count", DW_AT_count)
  , ("DW_AT_data_member_location", DW_AT_data_member_location)
  , ("DW_AT_decl_column", DW_AT_decl_column)
  , ("DW_AT_decl_file", DW_AT_decl_file)
  , ("DW_AT_decl_line", DW_AT_decl_line)
  , ("DW_AT_declaration", DW_AT_declaration)
  , ("DW_AT_discr_list", DW_AT_discr_list)
  , ("DW_AT_encoding", DW_AT_encoding)
  , ("DW_AT_external", DW_AT_external)
  , ("DW_AT_frame_base", DW_AT_frame_base)
  , ("DW_AT_friend", DW_AT_friend)
  , ("DW_AT_identifier_case", DW_AT_identifier_case)
  , ("DW_AT_macro_info", DW_AT_macro_info)
  , ("DW_AT_namelist_item", DW_AT_namelist_item)
  , ("DW_AT_priority", DW_AT_priority)
  , ("DW_AT_segment", DW_AT_segment)
  , ("DW_AT_specification", DW_AT_specification)
  , ("DW_AT_static_link", DW_AT_static_link)
  , ("DW_AT_type", DW_AT_type)
  , ("DW_AT_use_location", DW_AT_use_location)
  , ("DW_AT_variable_parameter", DW_AT_variable_parameter)
  , ("DW_AT_virtuality", DW_AT_virtuality)
  , ("DW_AT_vtable_elem_location", DW_AT_vtable_elem_location)
  , ("DW_AT_allocated", DW_AT_allocated)
  , ("DW_AT_associated", DW_AT_associated)
  , ("DW_AT_data_location", DW_AT_data_location)
  , ("DW_AT_byte_stride", DW_AT_byte_stride)
  , ("DW_AT_entry_pc", DW_AT_entry_pc)
  , ("DW_AT_use_UTF8", DW_AT_use_UTF8)
  , ("DW_AT_extension", DW_AT_extension)
  , ("DW_AT_ranges", DW_AT_ranges)
  , ("DW_AT_trampoline", DW_AT_trampoline)
  , ("DW_AT_call_column", DW_AT_call_column)
  , ("DW_AT_call_file", DW_AT_call_file)
  , ("DW_AT_call_line", DW_AT_call_line)
  , ("DW_AT_description", DW_AT_description)
  , ("DW_AT_binary_scale", DW_AT_binary_scale)
  , ("DW_AT_decimal_scale", DW_AT_decimal_scale)
  , ("DW_AT_small", DW_AT_small)
  , ("DW_AT_decimal_sign", DW_AT_decimal_sign)
  , ("DW_AT_digit_count", DW_AT_digit_count)
  , ("DW_AT_picture_string", DW_AT_picture_string)
  , ("DW_AT_mutable", DW_AT_mutable)
  , ("DW_AT_threads_scaled", DW_AT_threads_scaled)
  , ("DW_AT_explicit", DW_AT_explicit)
  , ("DW_AT_object_pointer", DW_AT_object_pointer)
  , ("DW_AT_endianity", DW_AT_endianity)
  , ("DW_AT_elemental", DW_AT_elemental)
  , ("DW_AT_pure", DW_AT_pure)
  , ("DW_AT_recursive", DW_AT_recursive)
  , ("DW_AT_signature", DW_AT_signature)
  , ("DW_AT_main_subprogram", DW_AT_main_subprogram)
  , ("DW_AT_data_bit_offset", DW_AT_data_bit_offset)
  , ("DW_AT_const_expr", DW_AT_const_expr)
  , ("DW_AT_enum_class", DW_AT_enum_class)
  , ("DW_AT_linkage_name", DW_AT_linkage_name)

  , ("DW_AT_string_length_bit_size", DW_AT_string_length_bit_size)
  , ("DW_AT_string_length_byte_size", DW_AT_string_length_byte_size)
  , ("DW_AT_rank", DW_AT_rank)
  , ("DW_AT_str_offsets_base", DW_AT_str_offsets_base)
  , ("DW_AT_addr_base", DW_AT_addr_base)
  , ("DW_AT_rnglists_base", DW_AT_rnglists_base)
  , ("DW_AT_dwo_id", DW_AT_dwo_id)
  , ("DW_AT_dwo_name", DW_AT_dwo_name)
  , ("DW_AT_reference", DW_AT_reference)
  , ("DW_AT_rvalue_reference", DW_AT_rvalue_reference)
  , ("DW_AT_macros", DW_AT_macros)
  , ("DW_AT_call_all_calls", DW_AT_call_all_calls)
  , ("DW_AT_call_all_source_calls", DW_AT_call_all_source_calls)
  , ("DW_AT_call_all_tail_calls", DW_AT_call_all_tail_calls)
  , ("DW_AT_call_return_pc", DW_AT_call_return_pc)
  , ("DW_AT_call_value", DW_AT_call_value)
  , ("DW_AT_call_origin", DW_AT_call_origin)
  , ("DW_AT_call_parameter", DW_AT_call_parameter)
  , ("DW_AT_call_pc", DW_AT_call_pc)
  , ("DW_AT_call_tail_call", DW_AT_call_tail_call)
  , ("DW_AT_call_target", DW_AT_call_target)
  , ("DW_AT_call_target_clobbered", DW_AT_call_target_clobbered)
  , ("DW_AT_call_data_location", DW_AT_call_data_location)
  , ("DW_AT_call_data_value", DW_AT_call_data_value)
  , ("DW_AT_noreturn", DW_AT_noreturn)
  , ("DW_AT_alignment", DW_AT_alignment)
  , ("DW_AT_export_symbols", DW_AT_export_symbols)
  , ("DW_AT_deleted", DW_AT_deleted)
  , ("DW_AT_defaulted", DW_AT_defaulted)
  , ("DW_AT_loclists_base", DW_AT_loclists_base)

  , ("DW_AT_MIPS_loop_begin", DW_AT_MIPS_loop_begin)
  , ("DW_AT_MIPS_tail_loop_begin", DW_AT_MIPS_tail_loop_begin)
  , ("DW_AT_MIPS_epilog_begin", DW_AT_MIPS_epilog_begin)
  , ("DW_AT_MIPS_loop_unroll_factor", DW_AT_MIPS_loop_unroll_factor)
  , ("DW_AT_MIPS_software_pipeline_depth", DW_AT_MIPS_software_pipeline_depth)
  , ("DW_AT_MIPS_linkage_name", DW_AT_MIPS_linkage_name)
  , ("DW_AT_MIPS_stride", DW_AT_MIPS_stride)
  , ("DW_AT_MIPS_abstract_name", DW_AT_MIPS_abstract_name)
  , ("DW_AT_MIPS_clone_origin", DW_AT_MIPS_clone_origin)
  , ("DW_AT_MIPS_has_inlines", DW_AT_MIPS_has_inlines)
  , ("DW_AT_MIPS_stride_byte", DW_AT_MIPS_stride_byte)
  , ("DW_AT_MIPS_stride_elem", DW_AT_MIPS_stride_elem)
  , ("DW_AT_MIPS_ptr_dopetype", DW_AT_MIPS_ptr_dopetype)
  , ("DW_AT_MIPS_allocatable_dopetype", DW_AT_MIPS_allocatable_dopetype)
  , ("DW_AT_MIPS_assumed_shape_dopetype", DW_AT_MIPS_assumed_shape_dopetype)


  , ("DW_AT_MIPS_assumed_size", DW_AT_MIPS_assumed_size)

  , ("DW_AT_sf_names", DW_AT_sf_names)
  , ("DW_AT_src_info", DW_AT_src_info)
  , ("DW_AT_mac_info", DW_AT_mac_info)
  , ("DW_AT_src_coords", DW_AT_src_coords)
  , ("DW_AT_body_begin", DW_AT_body_begin)
  , ("DW_AT_body_end", DW_AT_body_end)
  , ("DW_AT_GNU_vector", DW_AT_GNU_vector)
  , ("DW_AT_GNU_template_name", DW_AT_GNU_template_name)
  , ("DW_AT_GNU_odr_signature", DW_AT_GNU_odr_signature)
  , ("DW_AT_GNU_call_site_value", DW_AT_GNU_call_site_value)
  , ("DW_AT_GNU_call_site_data_value", DW_AT_GNU_call_site_data_value)
  , ("DW_AT_GNU_call_site_target", DW_AT_GNU_call_site_target)
  , ("DW_AT_GNU_call_site_target_clobbered", DW_AT_GNU_call_site_target_clobbered)
  , ("DW_AT_GNU_tail_call", DW_AT_GNU_tail_call)
  , ("DW_AT_GNU_all_tail_call_sites", DW_AT_GNU_all_tail_call_sites)
  , ("DW_AT_GNU_all_call_sites", DW_AT_GNU_all_call_sites)
  , ("DW_AT_GNU_all_source_call_sites", DW_AT_GNU_all_source_call_sites)
  , ("DW_AT_GNU_macros", DW_AT_GNU_macros)

  , ("DW_AT_GNU_dwo_name", DW_AT_GNU_dwo_name)
  , ("DW_AT_GNU_dwo_id", DW_AT_GNU_dwo_id)
  , ("DW_AT_GNU_ranges_base", DW_AT_GNU_ranges_base)
  , ("DW_AT_GNU_addr_base", DW_AT_GNU_addr_base)
  , ("DW_AT_GNU_pubnames", DW_AT_GNU_pubnames)
  , ("DW_AT_GNU_pubtypes", DW_AT_GNU_pubtypes)
  , ("DW_AT_GNU_discriminator", DW_AT_GNU_discriminator)

  , ("DW_AT_BORLAND_property_read", DW_AT_BORLAND_property_read)
  , ("DW_AT_BORLAND_property_write", DW_AT_BORLAND_property_write)
  , ("DW_AT_BORLAND_property_implements", DW_AT_BORLAND_property_implements)
  , ("DW_AT_BORLAND_property_index", DW_AT_BORLAND_property_index)
  , ("DW_AT_BORLAND_property_default", DW_AT_BORLAND_property_default)
  , ("DW_AT_BORLAND_Delphi_unit", DW_AT_BORLAND_Delphi_unit)
  , ("DW_AT_BORLAND_Delphi_class", DW_AT_BORLAND_Delphi_class)
  , ("DW_AT_BORLAND_Delphi_record", DW_AT_BORLAND_Delphi_record)
  , ("DW_AT_BORLAND_Delphi_metaclass", DW_AT_BORLAND_Delphi_metaclass)
  , ("DW_AT_BORLAND_Delphi_constructor", DW_AT_BORLAND_Delphi_constructor)
  , ("DW_AT_BORLAND_Delphi_destructor", DW_AT_BORLAND_Delphi_destructor)
  , ("DW_AT_BORLAND_Delphi_anonymous_method", DW_AT_BORLAND_Delphi_anonymous_method)
  , ("DW_AT_BORLAND_Delphi_interface", DW_AT_BORLAND_Delphi_interface)
  , ("DW_AT_BORLAND_Delphi_ABI", DW_AT_BORLAND_Delphi_ABI)
  , ("DW_AT_BORLAND_Delphi_return", DW_AT_BORLAND_Delphi_return)
  , ("DW_AT_BORLAND_Delphi_frameptr", DW_AT_BORLAND_Delphi_frameptr)
  , ("DW_AT_BORLAND_closure", DW_AT_BORLAND_closure)

  , ("DW_AT_LLVM_include_path", DW_AT_LLVM_include_path)
  , ("DW_AT_LLVM_config_macros", DW_AT_LLVM_config_macros)
  , ("DW_AT_LLVM_isysroot", DW_AT_LLVM_isysroot)
  , ("DW_AT_LLVM_tag_offset", DW_AT_LLVM_tag_offset)

  , ("DW_AT_APPLE_optimized", DW_AT_APPLE_optimized)
  , ("DW_AT_APPLE_flags", DW_AT_APPLE_flags)
  , ("DW_AT_APPLE_isa", DW_AT_APPLE_isa)
  , ("DW_AT_APPLE_block", DW_AT_APPLE_block)
  , ("DW_AT_APPLE_major_runtime_vers", DW_AT_APPLE_major_runtime_vers)
  , ("DW_AT_APPLE_runtime_class", DW_AT_APPLE_runtime_class)
  , ("DW_AT_APPLE_omit_frame_ptr", DW_AT_APPLE_omit_frame_ptr)
  , ("DW_AT_APPLE_property_name", DW_AT_APPLE_property_name)
  , ("DW_AT_APPLE_property_getter", DW_AT_APPLE_property_getter)
  , ("DW_AT_APPLE_property_setter", DW_AT_APPLE_property_setter)
  , ("DW_AT_APPLE_property_attribute", DW_AT_APPLE_property_attribute)
  , ("DW_AT_APPLE_objc_complete_type", DW_AT_APPLE_objc_complete_type)
  , ("DW_AT_APPLE_property", DW_AT_APPLE_property)
  ]

dw_at_name_map :: Map.Map DW_AT String
dw_at_name_map = Map.fromList [ (v, nm) | (nm,v) <- dw_at_names ]

instance Show DW_AT where
  showsPrec p (DW_AT a) =
    case Map.lookup (DW_AT a) dw_at_name_map of
      Just r -> showString r
      Nothing -> showParen (p > 10) $ showString "DW_AT 0x" . showHex a
