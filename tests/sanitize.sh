#!/bin/sh
# Sanitize dwarf-dump / llvm-dwarfdump output for environment-independent
# golden comparison. Replaces absolute file paths and memory addresses with
# stable placeholders so golden files work across build environments (Docker,
# CI, local) regardless of compilation directory or binary layout.
#
# Uses perl rather than sed for portability across BSD (macOS) and GNU/Linux.
exec perl -pe '
  s|^[^\t]*:\t(file format )|<binary>:\t$1|;
  s|(DW_AT_comp_dir)\t.*|$1\t("<path>")|;
  s|(DW_AT_decl_file)\t.*|$1\t("<path>")|;
  s|(DW_AT_call_file)\t.*|$1\t("<path>")|;
  s|(DW_AT_low_pc)\t.*|$1\t(<addr>)|;
  s|(DW_AT_high_pc)\t.*|$1\t(<addr>)|;
  s|(DW_AT_entry_pc)\t.*|$1\t(<addr>)|;
  s|(DW_AT_location)\t.*|$1\t(<addr>)|;
  s|(DW_AT_frame_base)\t.*|$1\t(<addr>)|;
'
