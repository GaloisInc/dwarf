{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- |
-- DWARF Call frame instruction datatypes and parsing.
--
-- The pretty printer is architecture specific and we only provide a function for
-- pretty printing x86 currently.  Additional architecture support is welcome.
module Data.Dwarf.CFA
  ( CallFrameReg (..),
    CallFrameExpr (..),
    CallFrameAddr (..),
    DW_CFA (..),
    CallFramePPCtx (..),
    ppCFA,
    parseCallFrameInstruction,
    parseCallFrameInstructions,
    ppX86CallFrameReg,
  )
where

import Data.Binary.Get (Get, getWord8)
import Data.Bits (shiftR, (.&.))
import qualified Data.ByteString as B
import Data.Dwarf.Internals
import Data.Dwarf.OP
import Data.Dwarf.Reader
import Data.Int (Int64)
import Data.Word (Word16, Word32, Word64, Word8)
import Numeric (showHex)

-- | A register in a call frame.
newtype CallFrameReg = CallFrameReg Word64
  deriving (Show)

getCallFrameReg :: Get CallFrameReg
getCallFrameReg = CallFrameReg <$> getULEB128

-- | This denotes a DWARF expression
newtype CallFrameExpr = CallFrameExpr B.ByteString
  deriving (Show)

getCallFrameExpr :: Get CallFrameExpr
getCallFrameExpr = CallFrameExpr <$> getByteStringLen getULEB128

-- | Represents a target address.
newtype CallFrameAddr = CallFrameAddr Word64
  deriving (Num)

instance Show CallFrameAddr where
  showsPrec _ (CallFrameAddr a) = showString "0x" . showHex a

-- | A call frame instruction.
--
-- This is used to compute the call frame information table as
-- described in the Dwarf version 5 standard section 6.4
data DW_CFA
  = -- | @DW_CFA_set_loc addr@ copies the current row to a new
    -- row, and sets the new location to @addr@.
    DW_CFA_set_loc !CallFrameAddr
  | -- | `DW_CFA_advance_loc delta` copies the current row to a new
    -- row, and adds @delta * code_alignment_factor@ to the new row
    -- location.
    --
    -- The location should be at less than `2^6` (64) so
    -- the delta can be encoded in the opcode.
    DW_CFA_advance_loc !Word8
  | -- | `DW_CFA_advance_loc1 delta` performs the same operation
    -- as `DW_CFA_advance_loc delta` but the delta is 8-bits.
    DW_CFA_advance_loc1 !Word8
  | -- | `DW_CFA_advance_loc2 delta` performs the same operation
    -- as `DW_CFA_advance_loc delta` but the delta is 16-bits.
    DW_CFA_advance_loc2 !Word16
  | -- | `DW_CFA_advance_loc4 delta` performs the same operation
    -- as `DW_CFA_advance_loc delta` but the delta is 32-bits.
    DW_CFA_advance_loc4 !Word32
  | -- | Defines the current CFA rule to use the register and offset.
    DW_CFA_def_cfa !CallFrameReg !Word64
  | -- | Defines the current CFA rule to use the register and offst.
    --
    -- This is the same as `DW_CFA_def_cfa` except the offset is
    -- signed and factored.  The actual offset is
    -- `offset * data_alignment_factor`.
    DW_CFA_def_cfa_sf !CallFrameReg !Int64
  | -- | Defines the current CFA rule to use the provided register
    -- and keep the offset.
    DW_CFA_def_cfa_register !CallFrameReg
  | -- | Defines the current CFA rule to use the keep the current
    -- register and use the new offset.
    DW_CFA_def_cfa_offset !Word64
  | -- | Defines the current CFA rule to use the keep the current
    -- register and use the new signed factored offset.  The actual
    -- offset is set to `offset * data_alignment_factor`.
    DW_CFA_def_cfa_offset_sf !Int64
  | -- | Defines the current rule CFA to be the expression denoted
    -- by the Dwarf expression.
    DW_CFA_def_cfa_expression !CallFrameExpr
  | -- 6.4.2.3 Register rule instructions

    -- | `DW_CFA_undefined r` to be `undefined`.
    DW_CFA_undefined !CallFrameReg
  | -- | @DW_CFA_same_value r@ defines @r@ to be @same value@.
    DW_CFA_same_value !CallFrameReg
  | -- | @DW_CFA_offset r o@ defines @r@ to be
    -- @offset(o * data_alignment_factor)@.
    --
    -- Note. In this encoding, the register index must be less than
    -- @2^6@.
    DW_CFA_offset !CallFrameReg !Word64
  | -- | @DW_CFA_offset_extended r o@ defines @r@ to be
    -- @offset(o * data_alignment_factor)@.
    --
    -- This is the same as `DW_CFA_offset` except for the encoding.
    DW_CFA_offset_extended !CallFrameReg !Word64
  | -- | @DW_CFA_offset_extended_sf r o@ defines @r@ to be
    -- `offset(o * data_alignment_factor)`.
    --
    -- This is the same as `DW_CFA_offset` except the offset is
    -- signed and extended.
    DW_CFA_offset_extended_sf !CallFrameReg !Int64
  | -- | @DW_CFA_val_offset r o@ sets the rule for @r@ to be
    -- `val_offset(o * data_alignment_factor).
    DW_CFA_val_offset !CallFrameReg !Word64
  | -- | `DW_CFA_val_offset r o` sets the rule for @r@ to be
    -- `val_offset(o * data_alignment_factor).
    --
    -- This is the same as `DW_CFA_val_offset` except the value is
    -- signed.
    DW_CFA_val_offset_sf !CallFrameReg !Int64
  | -- | `DW_CFA_register rs rd` sets the rule
    -- in register @rs@ to be `register(rd)`.
    DW_CFA_register !CallFrameReg !CallFrameReg
  | -- | `DW_CFA_expression r e` sets the rule for @r@ to be an
    -- `expression(e) where @e@ is evaluated with the CFA pushed to
    -- the DWARF evaluation stack.
    DW_CFA_expression !CallFrameReg !CallFrameExpr
  | -- | `DW_CFA_expression r e` sets the rule for @r@ to be an
    -- `val_expression(e) where @e@ is evaluated with the CFA pushed
    -- to the DWARF evaluation stack.
    DW_CFA_val_expression !CallFrameReg !CallFrameExpr
  | -- | This assigns the register to the value assigned by the
    -- initial instructions in the CIE.
    --
    -- Note. In this encoding, the register index must be less than
    -- `2^6`.
    DW_CFA_restore !CallFrameReg
  | -- | This assigns the register to the value assigned by the
    -- initial instructions in the CIE.
    DW_CFA_restore_extended !CallFrameReg
  | -- Row State Instructions

    -- | This pushes the current register rules to the stack.
    DW_CFA_remember_state
  | -- | This pps the rules off the stack and puts them in the
    -- current rows.
    DW_CFA_restore_state
  | -- Padding instruction

    -- | This instruction has no operands and does nothing.  It is
    -- used for padding.
    DW_CFA_nop
  | -- GNU extension

    -- | This specifies the total size of arguments that have been
    -- pushed to stack.
    DW_CFA_GNU_args_size !Word64
  deriving (Show)

getDW_CFA :: Endianess -> TargetSize -> Get DW_CFA
getDW_CFA end tgt = do
  tag <- getWord8
  -- Handle instuctions encoded using high tow bits.
  case tag `shiftR` 6 of
    0x1 -> pure $ DW_CFA_advance_loc (tag .&. 0x3f)
    0x2 -> DW_CFA_offset (CallFrameReg (fromIntegral (tag .&. 0x3f))) <$> getULEB128
    0x3 -> pure $ DW_CFA_restore (CallFrameReg (fromIntegral (tag .&. 0x3f)))
    0x0 ->
      case tag .&. 0x3f of
        0x00 -> pure DW_CFA_nop
        0x01 -> DW_CFA_set_loc <$> (CallFrameAddr <$> getTargetAddress end tgt)
        0x02 -> DW_CFA_advance_loc1 <$> getWord8
        0x03 -> DW_CFA_advance_loc2 <$> derGetW16 end
        0x04 -> DW_CFA_advance_loc4 <$> derGetW32 end
        0x05 -> DW_CFA_offset_extended <$> getCallFrameReg <*> getULEB128
        0x06 -> DW_CFA_restore_extended <$> getCallFrameReg
        0x07 -> DW_CFA_undefined <$> getCallFrameReg
        0x08 -> DW_CFA_same_value <$> getCallFrameReg
        0x09 -> DW_CFA_register <$> getCallFrameReg <*> getCallFrameReg
        0x0a -> pure DW_CFA_remember_state
        0x0b -> pure DW_CFA_restore_state
        0x0c -> DW_CFA_def_cfa <$> getCallFrameReg <*> getULEB128
        0x0d -> DW_CFA_def_cfa_register <$> getCallFrameReg
        0x0e -> DW_CFA_def_cfa_offset <$> getULEB128
        0x0f -> DW_CFA_def_cfa_expression <$> getCallFrameExpr
        0x10 -> DW_CFA_expression <$> getCallFrameReg <*> getCallFrameExpr
        0x11 -> DW_CFA_offset_extended_sf <$> getCallFrameReg <*> getSLEB128
        0x12 -> DW_CFA_def_cfa_sf <$> getCallFrameReg <*> getSLEB128
        0x13 -> DW_CFA_def_cfa_offset_sf <$> getSLEB128
        0x14 -> DW_CFA_val_offset <$> getCallFrameReg <*> getULEB128
        0x15 -> DW_CFA_val_offset_sf <$> getCallFrameReg <*> getSLEB128
        0x16 -> DW_CFA_val_expression <$> getCallFrameReg <*> getCallFrameExpr
        --        0x29 ->
        0x2e -> DW_CFA_GNU_args_size <$> getULEB128
        _ -> fail $ "Invalid CFA tag: " <> showHex (tag `shiftR` 6) " " <> showHex (tag .&. 0x3f) ""
    _ -> fail $ "Invalid CFA tag: " <> showHex (tag `shiftR` 6) " " <> showHex (tag .&. 0x3f) ""

-- | Parse a single
parseCallFrameInstruction ::
  Endianess ->
  TargetSize ->
  B.ByteString ->
  Either (Int64, String) (B.ByteString, Int64, DW_CFA)
parseCallFrameInstruction end tgt = tryStrictGet (getDW_CFA end tgt)

-- | Parse a ByteString into a sequence of call frame instructions.
--
-- If it fails it returns the instructionsit could, the offset of the
-- start of the instruction that failed, and a message.
parseCallFrameInstructions ::
  Endianess ->
  TargetSize ->
  B.ByteString ->
  Either ([DW_CFA], Int, String) [DW_CFA]
parseCallFrameInstructions end tgt b =
  case tryGetUntilDone (getDW_CFA end tgt) b of
    Left (p, o, msg) -> Left (p, fromIntegral o, msg)
    Right r -> Right r

-- | Information needed to pretty print a call frame operation.
data CallFramePPCtx = CallFramePPCtx
  { -- | Data alignment factor
    ppDataAlignment :: !Int64,
    -- | Reader for endianess, targetsize, etc.
    ppReader :: !Reader,
    -- | Register pretty printer
    ppReg :: !(Word64 -> String)
  }

class CFAArg a where
  ppArg ::
    -- | Data alignment factor
    CallFramePPCtx ->
    a ->
    String

instance CFAArg CallFrameAddr where
  ppArg _ (CallFrameAddr x) = showHex x ""

instance CFAArg CallFrameReg where
  ppArg ctx (CallFrameReg r) = ppReg ctx r

instance CFAArg Word8 where
  ppArg _ = show

instance CFAArg Word16 where
  ppArg _ = show

instance CFAArg Word32 where
  ppArg _ = show

instance CFAArg Word64 where
  ppArg _ = show

instance CFAArg Int64 where
  ppArg _ = show

ppOp :: CallFramePPCtx -> DW_OP -> String
ppOp ctx op =
  case op of
    DW_OP_breg r o ->
      let reg = ppReg ctx (fromIntegral r)
          oval
            | o >= 0 = "+" <> show o
            | otherwise = show o
       in "DW_OP_breg" <> show r <> " " <> reg <> oval
    DW_OP_lit x -> "DW_OP_lit" <> show x
    DW_OP_plus_uconst x -> "DW_OP_plus_uconst 0x" <> showHex x ""
    _ -> show op

instance CFAArg CallFrameExpr where
  ppArg ctx (CallFrameExpr bytes) =
    case parseDW_OPs (ppReader ctx) bytes of
      Left _ -> show bytes
      Right [] -> ""
      Right (s : l) -> ppOp ctx s <> foldr (\h r -> ", " <> ppOp ctx h <> r) "" l

-- | Pretty print a call frame register
ppX86CallFrameReg :: Word64 -> String
ppX86CallFrameReg r =
  case r of
    0 -> "RAX"
    1 -> "RDX"
    2 -> "RCX"
    3 -> "RBX"
    4 -> "RSI"
    5 -> "RDI"
    6 -> "RBP"
    7 -> "RSP"
    16 -> "RIP"
    _ | 17 <= r && r <= 32 -> "XMM" ++ show (r - 17)
    _ -> "R" ++ show r

-- | Pretty print a CFA in the format generated by llvm-dwarfdump
ppCFA ::
  CallFramePPCtx ->
  DW_CFA ->
  String
ppCFA opts cfa = do
  let daf = ppDataAlignment opts
  let pp :: CFAArg a => a -> String
      pp = ppArg opts
  case cfa of
    DW_CFA_set_loc a -> "DW_CFA_set_loc: " ++ pp a
    DW_CFA_advance_loc x -> "DW_CFA_advance_loc: " ++ pp x
    DW_CFA_advance_loc1 x -> "DW_CFA_advance_loc1: " ++ pp x
    DW_CFA_advance_loc2 x -> "DW_CFA_advance_loc2: " ++ pp x
    DW_CFA_advance_loc4 x -> "DW_CFA_advance_loc4: " ++ pp x
    DW_CFA_def_cfa r o -> "DW_CFA_def_cfa: " <> pp r <> " +" ++ show o
    DW_CFA_def_cfa_sf r o -> "DW_CFA_def_cfa_sf: " ++ pp r ++ " " ++ pp o
    DW_CFA_def_cfa_register r -> "DW_CFA_def_cfa_register: " ++ pp r
    DW_CFA_def_cfa_offset o -> "DW_CFA_def_cfa_offset: +" ++ pp o
    DW_CFA_def_cfa_offset_sf o -> "DW_CFA_def_cfa_offset_sf: " <> show (toInteger daf * toInteger o)
    DW_CFA_def_cfa_expression e -> "DW_CFA_def_cfa_expression: " ++ pp e
    DW_CFA_undefined r -> "DW_CFA_undefined: " ++ pp r
    DW_CFA_same_value r -> "DW_CFA_same_value: " ++ pp r
    DW_CFA_offset r o -> "DW_CFA_offset: " <> pp r <> " " <> show (toInteger daf * toInteger o)
    DW_CFA_offset_extended r o -> "DW_CFA_offset_extended: " ++ pp r ++ " " <> show (toInteger daf * toInteger o)
    DW_CFA_offset_extended_sf r o -> "DW_CFA_offset_extended_sf: " <> pp r <> " " <> show (toInteger daf * toInteger o)
    DW_CFA_val_offset r o -> "DW_CFA_val_offset: " <> pp r <> " " <> pp o
    DW_CFA_val_offset_sf r o -> "DW_CFA_val_offset_sf: " <> pp r <> " " <> pp o
    DW_CFA_register x y -> "DW_CFA_register: " <> pp x <> " " <> pp y
    DW_CFA_expression r e -> "DW_CFA_expression: " <> pp r <> " " <> pp e
    DW_CFA_val_expression r e -> "DW_CFA_val_expression: " <> pp r <> " " <> pp e
    DW_CFA_restore r -> "DW_CFA_restore: " <> pp r
    DW_CFA_restore_extended r -> "DW_CFA_restore_extended: " <> pp r
    DW_CFA_remember_state -> "DW_CFA_remember_state:"
    DW_CFA_restore_state -> "DW_CFA_restore_state:"
    DW_CFA_nop -> "DW_CFA_nop:"
    DW_CFA_GNU_args_size sz -> "DW_CFA_GNU_args_size: +" <> pp sz
