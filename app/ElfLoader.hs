{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
module ElfLoader (loadDwarfFromElf) where

import qualified Data.ByteString as B
import           Data.Dwarf (Endianess(..), Sections, mkSections)
import qualified Data.ElfEdit as Elf

-- | Load DWARF sections from an ELF file, returning
-- (file-format string, endianness, sections).
loadDwarfFromElf :: FilePath -> IO (Either String (String, Endianess, Sections))
loadDwarfFromElf path = do
  contents <- B.readFile path
  case Elf.parseElf contents of
    Elf.Elf32Res warnings elf
      | null warnings -> return $ Right
          ( getFileFormat32 elf
          , elfEndianess elf
          , extractSections32 elf
          )
      | otherwise -> return $ Left $ "ELF parsing warnings: " ++ show warnings
    Elf.Elf64Res warnings elf
      | null warnings -> return $ Right
          ( getFileFormat64 elf
          , elfEndianess elf
          , extractSections64 elf
          )
      | otherwise -> return $ Left $ "ELF parsing warnings: " ++ show warnings
    Elf.ElfHeaderError offset err ->
      return $ Left $ "ELF header error at " ++ show offset ++ ": " ++ show err

-- | Convert ELF data encoding to DWARF endianness.
elfEndianess :: Elf.Elf w -> Endianess
elfEndianess elf = case Elf.elfData elf of
  Elf.ELFDATA2LSB -> LittleEndian
  Elf.ELFDATA2MSB -> BigEndian

-- | Get file format string for a 64-bit ELF.
getFileFormat64 :: Elf.Elf 64 -> String
getFileFormat64 elf =
  case Elf.elfMachine elf of
    Elf.EM_X86_64  -> "elf64-x86-64"
    Elf.EM_AARCH64 -> "elf64-littleaarch64"
    Elf.EM_PPC64   -> case Elf.elfData elf of
                        Elf.ELFDATA2LSB -> "elf64-powerpcle"
                        Elf.ELFDATA2MSB -> "elf64-powerpc"
    _              -> "elf64-unknown"

-- | Get file format string for a 32-bit ELF.
getFileFormat32 :: Elf.Elf 32 -> String
getFileFormat32 elf =
  case Elf.elfMachine elf of
    Elf.EM_386 -> "elf32-i386"
    Elf.EM_ARM -> case Elf.elfData elf of
                    Elf.ELFDATA2LSB -> "elf32-littlearm"
                    Elf.ELFDATA2MSB -> "elf32-bigarm"
    Elf.EM_PPC -> case Elf.elfData elf of
                    Elf.ELFDATA2LSB -> "elf32-powerpcle"
                    Elf.ELFDATA2MSB -> "elf32-powerpc"
    _          -> "elf32-unknown"

-- | Extract DWARF sections from a 64-bit ELF file.
extractSections64 :: Elf.Elf 64 -> Sections
extractSections64 elf = mkSections $ \name ->
  case Elf.findSectionByName name elf of
    (section:_) -> Just $ Elf.elfSectionData section
    []          -> Nothing

-- | Extract DWARF sections from a 32-bit ELF file.
extractSections32 :: Elf.Elf 32 -> Sections
extractSections32 elf = mkSections $ \name ->
  case Elf.findSectionByName name elf of
    (section:_) -> Just $ Elf.elfSectionData section
    []          -> Nothing
