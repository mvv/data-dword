{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}

#include "MachDeps.h"

module Data.DoubleWord.Base
  ( BinaryWord(..)
  , DoubleWord(..)
  ) where

import Data.Int
import Data.Word
import Data.Bits (Bits(..))
#if __GLASGOW_HASKELL__ >= 705
import GHC.Prim (plusWord2#, timesWord2#)
# if WORD_SIZE_IN_BITS == 32
import GHC.Word (Word32(..))
# endif
# if WORD_SIZE_IN_BITS == 64
import GHC.Word (Word64(..))
# endif
#endif

class Bits w ⇒ BinaryWord w where
  type UnsignedWord w
  type SignedWord w
  unsignedWord ∷ w → UnsignedWord w
  signedWord ∷ w → SignedWord w
  unwrappedAdd ∷ w → w → (w, UnsignedWord w)
  unwrappedMul ∷ w → w → (w, UnsignedWord w)
  leadingZeroes ∷ w → Int
  trailingZeroes ∷ w → Int

instance BinaryWord Word8 where
  type UnsignedWord Word8 = Word8
  type SignedWord Word8 = Int8
  unsignedWord = id
  {-# INLINE unsignedWord #-}
  signedWord = fromIntegral
  {-# INLINE signedWord #-}
  unwrappedAdd x y = hi `seq` lo `seq` (hi, lo)
    where s = fromIntegral x + fromIntegral y ∷ Word16
          hi = hiWord s
          lo = loWord s
  {-# INLINE unwrappedAdd #-}
  unwrappedMul x y = hi `seq` lo `seq` (hi, lo)
    where p = fromIntegral x * fromIntegral y ∷ Word16
          hi = hiWord p
          lo = loWord p
  {-# INLINE unwrappedMul #-}
  leadingZeroes w | w .&. 0xF0 == 0 = go4 4 w
                  | otherwise       = go4 0 (shiftR w 4)
    where go4 off w' | w' .&. 8 /= 0 = off
                     | w' .&. 4 /= 0 = off + 1
                     | w' .&. 2 /= 0 = off + 2
                     | w' .&. 1 /= 0 = off + 3
                     | otherwise     = off + 4
  trailingZeroes w | w .&. 0x0F == 0 = go4 4 (shiftR w 4)
                   | otherwise       = go4 0 w
    where go4 off w' | w' .&. 1 /= 0 = off
                     | w' .&. 2 /= 0 = off + 1
                     | w' .&. 4 /= 0 = off + 2
                     | w' .&. 8 /= 0 = off + 3
                     | otherwise     = off + 4

instance BinaryWord Word16 where
  type UnsignedWord Word16 = Word16
  type SignedWord Word16 = Int16
  unsignedWord = id
  {-# INLINE unsignedWord #-}
  signedWord = fromIntegral
  {-# INLINE signedWord #-}
  unwrappedAdd x y = hi `seq` lo `seq` (hi, lo)
    where s  = fromIntegral x + fromIntegral y ∷ Word32
          lo = loWord s
          hi = hiWord s
  {-# INLINE unwrappedAdd #-}
  unwrappedMul x y = hi `seq` lo `seq` (hi, lo)
    where p  = fromIntegral x * fromIntegral y ∷ Word32
          lo = loWord p
          hi = hiWord p
  {-# INLINE unwrappedMul #-}
  leadingZeroes w | w .&. 0xFF00 == 0 = go8 8 w
                  | otherwise         = go8 0 (shiftR w 8)
    where
      go8 off w' | w' .&. 0xF0 == 0 = go4 (off + 4) w'
                 | otherwise        = go4 off (shiftR w' 4)
      go4 off w' | w' .&. 8 /= 0    = off
                 | w' .&. 4 /= 0    = off + 1
                 | w' .&. 2 /= 0    = off + 2
                 | w' .&. 1 /= 0    = off + 3
                 | otherwise        = off + 4
  trailingZeroes w | w .&. 0x00FF == 0 = go8 8 (shiftR w 8)
                   | otherwise         = go8 0 w
    where
      go8 off w' | w' .&. 0x0F == 0 = go4 (off + 4) (shiftR w' 4)
                 | otherwise        = go4 off w'
      go4 off w' | w' .&. 1 /= 0    = off
                 | w' .&. 2 /= 0    = off + 1
                 | w' .&. 4 /= 0    = off + 2
                 | w' .&. 8 /= 0    = off + 3
                 | otherwise        = off + 4

instance BinaryWord Word32 where
  type UnsignedWord Word32 = Word32
  type SignedWord Word32 = Int32
  unsignedWord = id
  {-# INLINE unsignedWord #-}
  signedWord = fromIntegral
  {-# INLINE signedWord #-}
#if __GLASGOW_HASKELL__ >= 705 && WORD_SIZE_IN_BITS == 32
  unwrappedAdd (W32# x) (W32# y) = hi `seq` lo `seq` (hi, lo)
    where (# hi', lo' #) = plusWord2# x y
          hi = W32# hi'
          lo = W32# lo'
#else
  unwrappedAdd x y = hi `seq` lo `seq` (hi, lo)
    where s  = fromIntegral x + fromIntegral y ∷ Word64
          lo = loWord s
          hi = hiWord s
#endif
  {-# INLINE unwrappedAdd #-}
#if __GLASGOW_HASKELL__ >= 705 && WORD_SIZE_IN_BITS == 32
  unwrappedMul (W32# x) (W32# y) = hi `seq` lo `seq` (hi, lo)
    where (# hi', lo' #) = timesWord2# x y
          lo = W32# lo'
          hi = W32# hi'
#else
  unwrappedMul x y = hi `seq` lo `seq` (hi, lo)
    where p  = fromIntegral x * fromIntegral y ∷ Word64
          lo = loWord p
          hi = hiWord p
#endif
  {-# INLINE unwrappedMul #-}
  leadingZeroes w | w .&. 0xFFFF0000 == 0 = go16 16 w
                  | otherwise             = go16 0 (shiftR w 16)
    where
      go16 off w' | w' .&. 0xFF00 == 0 = go8 (off + 8) w'
                  | otherwise          = go8 off (shiftR w' 8)
      go8  off w' | w' .&. 0xF0 == 0   = go4 (off + 4) w'
                  | otherwise          = go4 off (shiftR w' 4)
      go4  off w' | w' .&. 8 /= 0      = off
                  | w' .&. 4 /= 0      = off + 1
                  | w' .&. 2 /= 0      = off + 2
                  | w' .&. 1 /= 0      = off + 3
                  | otherwise          = off + 4
  trailingZeroes w | w .&. 0x0000FFFF == 0 = go16 16 (shiftR w 16)
                   | otherwise             = go16 0 w
    where
      go16 off w' | w' .&. 0x00FF == 0 = go8 (off + 8) (shiftR w' 8)
                  | otherwise          = go8 off w'
      go8  off w' | w' .&. 0x0F == 0   = go4 (off + 4) (shiftR w' 4)
                  | otherwise          = go4 off w'
      go4  off w' | w' .&. 1 /= 0      = off
                  | w' .&. 2 /= 0      = off + 1
                  | w' .&. 4 /= 0      = off + 2
                  | w' .&. 8 /= 0      = off + 3
                  | otherwise          = off + 4

instance BinaryWord Word64 where
  type UnsignedWord Word64 = Word64
  type SignedWord Word64 = Int64
  unsignedWord = id
  {-# INLINE unsignedWord #-}
  signedWord = fromIntegral
  {-# INLINE signedWord #-}
#if __GLASGOW_HASKELL__ >= 705 && WORD_SIZE_IN_BITS == 64
  unwrappedAdd (W64# x) (W64# y) = hi `seq` lo `seq` (hi, lo)
    where (# hi', lo' #) = plusWord2# x y
          lo = W64# lo'
          hi = W64# hi'
  {-# INLINE unwrappedAdd #-}
#else
  unwrappedAdd x y = hi `seq` lo `seq` (hi, lo)
    where lo = x + y
          hi = if lo > x then 1 else 0
  {-# INLINABLE unwrappedAdd #-}
#endif
#if __GLASGOW_HASKELL__ >= 705 && WORD_SIZE_IN_BITS == 64
  unwrappedMul (W64# x) (W64# y) = hi `seq` lo `seq` (hi, lo)
    where (# hi', lo' #) = timesWord2# x y
          lo = W64# lo'
          hi = W64# hi'
  {-# INLINE unwrappedMul #-}
#else
  unwrappedMul x y = hi `seq` lo `seq` (hi, lo)
    where xHi = hiWord x
          xLo = loWord x
          yHi = hiWord y
          yLo = loWord y
          hi0 = xHi * yHi
          lo0 = xLo * yLo
          p1  = xHi * yLo
          p2  = xLo * yHi
          lo  = lo0 + shiftL p1 32 + shiftL p2 32
          hi  = hi0 + shiftR p1 32 + shiftR p2 32
#endif
#if WORD_SIZE_IN_BITS == 64
  leadingZeroes w | w .&. 0xFFFFFFFF00000000 == 0 = go32 32 w
                  | otherwise                     = go32 0 (shiftR w 32)
    where
      go32 off w' | w' .&. 0xFFFF0000 == 0 = go16 (off + 16) w'
                  | otherwise              = go16 off (shiftR w' 16)
      go16 off w' | w' .&. 0xFF00 == 0     = go8 (off + 8) w'
                  | otherwise              = go8 off (shiftR w' 8)
      go8  off w' | w' .&. 0xF0 == 0       = go4 (off + 4) w'
                  | otherwise              = go4 off (shiftR w' 4)
      go4  off w' | w' .&. 8 /= 0          = off
                  | w' .&. 4 /= 0          = off + 1
                  | w' .&. 2 /= 0          = off + 2
                  | w' .&. 1 /= 0          = off + 3
                  | otherwise              = off + 4
  trailingZeroes w | w .&. 0x00000000FFFFFFFF == 0 = go32 32 (shiftR w 32)
                   | otherwise                     = go32 0 w
    where
      go32 off w' | w' .&. 0x0000FFFF == 0 = go16 (off + 16) (shiftR w' 16)
                  | otherwise              = go16 off w'
      go16 off w' | w' .&. 0x00FF == 0     = go8 (off + 8) (shiftR w' 8)
                  | otherwise              = go8 off w'
      go8  off w' | w' .&. 0x0F == 0       = go4 (off + 4) (shiftR w' 4)
                  | otherwise              = go4 off w'
      go4  off w' | w' .&. 1 /= 0          = off
                  | w' .&. 2 /= 0          = off + 1
                  | w' .&. 4 /= 0          = off + 2
                  | w' .&. 8 /= 0          = off + 3
                  | otherwise              = off + 4
#else
  leadingZeroes w | hiZeroes == 32 = 32 + leadingZeroes (loWord w)
                  | otherwise      = hiZeroes
    where hiZeroes = leadingZeroes (hiWord w)
  trailingZeroes w | loZeroes == 32 = 32 + trailingZeroes (hiWord w)
                   | otherwise      = loZeroes
    where loZeroes = trailingZeroes (loWord w)
#endif

instance BinaryWord Int8 where
  type UnsignedWord Int8 = Word8
  type SignedWord Int8 = Int8
  unsignedWord = fromIntegral
  {-# INLINE unsignedWord #-}
  signedWord = id
  {-# INLINE signedWord #-}
  unwrappedAdd x y = hi `seq` lo `seq` (hi, lo)
    where s = fromIntegral x + fromIntegral y ∷ Int16
          hi = hiWord s
          lo = loWord s
  {-# INLINE unwrappedAdd #-}
  unwrappedMul x y = hi `seq` lo `seq` (hi, lo)
    where p = fromIntegral x * fromIntegral y ∷ Int16
          hi = hiWord p
          lo = loWord p
  {-# INLINE unwrappedMul #-}
  leadingZeroes = leadingZeroes . unsignedWord
  {-# INLINE leadingZeroes #-}
  trailingZeroes = trailingZeroes . unsignedWord
  {-# INLINE trailingZeroes #-}

instance BinaryWord Int16 where
  type UnsignedWord Int16 = Word16
  type SignedWord Int16 = Int16
  unsignedWord = fromIntegral
  {-# INLINE unsignedWord #-}
  signedWord = id
  {-# INLINE signedWord #-}
  unwrappedAdd x y = hi `seq` lo `seq` (hi, lo)
    where s  = fromIntegral x + fromIntegral y ∷ Int32
          lo = loWord s
          hi = hiWord s
  {-# INLINE unwrappedAdd #-}
  unwrappedMul x y = hi `seq` lo `seq` (hi, lo)
    where p  = fromIntegral x * fromIntegral y ∷ Int32
          lo = loWord p
          hi = hiWord p
  {-# INLINE unwrappedMul #-}
  leadingZeroes = leadingZeroes . unsignedWord
  {-# INLINE leadingZeroes #-}
  trailingZeroes = trailingZeroes . unsignedWord
  {-# INLINE trailingZeroes #-}

instance BinaryWord Int32 where
  type UnsignedWord Int32 = Word32
  type SignedWord Int32 = Int32
  unsignedWord = fromIntegral
  {-# INLINE unsignedWord #-}
  signedWord = id
  {-# INLINE signedWord #-}
#if WORD_SIZE_IN_BITS == 32
  unwrappedAdd x y = hi `seq` lo `seq` (hi, lo)
    where extX = if x < 0 then maxBound else 0
          extY = if y < 0 then maxBound else 0
          (hi', lo) = unsignedWord x `unwrappedAdd` unsignedWord y
          hi = signedWord $ hi' + extX + extY
  unwrappedMul x y = hi `seq` lo `seq` (hi, lo)
    where extX = if x < 0 then negate y else 0
          extY = if y < 0 then negate x else 0
          (hi', lo) = unsignedWord x `unwrappedMul` unsignedWord y
          hi = signedWord hi' + extX + extY
#else
  unwrappedAdd x y = hi `seq` lo `seq` (hi, lo)
    where s  = fromIntegral x + fromIntegral y ∷ Int64
          lo = loWord s
          hi = hiWord s
  {-# INLINE unwrappedAdd #-}
  unwrappedMul x y = hi `seq` lo `seq` (hi, lo)
    where p  = fromIntegral x * fromIntegral y ∷ Int64
          lo = loWord p
          hi = hiWord p
  {-# INLINE unwrappedMul #-}
#endif
  leadingZeroes = leadingZeroes . unsignedWord
  {-# INLINE leadingZeroes #-}
  trailingZeroes = trailingZeroes . unsignedWord
  {-# INLINE trailingZeroes #-}

instance BinaryWord Int64 where
  type UnsignedWord Int64 = Word64
  type SignedWord Int64 = Int64
  unsignedWord = fromIntegral
  {-# INLINE unsignedWord #-}
  signedWord = id
  {-# INLINE signedWord #-}
  unwrappedAdd x y = hi `seq` lo `seq` (hi, lo)
    where extX = if x < 0 then maxBound else 0
          extY = if y < 0 then maxBound else 0
          (hi', lo) = unsignedWord x `unwrappedAdd` unsignedWord y
          hi = signedWord $ hi' + extX + extY
  unwrappedMul x y = hi `seq` lo `seq` (hi, lo)
    where extX = if x < 0 then negate y else 0
          extY = if y < 0 then negate x else 0
          (hi', lo) = unsignedWord x `unwrappedMul` unsignedWord y
          hi = signedWord hi' + extX + extY
  leadingZeroes = leadingZeroes . unsignedWord
  {-# INLINE leadingZeroes #-}
  trailingZeroes = trailingZeroes . unsignedWord
  {-# INLINE trailingZeroes #-}

class BinaryWord w ⇒ DoubleWord w where
  type LoWord w
  type HiWord w
  loWord      ∷ w → LoWord w
  hiWord      ∷ w → HiWord w
  fromHiAndLo ∷ HiWord w → LoWord w → w

instance DoubleWord Word16 where
  type LoWord Word16 = Word8
  type HiWord Word16 = Word8
  loWord w = fromIntegral w
  {-# INLINE loWord #-}
  hiWord w = fromIntegral $ shiftR w 8
  {-# INLINE hiWord #-}
  fromHiAndLo hi lo = shiftL (fromIntegral hi) 8 .|. fromIntegral lo
  {-# INLINE fromHiAndLo #-}

instance DoubleWord Word32 where
  type LoWord Word32 = Word16
  type HiWord Word32 = Word16
  loWord w = fromIntegral w
  {-# INLINE loWord #-}
  hiWord w = fromIntegral $ shiftR w 16
  {-# INLINE hiWord #-}
  fromHiAndLo hi lo = shiftL (fromIntegral hi) 16 .|. fromIntegral lo
  {-# INLINE fromHiAndLo #-}

instance DoubleWord Word64 where
  type LoWord Word64 = Word32
  type HiWord Word64 = Word32
  loWord w = fromIntegral w
  {-# INLINE loWord #-}
  hiWord w = fromIntegral $ shiftR w 32
  {-# INLINE hiWord #-}
  fromHiAndLo hi lo = shiftL (fromIntegral hi) 32 .|. fromIntegral lo
  {-# INLINE fromHiAndLo #-}

instance DoubleWord Int16 where
  type LoWord Int16 = Word8
  type HiWord Int16 = Int8
  loWord w = fromIntegral w
  {-# INLINE loWord #-}
  hiWord w = fromIntegral $ shiftR w 8
  {-# INLINE hiWord #-}
  fromHiAndLo hi lo = shiftL (fromIntegral hi) 8 .|. fromIntegral lo
  {-# INLINE fromHiAndLo #-}

instance DoubleWord Int32 where
  type LoWord Int32 = Word16
  type HiWord Int32 = Int16
  loWord w = fromIntegral w
  {-# INLINE loWord #-}
  hiWord w = fromIntegral $ shiftR w 16
  {-# INLINE hiWord #-}
  fromHiAndLo hi lo = shiftL (fromIntegral hi) 16 .|. fromIntegral lo
  {-# INLINE fromHiAndLo #-}

instance DoubleWord Int64 where
  type LoWord Int64 = Word32
  type HiWord Int64 = Int32
  loWord w = fromIntegral w
  {-# INLINE loWord #-}
  hiWord w = fromIntegral $ shiftR w 32
  {-# INLINE hiWord #-}
  fromHiAndLo hi lo = shiftL (fromIntegral hi) 32 .|. fromIntegral lo
  {-# INLINE fromHiAndLo #-}

