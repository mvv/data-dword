{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}

#include "MachDeps.h"

module Data.DoubleWord.Base
  ( UnsignedWord,
    SignedWord,
    DoubleWord(..),
    UnwrappedAdd(..),
    UnwrappedMul(..),
    LeadingZeroes(..)
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

type family UnsignedWord w

type instance UnsignedWord Word8  = Word8
type instance UnsignedWord Word16 = Word16
type instance UnsignedWord Word32 = Word32
type instance UnsignedWord Word64 = Word64
type instance UnsignedWord Int8   = Word8
type instance UnsignedWord Int16  = Word16
type instance UnsignedWord Int32  = Word32
type instance UnsignedWord Int64  = Word64

type family SignedWord w

type instance SignedWord Word8  = Int8
type instance SignedWord Word16 = Int16
type instance SignedWord Word32 = Int32
type instance SignedWord Word64 = Int64
type instance SignedWord Int8   = Int8
type instance SignedWord Int16  = Int16
type instance SignedWord Int32  = Int32
type instance SignedWord Int64  = Int64

class DoubleWord w where
  type LoWord w
  type HiWord w
  loWord      ∷ w → LoWord w
  hiWord      ∷ w → HiWord w
  fromHiAndLo ∷ HiWord w → LoWord w → w

instance DoubleWord Word32 where
  type LoWord Word32 = Word16
  type HiWord Word32 = Word16
  loWord w = fromIntegral w
  {-# INLINE loWord #-}
  hiWord w = fromIntegral $ w `shiftR` 16
  {-# INLINE hiWord #-}
  fromHiAndLo hi lo = fromIntegral hi `shiftL` 16 .|. fromIntegral lo
  {-# INLINE fromHiAndLo #-}

instance DoubleWord Int32 where
  type LoWord Int32 = Word16
  type HiWord Int32 = Int16
  loWord w = fromIntegral w
  {-# INLINE loWord #-}
  hiWord w = fromIntegral $ w `shiftR` 16
  {-# INLINE hiWord #-}
  fromHiAndLo hi lo = fromIntegral hi `shiftL` 16 .|. fromIntegral lo
  {-# INLINE fromHiAndLo #-}

instance DoubleWord Word64 where
  type LoWord Word64 = Word32
  type HiWord Word64 = Word32
  loWord w = fromIntegral w
  {-# INLINE loWord #-}
  hiWord w = fromIntegral $ w `shiftR` 32
  {-# INLINE hiWord #-}
  fromHiAndLo hi lo = fromIntegral hi `shiftL` 32 .|. fromIntegral lo
  {-# INLINE fromHiAndLo #-}

instance DoubleWord Int64 where
  type LoWord Int64 = Word32
  type HiWord Int64 = Int32
  loWord w = fromIntegral w
  {-# INLINE loWord #-}
  hiWord w = fromIntegral $ w `shiftR` 32
  {-# INLINE hiWord #-}
  fromHiAndLo hi lo = fromIntegral hi `shiftL` 32 .|. fromIntegral lo
  {-# INLINE fromHiAndLo #-}

class UnwrappedAdd w where
  unwrappedAdd ∷ w → w → (w, UnsignedWord w)

instance UnwrappedAdd Word16 where 
  unwrappedAdd x y = hi `seq` lo `seq` (hi, lo)
    where s  = fromIntegral x + fromIntegral y ∷ Word32
          lo = loWord s
          hi = hiWord s
  {-# INLINE unwrappedAdd #-}

instance UnwrappedAdd Int16 where 
  unwrappedAdd x y = hi `seq` lo `seq` (hi, lo)
    where s  = fromIntegral x + fromIntegral y ∷ Int32
          lo = loWord s
          hi = hiWord s
  {-# INLINE unwrappedAdd #-}

instance UnwrappedAdd Word32 where 
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

instance UnwrappedAdd Int32 where 
  unwrappedAdd x y = hi `seq` lo `seq` (hi, lo)
    where extX = if x < 0 then maxBound else 0 ∷ Word32
          extY = if y < 0 then maxBound else 0 ∷ Word32
          (hi', lo) = fromIntegral x `unwrappedAdd` fromIntegral y
          hi = fromIntegral $ hi' + extX + extY
  {-# INLINABLE unwrappedAdd #-}

instance UnwrappedAdd Word64 where 
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

instance UnwrappedAdd Int64 where 
  unwrappedAdd x y = hi `seq` lo `seq` (hi, lo)
    where extX = if x < 0 then maxBound else 0 ∷ Word64
          extY = if y < 0 then maxBound else 0 ∷ Word64
          (hi', lo) = fromIntegral x `unwrappedAdd` fromIntegral y
          hi = fromIntegral $ hi' + extX + extY
  {-# INLINABLE unwrappedAdd #-}

class UnwrappedMul w where
  unwrappedMul ∷ w → w → (w, UnsignedWord w)

instance UnwrappedMul Word16 where 
  unwrappedMul x y = hi `seq` lo `seq` (hi, lo)
    where p  = fromIntegral x * fromIntegral y ∷ Word32
          lo = loWord p
          hi = hiWord p
  {-# INLINE unwrappedMul #-}

instance UnwrappedMul Int16 where 
  unwrappedMul x y = hi `seq` lo `seq` (hi, lo)
    where p  = fromIntegral x * fromIntegral y ∷ Int32
          lo = loWord p
          hi = hiWord p
  {-# INLINE unwrappedMul #-}

instance UnwrappedMul Word32 where 
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

instance UnwrappedMul Int32 where
  unwrappedMul x y = hi `seq` lo `seq` (hi, lo)
    where p  = fromIntegral x * fromIntegral y ∷ Int64
          lo = loWord p
          hi = hiWord p
  {-# INLINE unwrappedMul #-}

instance UnwrappedMul Word64 where
#if __GLASGOW_HASKELL__ >= 705 && WORD_SIZE_IN_BITS == 64
  unwrappedMul (W64# x) (W64# y) = hi `seq` lo `seq` (hi, lo)
    where (# hi', lo' #) = timesWord2# x y
          lo = W64# lo'
          hi = W64# hi'
  {-# INLINE unwrappedMul #-}
#else
  unwrappedMul x y = hi `seq` lo `seq` (hi, lo)
    where xHi = x `shiftR` 32
          xLo = x .&. 0xFFFFFFFF
          yHi = y `shiftR` 32
          yLo = y .&. 0xFFFFFFFF
          hi0 = xHi * yHi
          lo0 = xLo * yLo
          p1  = xHi * yLo
          p2  = xLo * yHi
          lo  = lo0 + p1 `shiftL` 32 + p2 `shiftL` 32
          hi  = hi0 + p1 `shiftR` 32 + p2 `shiftR` 32
  {-# INLINABLE unwrappedMul #-}
#endif

instance UnwrappedMul Int64 where
  unwrappedMul x y = hi `seq` lo `seq` (hi, lo)
    where hiX = if x < 0 then negate y else 0
          hiY = if y < 0 then negate x else 0
          (hiP, lo) = fromIntegral x `unwrappedMul` fromIntegral y
          hi = fromIntegral (hiP ∷ Word64) + hiX + hiY

class Bits w ⇒ LeadingZeroes w where
  leadingZeroes ∷ w → Int

instance LeadingZeroes Word16 where
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

instance LeadingZeroes Int16 where
  leadingZeroes w = leadingZeroes w'
    where w' ∷ Word16
          w' = fromIntegral w
  {-# INLINE leadingZeroes #-}

instance LeadingZeroes Word32 where
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

instance LeadingZeroes Int32 where
  leadingZeroes w = leadingZeroes w'
    where w' ∷ Word32
          w' = fromIntegral w
  {-# INLINE leadingZeroes #-}

instance LeadingZeroes Word64 where
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
#else
  leadingZeroes w | hiZeroes == 32 = 32 + leadingZeroes (loWord w)
                  | otherwise      = hiZeroes
    where hiZeroes = leadingZeroes (hiWord w)
#endif

instance LeadingZeroes Int64 where
  leadingZeroes w = leadingZeroes w'
    where w' ∷ Word64
          w' = fromIntegral w
  {-# INLINE leadingZeroes #-}

