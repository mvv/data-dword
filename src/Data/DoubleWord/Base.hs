{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE TypeFamilies #-}

module Data.DoubleWord.Base
  ( UnsignedWord,
    SignedWord,
    DoubleWord(..),
    UnwrappedMul(..)
  ) where

import Data.Int
import Data.Word
import Data.Bits (Bits(..))

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

class UnwrappedMul w where
  unwrappedMul ∷ w → w → (w, UnsignedWord w)

instance UnwrappedMul Word32 where 
  unwrappedMul x y = hi `seq` lo `seq` (hi, lo)
    where p  = fromIntegral x * fromIntegral y ∷ Word64
          lo = loWord p
          hi = hiWord p

instance UnwrappedMul Int32 where
  unwrappedMul x y = hi `seq` lo `seq` (hi, lo)
    where p  = fromIntegral x * fromIntegral y ∷ Int64
          lo = loWord p
          hi = hiWord p

instance UnwrappedMul Word64 where
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

instance UnwrappedMul Int64 where
  unwrappedMul x y = hi `seq` lo `seq` (hi, lo)
    where xNeg = x < 0
          yNeg = y < 0
          pNeg = xNeg /= yNeg
          x'   = fromIntegral (if xNeg then negate x else x) ∷ Word64
          y'   = fromIntegral (if yNeg then negate y else y) ∷ Word64
          (hi', lo') = unwrappedMul x' y'
          (hi, lo)   = if pNeg
                       then (fromIntegral $ negate $
                               if lo' == 0 then hi' else hi' + 1,
                             negate lo')
                       else (fromIntegral hi', lo')

