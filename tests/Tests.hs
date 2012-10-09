{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

import Test.Framework (RunnerOptions'(..), TestOptions'(..),
                       defaultMainWithOpts, testGroup)
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Test.QuickCheck hiding ((.&.))

import Data.Bits
import Data.Word
import Data.Int
import Data.Monoid (mempty)
import Data.DoubleWord (BinaryWord(..))
import Types

class Iso α τ | τ → α where
  fromArbitrary ∷ α → τ 
  toArbitrary ∷ τ → α

instance Iso Word64 U64 where
  fromArbitrary w = U64 (fromIntegral $ w `shiftR` 32) (fromIntegral w)
  toArbitrary (U64 h l) = fromIntegral h `shiftL` 32 .|. fromIntegral l

instance Iso Int64 I64 where
  fromArbitrary w = I64 (fromIntegral $ w `shiftR` 32) (fromIntegral w)
  toArbitrary (I64 h l) = fromIntegral h `shiftL` 32 .|. fromIntegral l

instance Iso Word64 UU64 where
  fromArbitrary w = UU64 (fromIntegral $ w `shiftR` 48)
                         (U48 (fromIntegral $ w `shiftR` 32) (fromIntegral w))
  toArbitrary (UU64 h (U48 lh ll))  =  fromIntegral h `shiftL` 48
                                   .|. fromIntegral lh `shiftL` 32
                                   .|. fromIntegral ll

instance Iso Int64 II64 where
  fromArbitrary w = II64 (fromIntegral $ w `shiftR` 48)
                         (U48 (fromIntegral $ w `shiftR` 32) (fromIntegral w))
  toArbitrary (II64 h (U48 lh ll))  =  fromIntegral h `shiftL` 48
                                   .|. fromIntegral lh `shiftL` 32
                                   .|. fromIntegral ll

main = defaultMainWithOpts
         [ arbTestGroup "Word8" (0 ∷ Word8)
         , arbTestGroup "Int8" (0 ∷ Int8)
         , arbTestGroup "Word16" (0 ∷ Word16)
         , arbTestGroup "Int16" (0 ∷ Int16)
         , arbTestGroup "Word32" (0 ∷ Word32)
         , arbTestGroup "Int32" (0 ∷ Int32)
         , arbTestGroup "Word64" (0 ∷ Word64)
         , arbTestGroup "Int64" (0 ∷ Int64)
         , isoTestGroup "|Word32|Word32|" (0 ∷ U64)
         , isoTestGroup "|Int32|Word32|" (0 ∷ I64)
         , isoTestGroup "|Word16|Word16|Word32|" (0 ∷ UU64)
         , isoTestGroup "|Int16|Word16|Word32|" (0 ∷ II64) ]
         mempty {
           ropt_test_options =
             Just (mempty { topt_maximum_generated_tests = Just 1000 })
         }

arbTestGroup name t =
  testGroup name
    [ testGroup "BinaryWord"
        [ testProperty "unwrappedAdd" $ prop_unwrappedAddArb t
        , testProperty "unwrappedMul" $ prop_unwrappedMulArb t
        , testProperty "leadingZeroes" $ prop_leadingZeroesArb t
        , testProperty "trailingZeroes" $ prop_trailingZeroesArb t
        , testProperty "allZeroes" $ prop_allZeroesArb t
        , testProperty "allOnes" $ prop_allOnesArb t
        , testProperty "msb" $ prop_msbArb t
        , testProperty "lsb" $ prop_lsbArb t
        , testProperty "testMsb" $ prop_testMsbArb t
        , testProperty "testLsb" $ prop_testLsbArb t ]
    ]

isoTestGroup name t =
  testGroup name
    [ testProperty "Iso" $ prop_conv t
    , testGroup "Eq" [ testProperty "(==)" $ prop_eq t ]
    , testGroup "Ord" [ testProperty "compare" $ prop_compare t ]
    , testGroup "Bounded"
        [ testProperty "minBound" $ prop_minBound t
        , testProperty "maxBound" $ prop_maxBound t ]
    , testGroup "Enum"
        [ testProperty "succ" $ prop_succ t
        , testProperty "pred" $ prop_pred t ]
    , testGroup "Num"
        [ testProperty "negate" $ prop_negate t
        , testProperty "abs" $ prop_abs t
        , testProperty "signum" $ prop_signum t
        , testProperty "(+)" $ prop_add t
        , testProperty "(-)" $ prop_sub t
        , testProperty "(*)" $ prop_mul t
        , testProperty "fromInteger" $ prop_fromInteger t ]
    , testGroup "Real"
        [ testProperty "toRational" $ prop_toRational t ]
    , testGroup "Integral"
        [ testProperty "toInteger" $ prop_toInteger t
        , testProperty "quotRem" $ prop_quotRem t
        , testProperty "quot" $ prop_quot t
        , testProperty "rem" $ prop_rem t
        , testProperty "divMod" $ prop_divMod t
        , testProperty "div" $ prop_div t
        , testProperty "mod" $ prop_mod t ]
    , testGroup "Bits"
        [ testProperty "complement" $ prop_complement t
        , testProperty "xor" $ prop_xor t
        , testProperty "(.&.)" $ prop_and t
        , testProperty "(.|.)" $ prop_or t
        , testProperty "shiftL" $ prop_shiftL t
        , testProperty "shiftR" $ prop_shiftR t
        , testProperty "rotateL" $ prop_rotateL t
        , testProperty "rotateR" $ prop_rotateR t
        , testProperty "bit" $ prop_bit t
        , testProperty "setBit" $ prop_setBit t
        , testProperty "clearBit" $ prop_clearBit t
        , testProperty "complementBit" $ prop_complementBit t
        , testProperty "testBit" $ prop_testBit t
        , testProperty "popCount" $ prop_popCount t
        ]
    , testGroup "BinaryWord"
        [ testProperty "unwrappedAdd" $ prop_unwrappedAdd t
        , testProperty "unwrappedMul" $ prop_unwrappedMul t
        , testProperty "leadingZeroes" $ prop_leadingZeroes t
        , testProperty "trailingZeroes" $ prop_trailingZeroes t
        , testProperty "allZeroes" $ prop_allZeroes t
        , testProperty "allOnes" $ prop_allOnes t
        , testProperty "msb" $ prop_msb t
        , testProperty "lsb" $ prop_lsb t
        , testProperty "testMsb" $ prop_testMsb t
        , testProperty "testLsb" $ prop_testLsb t
        ]
    ]

prop_unwrappedAddArb ∷ ∀ α
                     . (Integral α, BinaryWord α, Bounded (UnsignedWord α),
                        Integral (UnsignedWord α))
                     ⇒ α → α → α → Bool
prop_unwrappedAddArb _ x y = s == toInteger x + toInteger y
  where (hi, lo) = unwrappedAdd x y
        s = toInteger hi * (toInteger (maxBound ∷ UnsignedWord α) + 1)
          + toInteger lo

prop_unwrappedMulArb ∷ ∀ α
                     . (Integral α, BinaryWord α, Bounded (UnsignedWord α),
                        Integral (UnsignedWord α))
                     ⇒ α → α → α → Bool
prop_unwrappedMulArb _ x y = p == toInteger x * toInteger y
  where (hi, lo) = unwrappedMul x y 
        p = toInteger hi * (toInteger (maxBound ∷ UnsignedWord α) + 1)
          + toInteger lo

prop_leadingZeroesArb ∷ ∀ α . (Num α, BinaryWord α) ⇒ α → α → Bool
prop_leadingZeroesArb _ x
  | lz == 0   = testBit x (bs - 1)
  | lz == bs  = x == 0
  | otherwise = shiftR x (bs - lz) == 0 && testBit x (bs - lz - 1)
  where lz = leadingZeroes x
        bs = bitSize x

prop_trailingZeroesArb ∷ ∀ α . (Num α, BinaryWord α) ⇒ α → α → Bool
prop_trailingZeroesArb _ x
  | tz == 0   = testBit x 0
  | tz == bs  = x == 0
  | otherwise = shiftL x (bs - tz) == 0 && testBit x tz
  where tz = trailingZeroes x
        bs = bitSize x

prop_allZeroesArb ∷ ∀ α . BinaryWord α ⇒ α → Bool
prop_allZeroesArb a =
  all (not . testBit (allZeroes ∷ α)) [0 .. bitSize a - 1]

prop_allOnesArb ∷ ∀ α . BinaryWord α ⇒ α → Bool
prop_allOnesArb a = all (testBit (allOnes ∷ α)) [0 .. bitSize a - 1]

prop_msbArb ∷ ∀ α . BinaryWord α ⇒ α → Bool
prop_msbArb a = testBit (msb ∷ α) (bitSize a - 1) &&
                all (not . testBit (msb ∷ α)) [0 .. bitSize a - 2]

prop_lsbArb ∷ ∀ α . BinaryWord α ⇒ α → Bool
prop_lsbArb a = testBit (lsb ∷ α) 0 &&
                all (not . testBit (lsb ∷ α)) [1 .. bitSize a - 1]

prop_testMsbArb ∷ ∀ α . BinaryWord α ⇒ α → α → Bool
prop_testMsbArb _ x = testMsb x == testBit x (bitSize x - 1)

prop_testLsbArb ∷ ∀ α . BinaryWord α ⇒ α → α → Bool
prop_testLsbArb _ x = testLsb x == testBit x 0

toType ∷ Iso α τ ⇒ τ → α → τ 
toType _ = fromArbitrary

fromType ∷ Iso α τ ⇒ τ → τ → α 
fromType _ = toArbitrary

withUnary ∷ Iso α τ ⇒ τ → (τ → τ) → α → α
withUnary _ f = toArbitrary . f . fromArbitrary

withUnary' ∷ Iso α τ ⇒ τ → (τ → β) → α → β
withUnary' _ f = f . fromArbitrary

withBinary ∷ Iso α τ ⇒ τ → (τ → τ → τ) → α → α → α
withBinary _ f x y = toArbitrary $ f (fromArbitrary x) (fromArbitrary y)

withBinary' ∷ Iso α τ ⇒ τ → (τ → τ → β) → α → α → β
withBinary' _ f x y = f (fromArbitrary x) (fromArbitrary y)

propUnary f g t w = f w == withUnary t g w
propUnary' f g t w = f w == withUnary' t g w

propBinary f g t w1 w2 = f w1 w2 == withBinary t g w1 w2
propBinary' f g t w1 w2 = f w1 w2 == withBinary' t g w1 w2

prop_conv t w = toArbitrary (toType t w) == w

prop_eq = propBinary' (==) (==)

prop_compare = propBinary' compare compare

prop_minBound t = minBound == fromType t minBound
prop_maxBound t = maxBound == fromType t maxBound

prop_succ t w = (w /= maxBound) ==> (succ w == withUnary t succ w)
prop_pred t w = (w /= minBound) ==> (pred w == withUnary t pred w)

prop_unwrappedAdd ∷ (Iso α τ, Iso (UnsignedWord α) (UnsignedWord τ),
                     BinaryWord α, BinaryWord τ, Eq α, Eq (UnsignedWord α))
                  ⇒ τ → α → α → Bool
prop_unwrappedAdd t x y = h1 == toArbitrary h2 && l1 == toArbitrary l2
  where (h1, l1) = unwrappedAdd x y
        (h2, l2) = unwrappedAdd (toType t x) (toType t y)

prop_unwrappedMul ∷ (Iso α τ, Iso (UnsignedWord α) (UnsignedWord τ),
                     BinaryWord α, BinaryWord τ, Eq α, Eq (UnsignedWord α))
                  ⇒ τ → α → α → Bool
prop_unwrappedMul t x y = h1 == toArbitrary h2 && l1 == toArbitrary l2
  where (h1, l1) = unwrappedMul x y
        (h2, l2) = unwrappedMul (toType t x) (toType t y)

prop_leadingZeroes = propUnary' leadingZeroes leadingZeroes
prop_trailingZeroes = propUnary' trailingZeroes trailingZeroes
prop_allZeroes t = allZeroes == fromType t allZeroes
prop_allOnes t = allOnes == fromType t allOnes
prop_msb t = msb == fromType t msb
prop_lsb t = lsb == fromType t lsb
prop_testMsb = propUnary' testMsb testMsb
prop_testLsb = propUnary' testLsb testLsb

prop_negate = propUnary negate negate
prop_abs = propUnary abs abs
prop_signum = propUnary signum signum
prop_add = propBinary (+) (+)
prop_sub = propBinary (-) (-)
prop_mul = propBinary (*) (*)
prop_fromInteger t i = fromInteger i == fromType t (fromInteger i) 

prop_toRational = propUnary' toRational toRational

prop_toInteger = propUnary' toInteger toInteger
prop_quotRem t n d = (d /= 0) ==> (qr == (fromType t q1, fromType t r1))
  where qr = quotRem n d
        (q1, r1) = quotRem (fromArbitrary n) (fromArbitrary d)
prop_quot t n d = (d /= 0) ==> (q == fromType t q1)
  where q = quot n d
        q1 = quot (fromArbitrary n) (fromArbitrary d)
prop_rem t n d = (d /= 0) ==> (r == fromType t r1)
  where r = rem n d
        r1 = rem (fromArbitrary n) (fromArbitrary d)
prop_divMod t n d = (d /= 0) ==> (qr == (fromType t q1, fromType t r1))
  where qr = divMod n d
        (q1, r1) = divMod (fromArbitrary n) (fromArbitrary d)
prop_div t n d = (d /= 0) ==> (q == fromType t q1)
  where q = div n d
        q1 = div (fromArbitrary n) (fromArbitrary d)
prop_mod t n d = (d /= 0) ==> (r == fromType t r1)
  where r = mod n d
        r1 = mod (fromArbitrary n) (fromArbitrary d)

prop_complement = propUnary complement complement
prop_xor = propBinary xor xor
prop_and = propBinary (.&.) (.&.)
prop_or = propBinary (.|.) (.|.)
propOffsets f g t w =
  all (\b → f w b == withUnary t (`g` b) w) [0 .. bitSize t]
prop_shiftL = propOffsets shiftL shiftL
prop_shiftR = propOffsets shiftR shiftR
prop_rotateL = propOffsets rotateL rotateL
prop_rotateR = propOffsets rotateR rotateR
prop_bit t = all (\b → bit b == fromType t (bit b)) [0 .. bitSize t - 1]
propBits f g t w =
  all (\b → f w b == withUnary t (`g` b) w) [0 .. bitSize t - 1]
prop_setBit = propBits setBit setBit
prop_clearBit = propBits clearBit clearBit
prop_complementBit = propBits complementBit complementBit
prop_testBit t w =
  all (\b → testBit w b == withUnary' t (`testBit` b) w) [0 .. bitSize t - 1]
prop_popCount = propUnary' popCount popCount

