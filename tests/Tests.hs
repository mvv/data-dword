{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

import Test.Framework (defaultMain, testGroup)
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Test.QuickCheck hiding ((.&.))

import Data.Bits
import Data.Word
import Data.Int
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

main = defaultMain [ isoTestGroup "|Word32|Word32|" (0 ∷ U64)
                   , isoTestGroup "|Int32|Word32|" (0 ∷ I64)
                   , isoTestGroup "|Word16|Word16|Word32|" (0 ∷ UU64)
                   , isoTestGroup "|Int16|Word16|Word32|" (0 ∷ II64) ]

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
        [ testProperty "toInteger" $ prop_toInteger t ]
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
#if MIN_VERSION_base(4,5,0)
        , testProperty "popCount" $ prop_popCount t
#endif
        ]
    ]

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

prop_negate = propUnary negate negate
prop_abs = propUnary abs abs
prop_signum = propUnary signum signum
prop_add = propBinary (+) (+)
prop_sub = propBinary (-) (-)
prop_mul = propBinary (*) (*)
prop_fromInteger t i = fromInteger i == fromType t (fromInteger i) 

prop_toRational = propUnary' toRational toRational

prop_toInteger = propUnary' toInteger toInteger

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
#if MIN_VERSION_base(4,5,0)
prop_popCount = propUnary' popCount popCount
#endif

