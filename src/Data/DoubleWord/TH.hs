{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE TemplateHaskell #-}

module Data.DoubleWord.TH
  ( mkDoubleWord
  , mkUnpackedDoubleWord
  ) where

import GHC.Arr (Ix(..))
import Data.Ratio ((%))
import Data.Bits (Bits(..))
import Data.Hashable (Hashable(..), combine)
import Control.Applicative ((<$>), (<*>))
import Language.Haskell.TH
import Data.DoubleWord.Base

-- |
mkDoubleWord ∷ String -- ^ Unsigned variant type name
             → String -- ^ Unsigned variant constructor name
             → Strict -- ^ Unsigned variant higher half strictness
             → Name   -- ^ Unsigned variant higher half type
             → String -- ^ Signed variant type name
             → String -- ^ Signed variant constructor name
             → Strict -- ^ Signed variant higher half strictness
             → Name   -- ^ Signed variant higher half type
             → Strict -- ^ Lower half strictness
             → Name   -- ^ Lower half type
             → Q [Dec]
mkDoubleWord un uc uhs uhn sn sc shs shn ls ln =
    (++) <$> mkDoubleWord' False un' uc' sn' sc' uhs (ConT uhn) ls (ConT ln)
         <*> mkDoubleWord' True  sn' sc' un' uc' shs (ConT shn) ls (ConT ln)
  where un' = mkName un
        uc' = mkName uc
        sn' = mkName sn
        sc' = mkName sc

mkUnpackedDoubleWord ∷ String → Name → String → Name → Name → Q [Dec]
mkUnpackedDoubleWord un uhn sn shn ln =
  mkDoubleWord un un Unpacked uhn sn sn Unpacked shn Unpacked ln

mkDoubleWord' ∷ Bool
              → Name → Name
              → Name → Name
              → Strict → Type
              → Strict → Type
              → Q [Dec]
mkDoubleWord' signed tp cn otp ocn hiS hiT loS loT = return $
    [DataD [] tp [] [NormalC cn [(hiS, hiT), (loS, loT)]] [],
     TySynInstD ''UnsignedWord [ConT tp] $ ConT $ if signed then otp else tp,
     TySynInstD ''SignedWord [ConT tp] $ ConT $ if signed then tp else otp,
     inst ''DoubleWord [tp]
       [TySynInstD ''LoWord [ConT tp] loT,
        TySynInstD ''HiWord [ConT tp] hiT,
        funLo 'loWord (VarE lo), inline 'loWord,
        funHi 'hiWord (VarE hi), inline 'hiWord,
        fun 'fromHiAndLo (ConE cn), inline 'fromHiAndLo],
     inst ''Eq [tp]
       [{-
          (W hi lo) == (W hi' lo') = hi == hi' && lo == lo'
        -}
        funHiLo2 '(==) $ appV '(&&) [appVN '(==) [hi, hi'],
                                     appVN '(==) [lo, lo']],
        inline '(==)],
     inst ''Ord [tp]
       [{-
          compare (W hi lo) (W hi' lo') = case hi `compare` hi' of
            EQ → lo `compare` lo'
            x  → x
        -}
        funHiLo2 'compare $ CaseE (appVN 'compare [hi, hi'])
          [Match (ConP 'EQ []) (NormalB (appVN 'compare [lo, lo'])) [],
           Match (VarP x) (NormalB (VarE x)) []],
        inline 'compare],
     inst ''Bounded [tp]
       [{- minBound = W minBound minBound -}
        fun 'minBound $ appWN ['minBound, 'minBound],
        inline 'minBound,
        {- maxBound = W maxBound maxBound -}
        fun 'maxBound $ appWN ['maxBound, 'maxBound],
        inline 'maxBound],
     inst ''Enum [tp]
       [
        {-
          succ (W hi lo) = if lo == maxBound then W (succ hi) minBound
                                             else W hi (succ lo)
        -}
        funHiLo 'succ $ CondE (appVN '(==) [lo, 'maxBound])
                              (appW [appVN 'succ [hi], VarE 'minBound])
                              (appW [VarE hi, appVN 'succ [lo]]),
        inline 'succ,
        {-
          pred (W hi lo) = if lo == minBound then W (pred hi) maxBound
                                             else W hi (pred lo)
        -}
        funHiLo 'pred $ CondE (appVN '(==) [lo, 'minBound])
                              (appW [appVN 'pred [hi], VarE 'maxBound])
                              (appW [VarE hi, appVN 'pred [lo]]),
        inline 'pred,
        {-
          toEnum x
            | x < 0     = if signed
                          then W (-1) (negate $ 1 + toEnum (negate (x + 1)))
                          else ERROR
            | otherwise = W 0 (toEnum x)
        -}
        funX 'toEnum $
          CondE (appV '(<) [VarE x, litI 0])
                (if signed
                 then appW [
                        litI (-1),
                        appV 'negate [
                          appV '(+) [
                            litI 1,
                            appV 'toEnum [
                              appV 'negate [appV '(+) [VarE x, litI 1]]]]]]
                 else appV 'error [litS "toEnum: nagative value"])
                (appW [litI 0, appVN 'toEnum [x]]),
        inline 'toEnum,
        {-
          fromEnum (W 0 lo)    = fromEnum lo
          fromEnum (W (-1) lo) = if signed then negate $ fromEnum $ negate lo
                                           else ERROR
          fromEnum _           = ERROR
        -}
        FunD 'fromEnum $
          Clause [ConP cn [LitP $ IntegerL 0, VarP lo]]
                 (NormalB $ appVN 'fromEnum [lo]) [] :
          if signed
          then [Clause [ConP cn [LitP $ IntegerL (-1), VarP lo]]
                       (NormalB $ appV 'negate [
                                    appV 'fromEnum [
                                      appV 'negate [VarE lo]]]) [],
                Clause [WildP]
                       (NormalB $ appV 'error [
                                    litS "fromEnum: out of bounds"]) []]
          else
            [Clause [WildP]
                    (NormalB $ appV 'error [
                                 litS "fromEnum: out of bounds"]) []],
        inline 'fromEnum,
        {- enumFrom x = enumFromTo x maxBound -}
        funX 'enumFrom $ appVN 'enumFromTo [x, 'maxBound],
        inline 'enumFrom,
        {- 
          enumFromThen x y =
            enumFromThenTo x y $ if y >= x then maxBound else minBound 
        -}
        funXY 'enumFromThen $
          appV 'enumFromThenTo [
            VarE x, VarE y,
            CondE (appVN '(>=) [x, y]) (VarE 'maxBound) (VarE 'minBound)],
        inline 'enumFromThen,
        {-
          enumFromTo x y = case y `compare` x of
              LT → x : down y x
              EQ → [x]
              GT → x : up y x
            where down to c = next : if next == to then [] else down to next
                    where next = c - 1
                  up to c = next : if next == to then [] else up to next
                    where next = c + 1 
        -}
        FunD 'enumFromTo [
          Clause [VarP x, VarP y]
            (NormalB $
              CaseE (appVN 'compare [y, x]) [
                Match
                  (ConP 'LT [])
                  (NormalB $ appC '(:) [VarE x, appVN down [y, x]]) [],
                Match
                  (ConP 'EQ [])
                  (NormalB $ appC '(:) [VarE x, ConE '[]]) [],
                Match
                  (ConP 'GT [])
                  (NormalB $ appC '(:) [VarE x, appVN up [y, x]]) []])
            [FunD down
              [Clause [VarP to, VarP c]
                (NormalB $
                  appC '(:) [
                    VarE next,
                    CondE (appVN '(==) [next, to])
                          (ConE '[]) (appVN down [to, next])])
                [ValD (VarP next)
                      (NormalB $ appV '(-) [VarE c, litI 1]) []]],
             FunD up
              [Clause [VarP to, VarP c]
                (NormalB $
                  appC '(:) [
                    VarE next,
                    CondE (appVN '(==) [next, to])
                          (ConE '[]) (appVN up [to, next])])
                [ValD (VarP next)
                      (NormalB $ appV '(+) [VarE c, litI 1]) []]]]],
        inlinable 'enumFromTo,
        {-
          enumFromThenTo x y z = case y `compare` x of 
              LT → if z > x then [] else down (x - y) z x
              EQ → repeat x
              GT → if z < x then [] else up (y - x) z x
            where down s to c = c : if next < to then [] else down s to next
                    where next = c - s
                  up s to c = c : if next > to then [] else up s to next
                    where next = c + s 
        -}
        FunD 'enumFromThenTo [
          Clause [VarP x, VarP y, VarP z]
            (NormalB $
              CaseE (appVN 'compare [y, x]) [
                Match
                  (ConP 'LT [])
                  (NormalB $
                    CondE (appVN '(>) [z, x]) (ConE '[])
                          (appV down [appVN '(-) [x, y], VarE z, VarE x])) [],
                Match (ConP 'EQ []) (NormalB $ appVN 'repeat [x]) [],
                Match
                  (ConP 'GT [])
                  (NormalB $
                    CondE (appVN '(<) [z, x]) (ConE '[])
                          (appV up [appVN '(-) [y, x], VarE z, VarE x])) []])
            [FunD down [
              Clause [VarP step, VarP to, VarP c]
                (NormalB $
                  appC '(:) [
                    VarE c,
                    CondE (appVN '(<) [next, to])
                          (ConE '[]) (appVN down [step, to, next])])
                [ValD (VarP next) (NormalB $ appVN '(-) [c, step]) []]],
             FunD up [
              Clause [VarP step, VarP to, VarP c]
                (NormalB $
                  appC '(:) [
                    VarE c,
                    CondE (appVN '(==) [next, to])
                          (ConE '[]) (appVN up [step, to, next])])
                [ValD (VarP next) (NormalB $ appVN '(+) [c, step]) []]]]],
        inlinable 'enumFromThenTo],
     inst ''UnwrappedMul [tp]
       [{-
          unwrappedMul (W hi lo) (W hi' lo') =
        -}
       ],
     inst ''Num [tp]
       [{-
          negate (W hi lo) = if lo == 0 then W (negate hi) 0
                                        else W (negate $ hi + 1) (negate lo)
        -}
        funHiLo 'negate $
          CondE (appV '(==) [VarE lo, litI 0])
                (appW [appVN 'negate [hi], litI 0])
                (appW [appV 'negate [appV '(+) [litI 1, VarE hi]],
                       appVN 'negate [lo]]),
        inline 'negate,
        {- 
          abs x = if signed
                  then if x < 0 then negate x else x 
                  else x
        -}
        funX 'abs $
          if signed
          then CondE (appV '(<) [VarE x, litI 0]) (appVN 'negate [x]) (VarE x)
          else VarE x,
        inline 'abs,
        {-
          signum (W hi lo) = if SIGNED
                             then case hi `compare` 0 of
                               LT → W (-1) maxBound
                               EQ → if lo == 0 then W 0 0 else W 0 1
                               GT → W 0 1
                             else if hi == 0 && lo == 0 then W 0 0 else W 0 1
        -}
        funHiLo 'signum $
           if signed
           then CaseE (appV 'compare [VarE hi, litI 0]) [
                  Match (ConP 'LT [])
                        (NormalB $ appW [litI (-1), VarE 'maxBound]) [],
                  Match (ConP 'EQ [])
                        (NormalB $ CondE (appV '(==) [VarE lo, litI 0])
                                         (appW [litI 0, litI 0])
                                         (appW [litI 0, litI 1])) [],
                  Match (ConP 'GT [])
                        (NormalB $ appW [litI 0, litI 1]) []]
           else CondE (appV '(&&) [appV '(==) [VarE hi, litI 0],
                                   appV '(==) [VarE lo, litI 0]])
                      (appW [litI 0, litI 0]) (appW [litI 0, litI 1]),
        inline 'signum,
        {-
          (W hi lo) + (W hi' lo') = W y x
            where x = lo + lo'
                  y = hi + hi' + if x < lo then 1 else 0
        -}
        funHiLo2' '(+) (appWN [y, x]) [
          val x (appVN '(+) [lo, lo']),
          val y (appV '(+) [appVN '(+) [hi, hi'],
                            CondE (appVN '(<) [x, lo]) (litI 1) (litI 0)])],
        inline '(+),
        {-
          UNSIGNED:
            (W hi lo) * (W hi' lo') =
                W (hi * fromIntegral lo' + hi' * fromIntegral lo +
                   fromIntegral x) y
              where (x, y) = unwrappedMul lo lo'

          SIGNED:
            (W hi lo) * (W hi' lo') = W (fromIntegral x) y
              where U x y = U (fromIntegral hi) lo * U (fromIntegral hi') lo'
        -}
        if signed
        then
          funHiLo2' '(*)
            (appW [appVN 'fromIntegral [x], VarE y])
            [ValD (ConP ocn [VarP x, VarP y])
              (NormalB $
                appV '(*) [
                  appC ocn [appVN 'fromIntegral [hi], VarE lo],
                  appC ocn [appVN 'fromIntegral [hi'], VarE lo']]) []]
        else
          funHiLo2' '(*)
            (appW [
              appV '(+) [
                appV '(+) [
                  appV '(*) [VarE hi, appVN 'fromIntegral [lo']],
                  appV '(*) [VarE hi', appVN 'fromIntegral [lo]]],
                appVN 'fromIntegral [x]],
              VarE y])
            [vals [x, y] (appVN 'unwrappedMul [lo, lo'])],
        inline '(*),
        {-
          fromInteger x = W (fromInteger y) (fromInteger z)
            where (y, z) = x `quotRem` (toInteger (maxBound ∷ L) + 1)
        -}
        funX' 'fromInteger
          (appW [appVN 'fromInteger [y], appVN 'fromInteger [z]])
          [vals [y, z]
            (appV 'quotRem [
              VarE x,
              appV '(+) [
                appV 'toInteger [SigE (VarE 'maxBound) loT], litI 1]])],
        inlinable 'fromInteger],
     inst ''Real [tp]
       [{- toRational x = toInteger x % 1 -}
        funX 'toRational $ appV '(%) [appVN 'toInteger [x], litI 1],
        inline 'toRational],
     inst ''Integral [tp]
       [{-
          toInteger (W hi lo) =
            toInteger hi * (toInteger (maxBound ∷ L) + 1) + toInteger lo
        -}
        funHiLo 'toInteger $
          appV '(+) [
            appV '(*) [
              appVN 'toInteger [hi],
              appV '(+) [
                appV 'toInteger [SigE (VarE 'maxBound) loT], litI 1]],
            appVN 'toInteger [lo]]],
     inst ''Show [tp]
       [fun 'show $ appVN '(.) ['show, 'toInteger], inline 'show],
     inst ''Hashable [tp]
       [{- hash (W hi lo) = hash hi `combine` hash lo -}
        funHiLo 'hash $ appV 'combine [appVN 'hash [hi], appVN 'hash [lo]],
        inline 'hash,
        inline 'hashWithSalt],
     inst ''Ix [tp]
       [{- range (x, y) = enumFromTo x y -}
        funTup 'range $ appVN 'enumFromTo [x, y],
        inline 'range,
        {- unsafeIndex (x, _) z = fromIntegral z - fromIntegral x -}
        funTupLZ 'unsafeIndex $
          appV '(-) [appVN 'fromIntegral [z], appVN 'fromIntegral [x]],
        inline 'unsafeIndex,
        {- inRange (x, y) z = z >= x && z <= y -}
        funTupZ 'inRange $ appV '(&&) [appVN '(>=) [z, x], appVN '(<=) [z, y]],
        inline 'inRange
       ],
     inst ''Bits [tp]
       [{- bitSize _ = bitSize (undefined ∷ H) + bitSize (undefined ∷ L) -}
        fun_ 'bitSize $ appV '(+) [
          appV 'bitSize [SigE (VarE 'undefined) hiT],
          appV 'bitSize [SigE (VarE 'undefined) loT]],
        inline 'bitSize,
        {- isSigned _ = SIGNED -}
        fun_ 'isSigned $ ConE $ if signed then 'True else 'False,
        inline 'isSigned,
        {- complement (W hi lo) = W (complement hi) (complement lo) -}
        funHiLo 'complement $
          appW [appVN 'complement [hi], appVN 'complement [lo]],
        inline 'complement,
        {- xor (W hi lo) (W hi' lo') = W (xor hi hi') (xor lo lo') -}
        funHiLo2 'xor $ appW [appVN 'xor [hi, hi'], appVN 'xor [lo, lo']],
        inline 'xor,
        {- (W hi lo) .&. (W hi' lo') = W (hi .&. hi') (lo .&. lo') -}
        funHiLo2 '(.&.) $
          appW [appVN '(.&.) [hi, hi'], appVN '(.&.) [lo, lo']],
        inline '(.&.),
        {- (W hi lo) .|. (W hi' lo') = W (hi .|. hi') (lo .|. lo') -}
        funHiLo2 '(.|.) $
          appW [appVN '(.|.) [hi, hi'], appVN '(.|.) [lo, lo']],
        inline '(.|.),
        {-
          shiftL (W hi lo) x =
              if y > 0
                then W (shiftL hi x .|. fromIntegral (shiftR lo y))
                       (shiftL lo x)
                else W (fromIntegral $ shiftL lo $ negate y) 0
            where y = bitSize (undefined ∷ L) - x
        -}
        funHiLoX' 'shiftL
          (CondE (appV '(>) [VarE y, litI 0])
                 (appW [appV '(.|.) [
                          appVN 'shiftL [hi, x],
                          appV 'fromIntegral [appVN 'shiftR [lo, y]]],
                        appVN 'shiftL [lo, x]])
                 (appW [appV 'fromIntegral [
                          appV 'shiftL [VarE lo, appVN 'negate [y]]],
                        litI 0]))
          [val y $
             appV '(-) [appV 'bitSize [SigE (VarE 'undefined) loT], VarE x]],
        {-
          shiftR (W hi lo) x =
              W (shiftR hi x)
                (if y >= 0 then shiftL (fromIntegral hi) y .|. shiftR lo x
                           else z)
            where y = bitSize (undefined ∷ L) - x
                  z = if SIGNED
                      then fromIntegral $
                             shiftR (fromIntegral hi ∷ SignedWord L) $
                               negate y
                      else shiftR (fromIntegral hi) $ negate y
        -}
        funHiLoX' 'shiftR
          (appW [
             appVN 'shiftR [hi, x],
             CondE (appV '(>=) [VarE y, litI 0])
                   (appV '(.|.) [
                      appV 'shiftL [appVN 'fromIntegral [hi], VarE y],
                      appVN 'shiftR [lo, x]])
                   (VarE z)])
          [val y $
             appV '(-) [appV 'bitSize [SigE (VarE 'undefined) loT], VarE x],
           val z $
             if signed
             then appV 'fromIntegral [
                    appV 'shiftR [
                      SigE (appVN 'fromIntegral [hi])
                           (AppT (ConT ''SignedWord) loT),
                      appVN 'negate [y]]]
             else appV 'shiftR [appVN 'fromIntegral [hi], appVN 'negate [y]]],
        {-
          bit x = if y >= 0 then W (bit y) 0 else W 0 (bit x)
            where y = x - bitSize (undefined ∷ LoWord W)
        -}
        funX' 'bit (CondE (appV '(>=) [VarE y, litI 0])
                          (appW [appVN 'bit [y], litI 0])
                          (appW [litI 0, appVN 'bit [x]]))
          [val y $
             appV '(-) [VarE x, appV 'bitSize [SigE (VarE 'undefined) loT]]],
        inline 'bit,
        {-
          setBit (W hi lo) x =
              if y >= 0 then W (setBit hi y) lo else W hi (setBit lo x)
            where y = x - bitSize (undefined ∷ L)
        -}
        funHiLoX' 'setBit
          (CondE (appV '(>=) [VarE y, litI 0])
                 (appW [appVN 'setBit [hi, y], VarE lo])
                 (appW [VarE hi, appVN 'setBit [lo, x]]))
          [val y $
             appV '(-) [VarE x, appV 'bitSize [SigE (VarE 'undefined) loT]]],
        inline 'setBit,
        {-
          clearBit (W hi lo) x =
              if y >= 0 then W (clearBit hi y) lo
                        else W hi (clearBit lo x)
            where y = x - bitSize (undefined ∷ L)
        -}
        funHiLoX' 'clearBit
          (CondE (appV '(>=) [VarE y, litI 0])
                 (appW [appVN 'clearBit [hi, y], VarE lo])
                 (appW [VarE hi, appVN 'clearBit [lo, x]]))
          [val y $
             appV '(-) [VarE x, appV 'bitSize [SigE (VarE 'undefined) loT]]],
        inline 'clearBit,
        {-
          complementBit (W hi lo) x =
              if y >= 0 then W (complementBit hi y) lo
                        else W hi (complementBit lo x)
            where y = x - bitSize (undefined ∷ L)
        -}
        funHiLoX' 'complementBit
          (CondE (appV '(>=) [VarE y, litI 0])
                 (appW [appVN 'complementBit [hi, y], VarE lo])
                 (appW [VarE hi, appVN 'complementBit [lo, x]]))
          [val y $
             appV '(-) [VarE x, appV 'bitSize [SigE (VarE 'undefined) loT]]],
        inline 'complementBit,
        {-
          testBit (W hi lo) x =
              if y >= 0 then testBit hi y else testBit lo x
            where y = x - bitSize (undefined ∷ L)
        -}
        funHiLoX' 'testBit
          (CondE (appV '(>=) [VarE y, litI 0])
                 (appVN 'testBit [hi, y])
                 (appVN 'testBit [lo, x]))
          [val y $
             appV '(-) [VarE x, appV 'bitSize [SigE (VarE 'undefined) loT]]],
        inline 'testBit
       ]
    ]
  where
    x    = mkName "x"
    y    = mkName "y"
    z    = mkName "z"
    c    = mkName "c"
    next = mkName "next"
    step = mkName "step"
    to   = mkName "to"
    down = mkName "down"
    up   = mkName "up"
    hi   = mkName "hi"
    lo   = mkName "lo"
    hi'  = mkName "hi'"
    lo'  = mkName "lo'"
    inst cls params = InstanceD [] (foldl AppT (ConT cls) (ConT <$> params))
    fun n e       = FunD n [Clause [] (NormalB e) []]
    fun_ n e      = FunD n [Clause [WildP] (NormalB e) []]
    funX' n e ds  = FunD n [Clause [VarP x] (NormalB e) ds]
    funX n e      = funX' n e []
    funXY n e     = FunD n [Clause [VarP x, VarP y] (NormalB e) []]
    funXY' n e ds = FunD n [Clause [VarP x, VarP y] (NormalB e) ds]
    funTup n e    = FunD n [Clause [TupP [VarP x, VarP y]] (NormalB e) []]
    funTupZ n e   =
      FunD n [Clause [TupP [VarP x, VarP y], VarP z] (NormalB e) []]
    funTupLZ n e  =
      FunD n [Clause [TupP [VarP x, WildP], VarP z] (NormalB e) []]
    funLo n e     = FunD n [Clause [ConP cn [WildP, VarP lo]] (NormalB e) []]
    funHi n e     = FunD n [Clause [ConP cn [VarP hi, WildP]] (NormalB e) []]
    funHiLo n e   = FunD n [Clause [ConP cn [VarP hi, VarP lo]] (NormalB e) []]
    funHiLoX' n e ds =
      FunD n [Clause [ConP cn [VarP hi, VarP lo], VarP x] (NormalB e) ds]
    funHiLo2 n e     = funHiLo2' n e []
    funHiLo2' n e ds =
      FunD n [Clause [ConP cn [VarP hi, VarP lo],
                      ConP cn [VarP hi', VarP lo']] (NormalB e) ds]
    inline n = PragmaD $ InlineP n $ InlineSpec True False Nothing
    inlinable n = PragmaD $ InlineP n $ InlineSpec True False Nothing
    val n e   = ValD (VarP n) (NormalB e) []
    vals ns e = ValD (TupP (VarP <$> ns)) (NormalB e) []
    app f   = foldl AppE f
    appN f  = app f . fmap VarE
    appV f  = app (VarE f)
    appC f  = app (ConE f)
    appW    = appC cn
    appVN f = appN (VarE f)
    appCN f = appN (ConE f)
    appWN   = appCN cn
    litI = LitE . IntegerL
    litS = LitE . StringL

