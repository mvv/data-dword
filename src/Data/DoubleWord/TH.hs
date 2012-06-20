{-# LANGUAGE CPP #-}
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
import Language.Haskell.TH hiding (match)
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
    [ DataD [] tp [] [NormalC cn [(hiS, hiT), (loS, loT)]] []
    , TySynInstD ''UnsignedWord [ConT tp] $ ConT $ if signed then otp else tp
    , TySynInstD ''SignedWord [ConT tp] $ ConT $ if signed then tp else otp
    , inst ''DoubleWord [tp]
        [ TySynInstD ''LoWord [ConT tp] loT
        , TySynInstD ''HiWord [ConT tp] hiT
        , funLo 'loWord (VarE lo)
        , inline 'loWord
        , funHi 'hiWord (VarE hi)
        , inline 'hiWord
        , fun 'fromHiAndLo (ConE cn)
        , inline 'fromHiAndLo ]
    , inst ''Eq [tp] $
        {- (W hi lo) == (W hi' lo') = hi == hi' && lo == lo' -}
        [ funHiLo2 '(==) $
            appV '(&&) [appVN '(==) [hi, hi'], appVN '(==) [lo, lo']]
        , inline '(==) ]
    , inst ''Ord [tp]
        {-
          compare (W hi lo) (W hi' lo') = case hi `compare` hi' of
            EQ → lo `compare` lo'
            x  → x
        -}
        [ funHiLo2 'compare $
            CaseE (appVN 'compare [hi, hi'])
              [ Match (ConP 'EQ []) (NormalB (appVN 'compare [lo, lo'])) []
              , Match (VarP x) (NormalB (VarE x)) [] ]
        , inline 'compare ]
    , inst ''Bounded [tp]
        {- minBound = W minBound minBound -}
        [ fun 'minBound $ appWN ['minBound, 'minBound]
        , inline 'minBound
        {- maxBound = W maxBound maxBound -}
        , fun 'maxBound $ appWN ['maxBound, 'maxBound]
        , inline 'maxBound ]
    , inst ''Enum [tp]
        {-
          succ (W hi lo) = if lo == maxBound then W (succ hi) minBound
                                             else W hi (succ lo)
        -}
        [ funHiLo 'succ $ CondE (appVN '(==) [lo, 'maxBound])
                                (appW [appVN 'succ [hi], VarE 'minBound])
                                (appW [VarE hi, appVN 'succ [lo]])
        , inline 'succ
        {-
          pred (W hi lo) = if lo == minBound then W (pred hi) maxBound
                                             else W hi (pred lo)
        -}
        , funHiLo 'pred $ CondE (appVN '(==) [lo, 'minBound])
                                (appW [appVN 'pred [hi], VarE 'maxBound])
                                (appW [VarE hi, appVN 'pred [lo]])
        , inline 'pred
        {-
          toEnum x
            | x < 0     = if signed
                          then W (-1) (negate $ 1 + toEnum (negate (x + 1)))
                          else ERROR
            | otherwise = W 0 (toEnum x)
        -}
        , funX 'toEnum $
            CondE (appV '(<) [VarE x, litI 0])
                  (if signed
                   then appW [ litI (-1)
                             , appV 'negate
                                 [ appV '(+)
                                     [ litI 1
                                     , appV 'toEnum
                                         [ appV 'negate
                                             [appV '(+) [VarE x, litI 1]] ]
                                     ]
                                 ]
                             ]
                   else appV 'error [litS "toEnum: nagative value"])
                  (appW [litI 0, appVN 'toEnum [x]])
        , inline 'toEnum
        {-
          fromEnum (W 0 lo)    = fromEnum lo
          fromEnum (W (-1) lo) = if signed then negate $ fromEnum $ negate lo
                                           else ERROR
          fromEnum _           = ERROR
        -}
        , FunD 'fromEnum $
            Clause [ConP cn [LitP $ IntegerL 0, VarP lo]]
                   (NormalB $ appVN 'fromEnum [lo]) [] :
            if signed
            then [ Clause [ConP cn [LitP $ IntegerL (-1), VarP lo]]
                          (NormalB $
                             appV 'negate
                               [appV 'fromEnum [appV 'negate [VarE lo]]])
                          []
                 , Clause [WildP]
                          (NormalB $
                             appV 'error [litS "fromEnum: out of bounds"])
                          []
                 ]
            else [ Clause [WildP]
                          (NormalB $
                             appV 'error [litS "fromEnum: out of bounds"])
                          [] ]
        , inline 'fromEnum
        {- enumFrom x = enumFromTo x maxBound -}
        , funX 'enumFrom $ appVN 'enumFromTo [x, 'maxBound]
        , inline 'enumFrom
        {- 
          enumFromThen x y =
            enumFromThenTo x y $ if y >= x then maxBound else minBound 
        -}
        , funXY 'enumFromThen $
            appV 'enumFromThenTo
              [ VarE x
              , VarE y
              , CondE (appVN '(>=) [x, y]) (VarE 'maxBound) (VarE 'minBound)
              ]
        , inline 'enumFromThen
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
        , FunD 'enumFromTo $ return $
            Clause
              [VarP x, VarP y]
              (NormalB $
                 CaseE (appVN 'compare [y, x])
                   [ Match
                       (ConP 'LT [])
                       (NormalB $ appC '(:) [VarE x, appVN down [y, x]])
                       []
                   , Match
                       (ConP 'EQ [])
                       (NormalB $ appC '(:) [VarE x, ConE '[]])
                       []
                   , Match
                       (ConP 'GT [])
                       (NormalB $ appC '(:) [VarE x, appVN up [y, x]])
                       []
                   ])
              [ FunD down $ return $
                  Clause [VarP to, VarP c]
                    (NormalB $
                       appC '(:)
                         [ VarE next
                         , CondE (appVN '(==) [next, to])
                                 (ConE '[]) (appVN down [to, next])
                         ])
                    [ValD (VarP next)
                          (NormalB $ appV '(-) [VarE c, litI 1]) []]
              , FunD up $ return $
                  Clause [VarP to, VarP c]
                    (NormalB $
                       appC '(:)
                         [ VarE next
                         , CondE (appVN '(==) [next, to])
                                 (ConE '[]) (appVN up [to, next])
                         ])
                    [ValD (VarP next)
                          (NormalB $ appV '(+) [VarE c, litI 1]) []]
              ]
#ifdef HAVE_TH_INLINABLE
        , inlinable 'enumFromTo
#endif
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
        , FunD 'enumFromThenTo $ return $
            Clause [VarP x, VarP y, VarP z]
              (NormalB $
                CaseE (appVN 'compare [y, x])
                  [ Match
                      (ConP 'LT [])
                      (NormalB $
                         CondE (appVN '(>) [z, x])
                               (ConE '[])
                               (appV down [appVN '(-) [x, y], VarE z, VarE x]))
                      []
                  , Match (ConP 'EQ []) (NormalB $ appVN 'repeat [x]) []
                  , Match
                      (ConP 'GT [])
                      (NormalB $
                         CondE (appVN '(<) [z, x]) (ConE '[])
                               (appV up [appVN '(-) [y, x], VarE z, VarE x]))
                      []
                  ])
              [ FunD down $ return $
                  Clause [VarP step, VarP to, VarP c]
                    (NormalB $
                       appC '(:)
                         [ VarE c
                         , CondE (appVN '(<) [next, to])
                                 (ConE '[]) (appVN down [step, to, next])
                         ])
                    [ValD (VarP next) (NormalB $ appVN '(-) [c, step]) []]
              , FunD up $ return $
                  Clause [VarP step, VarP to, VarP c]
                    (NormalB $
                       appC '(:)
                         [ VarE c
                         , CondE (appVN '(==) [next, to])
                                 (ConE '[]) (appVN up [step, to, next])
                         ])
                    [ValD (VarP next) (NormalB $ appVN '(+) [c, step]) []]]
#ifdef HAVE_TH_INLINABLE
        , inlinable 'enumFromThenTo
#endif
        ]
    , inst ''UnwrappedAdd [tp] $ return $
        {-
          UNSIGNED:
            unwrappedAdd (W hi lo) (W hi' lo') = (W 0 z, W y x)
              where (t1, x) = unwrappedAdd lo lo' 
                    (t3, t2) = unwrappedAdd hi (fromIntegral t1)
                    (t4, y) = unwrappedAdd t2 hi'
                    z = fromIntegral $ t3 + t4
          SIGNED:
            unwrappedAdd (W hi lo) (W hi' lo') = (z, x)
              where t1 = if hi < 0 then maxBound else minBound
                    t2 = if hi' < 0 then maxBound else minBound
                    (y, x) = unwrappedAdd (U (fromIntegral hi) lo)
                                          (U (fromIntegral hi') lo')
                    z = fromIntegral $ y + t1 + t2
        -}
        if signed
        then
          funHiLo2' 'unwrappedAdd (TupE [VarE z, VarE x])
            [ val t1 $ CondE (appV '(<) [VarE hi, litI 0])
                             (VarE 'maxBound) (VarE 'minBound)
            , val t2 $ CondE (appV '(<) [VarE hi', litI 0])
                             (VarE 'maxBound) (VarE 'minBound)
            , vals [y, x] $
                appV 'unwrappedAdd
                  [ appC ocn [appVN 'fromIntegral [hi], VarE lo]
                  , appC ocn [appVN 'fromIntegral [hi'], VarE lo'] ]
            , val z $
                appV 'fromIntegral [appV '(+) [VarE y, appVN '(+) [t1, t2]]]
            ]
        else
          funHiLo2' 'unwrappedAdd
            (TupE [appW [litI 0, VarE z], appWN [y, x]])
            [ vals [t1, x] $ appVN 'unwrappedAdd [lo, lo']
            , vals [t3, t2] $
                appV 'unwrappedAdd [VarE hi, appVN 'fromIntegral [t1]]
            , vals [t4, y] $ appVN 'unwrappedAdd [t2, hi']
            , val z $ appV 'fromIntegral [appVN '(+) [t3, t4]]
            ]
    , inst ''UnwrappedMul [tp] $ return $
        {-
          UNSIGNED:
            unwrappedMul (W hi lo) (W hi' lo') =
                (W (hhh + fromIntegral (shiftR t9 y) + shiftL x z)
                   (shiftL t9 z .|. shiftR t3 y),
                 W (fromIntegral t3) lll)
              where (llh, lll) = unwrappedMul lo lo'
                    (hlh, hll) = unwrappedMul (fromIntegral hi) lo'
                    (lhh, lhl) = unwrappedMul lo (fromIntegral hi')
                    (hhh, hhl) = unwrappedMul hi hi'
                    (t2, t1) = unwrappedAdd llh hll
                    (t4, t3) = unwrappedAdd t1 lhl
                    (t6, t5) = unwrappedAdd (fromIntegral hhl) (t2 + t4)
                    (t8, t7) = unwrappedAdd t5 lhh
                    (t10, t9) = unwrappedAdd t7 hlh
                    x = fromIntegral $ t6 + t8 + t10
                    y = bitSize (undefined ∷ H)
                    z = bitSize (undefined ∷ L) - y
          SIGNED:
            unwrappedMul (W hi lo) (W hi' lo') = (x, y)
              where t1 = W (complement hi') (complement lo') + 1
                    t2 = W (complement hi) (complement lo) + 1
                    (t3, y) = unwrappedMul (W (fromIntegral hi) lo)
                                           (W (fromIntegral hi') lo')
                    z = fromIntegral t3
                    x = if hi < 0
                        then if hi' < 0
                             then z + t1 + t2
                             else z + t1
                        else if hi' < 0
                             then z + t2
                             else z
        -}
        if signed
        then
          funHiLo2' 'unwrappedMul (TupE [VarE x, VarE y])
            [ val t1 $
                appV '(+) [ appW [ appVN 'complement [hi']
                                 , appVN 'complement [lo'] ]
                          , litI 1 ]
            , val t2 $
                appV '(+) [ appW [ appVN 'complement [hi]
                                 , appVN 'complement [lo] ]
                          , litI 1 ]
            , vals [t3, y] $
                appV 'unwrappedMul
                  [ appC ocn [appVN 'fromIntegral [hi], VarE lo]
                  , appC ocn [appVN 'fromIntegral [hi'], VarE lo'] ]
            , val z $ appVN 'fromIntegral [t3]
            , val x $
                CondE (appV '(<) [VarE hi, litI 0])
                  (CondE (appV '(<) [VarE hi', litI 0])
                     (appV '(+) [VarE z, appVN '(+) [t1, t2]])
                     (appVN '(+) [z, t1]))
                  (CondE (appV '(<) [VarE hi', litI 0])
                     (appVN '(+) [z, t2]) (VarE z))
            ]
        else
          funHiLo2' 'unwrappedMul
            (TupE [ appW
                      [ appV '(+)
                          [ VarE hhh
                          , appV '(+)
                              [ appV 'fromIntegral [appVN 'shiftR [t9, y]]
                              , appVN 'shiftL [x, z] ]
                          ]
                      , appV '(.|.) [ appVN 'shiftL [t9, z]
                                    , appVN 'shiftR [t3, y] ]
                      ]
                  , appW [appVN 'fromIntegral [t3], VarE lll]
                  ])
            [ vals [llh, lll] $ appVN 'unwrappedMul [lo, lo']
            , vals [hlh, hll] $
                appV 'unwrappedMul [appVN 'fromIntegral [hi], VarE lo']
            , vals [lhh, lhl] $
                appV 'unwrappedMul [VarE lo, appVN 'fromIntegral [hi']]
            , vals [hhh, hhl] $ appVN 'unwrappedMul [hi, hi']
            , vals [t2, t1] $ appVN 'unwrappedAdd [llh, hll]
            , vals [t4, t3] $ appVN 'unwrappedAdd [t1, lhl]
            , vals [t6, t5] $
                appV 'unwrappedAdd [ appVN 'fromIntegral [hhl]
                                   , appVN '(+) [t2, t4] ]
            , vals [t8, t7] $ appVN 'unwrappedAdd [t5, lhh]
            , vals [t10, t9] $ appVN 'unwrappedAdd [t7, hlh]
            , val x $
                appV 'fromIntegral
                  [appV '(+) [VarE t6, appVN '(+) [t8, t10]]]
            , val y $ appV 'bitSize [SigE (VarE 'undefined) hiT]
            , val z $ appV '(-) [ appV 'bitSize [SigE (VarE 'undefined) loT]
                                , VarE y ]
            ]
    , inst ''Num [tp]
        {-
          negate (W hi lo) = if lo == 0 then W (negate hi) 0
                                        else W (negate $ hi + 1) (negate lo)
        -}
        [ funHiLo 'negate $
            CondE (appV '(==) [VarE lo, litI 0])
                  (appW [appVN 'negate [hi], litI 0])
                  (appW [ appV 'negate [appV '(+) [litI 1, VarE hi]]
                        , appVN 'negate [lo] ])
        , inline 'negate
        {- 
          abs x = if SIGNED
                  then if x < 0 then negate x else x 
                  else x
        -}
        , funX 'abs $
            if signed
            then CondE (appV '(<) [VarE x, litI 0])
                       (appVN 'negate [x]) (VarE x)
            else VarE x
        , inline 'abs
        {-
          signum (W hi lo) = if SIGNED
                             then case hi `compare` 0 of
                               LT → W (-1) maxBound
                               EQ → if lo == 0 then W 0 0 else W 0 1
                               GT → W 0 1
                             else if hi == 0 && lo == 0 then W 0 0 else W 0 1
        -}
        , funHiLo 'signum $
            if signed
            then CaseE (appV 'compare [VarE hi, litI 0])
                   [ Match (ConP 'LT [])
                           (NormalB $ appW [litI (-1), VarE 'maxBound]) []
                   , Match (ConP 'EQ [])
                           (NormalB $ CondE (appV '(==) [VarE lo, litI 0])
                                            (appW [litI 0, litI 0])
                                            (appW [litI 0, litI 1]))
                           []
                   , Match (ConP 'GT [])
                           (NormalB $ appW [litI 0, litI 1]) []
                   ]
            else CondE (appV '(&&) [ appV '(==) [VarE hi, litI 0]
                                   , appV '(==) [VarE lo, litI 0] ])
                       (appW [litI 0, litI 0]) (appW [litI 0, litI 1])
        , inline 'signum
        {-
          (W hi lo) + (W hi' lo') = W y x
            where x = lo + lo'
                  y = hi + hi' + if x < lo then 1 else 0
        -}
        , funHiLo2' '(+) (appWN [y, x])
            [ val x $ appVN '(+) [lo, lo']
            , val y $ appV '(+)
                        [ appVN '(+) [hi, hi']
                        , CondE (appVN '(<) [x, lo]) (litI 1) (litI 0) ]
            ]
        , inline '(+)
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
        , if signed
          then
            funHiLo2' '(*)
              (appW [appVN 'fromIntegral [x], VarE y])
              [ValD (ConP ocn [VarP x, VarP y])
                (NormalB $
                  appV '(*)
                    [ appC ocn [appVN 'fromIntegral [hi], VarE lo]
                    , appC ocn [appVN 'fromIntegral [hi'], VarE lo'] ])
                []]
          else
            funHiLo2' '(*)
              (appW [ appV '(+)
                        [ appV '(+)
                            [ appV '(*) [VarE hi, appVN 'fromIntegral [lo']]
                            , appV '(*) [VarE hi', appVN 'fromIntegral [lo]] ]
                        , appVN 'fromIntegral [x] ]
                    , VarE y ])
              [vals [x, y] (appVN 'unwrappedMul [lo, lo'])]
        , inline '(*)
        {-
          fromInteger x = W (fromInteger y) (fromInteger z)
            where (y, z) = x `divMod` (toInteger (maxBound ∷ L) + 1)
        -}
        , funX' 'fromInteger
            (appW [appVN 'fromInteger [y], appVN 'fromInteger [z]])
            [vals [y, z]
               (appV 'divMod
                  [ VarE x
                  , appV '(+)
                      [appV 'toInteger [SigE (VarE 'maxBound) loT], litI 1]
                  ])]
#ifdef HAVE_TH_INLINABLE
        , inlinable 'fromInteger
#endif
        ]
    , inst ''Real [tp]
        {- toRational x = toInteger x % 1 -}
        [ funX 'toRational $ appV '(%) [appVN 'toInteger [x], litI 1]
        , inline 'toRational ]
    , inst ''Integral [tp]
        {-
          toInteger (W hi lo) =
            toInteger hi * (toInteger (maxBound ∷ L) + 1) + toInteger lo
        -}
        [ funHiLo 'toInteger $
            appV '(+)
              [ appV '(*)
                  [ appVN 'toInteger [hi]
                  , appV '(+)
                      [appV 'toInteger [SigE (VarE 'maxBound) loT], litI 1] ]
              , appVN 'toInteger [lo] ]
        {-
          UNSIGNED:
            quotRem x@(W hi lo) y@(W hi' lo') =
                if hi' == 0 && lo' == 0
                then error "divide by zero"
                else case compare hi hi' of
                  LT → (0, x)
                  EQ → compare lo lo' of
                    LT → (0, x)
                    EQ → (1, 0)
                    GT | hi' == 0 → (W 0 t2, W 0 t1)
                      where (t2, t1) = quotRem lo lo'
                    GT → (1, lo - lo')
                  GT | lo' == 0 → (W 0 (fromIntegral t2),
                                   W (fromIntegral t1) lo)
                    where (t2, t1) = quotRem hi hi'
                  GT | hi' == 0 && lo' == maxBound → 
                      if t2 == 0
                      then if t1 == maxBound
                           then (W 0 z + 1, 0)
                           else (W 0 z, t1)
                      else if t1 == maxBound
                           then (W 0 z + 2, 1)
                           else if t1 == xor maxBound 1
                                then (W 0 z + 2, 0)
                                else (W 0 z + 1, W 0 (t1 + 1))
                    where z = fromIntegral hi
                          (t2, t1) = unwrappedAdd z lo
                  GT | hi' == 0 → (t2, W 0 t1)
                    where (t2, t1) = div1 hi lo lo'
                  GT → if t1 == t2
                       then (1, x - y)
                       else (W 0 (fromIntegral q2), shiftR r2 t2)
                    where t1 = leadingZeroes hi
                          t2 = leadingZeroes hi'
                          z = shiftR hi (bitSize (undefined ∷ H) - t2)
                          W hhh hll = shiftL x t2
                          v@(W lhh lll) = shiftL y t2
                          -- z hhh hll / lhh lll
                          ((0, q1), r1) = div2 z hhh lhh
                          (t4, t3) = unwrappedMul (fromIntegral q1) lll
                          t5 = W (fromIntegral t4) t3
                          t6 = W r1 hll
                          (t8, t7) = unwrappedAdd t6 v
                          (t10, t9) = unwrappedAdd t7 v
                          (q2, r2) =
                            if t5 > t6
                            then
                              if loWord t8 == 0
                              then
                                if t7 >= t5
                                then (q1 - 1, t7 - t5)
                                else
                                  if loWord t10 == 0
                                  then (q1 - 2, t9 - t5)
                                  else (q1 - 2, (maxBound - t5) + t9 + 1)
                              else
                                (q1 - 1, (maxBound - t5) + t7 + 1) 
                            else
                              (q1, t6 - t5)
            where div1 hhh hll by = go hhh hll 0
                    where (t2, t1) = quotRem maxBound by
                          go h l c =
                              if z == 0
                              then (c + W (fromIntegral t8) t7 + W 0 t10, t9)
                              else go (fromIntegral z) t5
                                      (c + (W (fromIntegral t8) t7))
                            where h1 = fromIntegral h
                                  (t4, t3) = unwrappedMul h1 (t1 + 1)
                                  (t6, t5) = unwrappedAdd t3 l
                                  z = t4 + t6
                                  (t8, t7) = unwrappedMul h1 t2
                                  (t10, t9) = quotRem t5 by
                  div2 hhh hll by = go hhh hll (0, 0)
                    where (t2, t1) = quotRem maxBound by
                          go h l c =
                              if z == 0
                              then (addT (addT c (t8, t7)) (0, t10), t9)
                              else go z t5 (addT c (t8, t7))
                            where (t4, t3) = unwrappedMul h (t1 + 1)
                                  (t6, t5) = unwrappedAdd t3 l
                                  z = t4 + t6
                                  (t8, t7) = unwrappedMul h t2
                                  (t10, t9) = quotRem t5 by
                          addT (lhh, lhl) (llh, lll) = (lhh + llh + t4, t3)
                            where (t4, t3) = unwrappedAdd lhl lll

          SIGNED:
            quotRem x y =
              if x >= 0
              then
                if y >= 0
                then let (q, r) = quotRem (fromIntegral x ∷ U)
                                          (fromIntegral y) in
                       (fromIntegral q, fromIntegral r)
                else let (q, r) = quotRem (fromIntegral x ∷ U)
                                          (negate $ fromIntegral y) in
                       (fromIntegral $ negate q, fromIntegral r)
              else
                if y >= 0
                then let (q, r) = quotRem (negate $ fromIntegral x ∷ U)
                                          (fromIntegral y) in
                       (fromIntegral $ negate q, fromIntegral $ negate r)
                else let (q, r) = quotRem (negate $ fromIntegral x ∷ U)
                                          (negate $ fromIntegral y) in
                       (fromIntegral q, fromIntegral $ negate r)
        -}
        , if signed
          then
            funXY 'quotRem $
              CondE (appV '(>=) [VarE x, litI 0])
                (CondE (appV '(>=) [VarE y, litI 0])
                   (LetE [vals [q, r] $
                            appV 'quotRem
                              [ SigE (appVN 'fromIntegral [x]) (ConT otp)
                              , appVN 'fromIntegral [y] ]]
                      (TupE [ appVN 'fromIntegral [q]
                            , appVN 'fromIntegral [r] ]))
                   (LetE [vals [q, r] $
                            appV 'quotRem
                              [ SigE (appVN 'fromIntegral [x]) (ConT otp)
                              , appV 'fromIntegral [appVN 'negate [y]] ]]
                      (TupE [ appV 'fromIntegral [appVN 'negate [q]]
                            , appVN 'fromIntegral [r] ])))
                (CondE (appV '(>=) [VarE y, litI 0])
                   (LetE [vals [q, r] $
                            appV 'quotRem
                              [ SigE (appV 'fromIntegral [appVN 'negate [x]])
                                     (ConT otp)
                              , appVN 'fromIntegral [y] ]]
                      (TupE [ appV 'fromIntegral [appVN 'negate [q]]
                            , appV 'fromIntegral [appVN 'negate [r]] ]))
                   (LetE [vals [q, r] $
                            appV 'quotRem
                              [ SigE (appV 'fromIntegral [appVN 'negate [x]])
                                     (ConT otp)
                              , appV 'fromIntegral [appVN 'negate [y]] ]]
                      (TupE [ appVN 'fromIntegral [q]
                            , appV 'fromIntegral [appVN 'negate [r]] ])))
          else
            funHiLo2XY' 'quotRem
              (CondE (appV '(&&) [ appV '(==) [VarE hi', litI 0]
                                 , appV '(==) [VarE lo', litI 0] ])
                 (appV 'error [litS "divide by zero"])
                 (CaseE (appVN 'compare [hi, hi'])
                    [ match (ConP 'LT []) (TupE [litI 0, VarE x])
                    , match (ConP 'EQ [])
                        (CaseE (appVN 'compare [lo, lo'])
                           [ match (ConP 'LT []) (TupE [litI 0, VarE x])
                           , match (ConP 'EQ []) (TupE [litI 1, litI 0])
                           , Match (ConP 'GT [])
                               (GuardedB $ return
                                  ( NormalG (appV '(==) [VarE hi', litI 0])
                                  , TupE [ appW [litI 0, VarE t2]
                                         , appW [litI 0, VarE t1] ]))
                               [vals [t2, t1] $ appVN 'quotRem [lo, lo']]
                           , match (ConP 'GT []) $
                               TupE [ litI 1
                                    , appW [litI 0, appVN '(-) [lo, lo']] ]
                           ])
                    , Match (ConP 'GT [])
                        (GuardedB $ return
                           ( NormalG (appV '(==) [VarE lo', litI 0])
                           , TupE
                               [ appW [litI 0, appVN 'fromIntegral [t2]]
                               , appW [appVN 'fromIntegral [t1], VarE lo]
                               ] ))
                        [vals [t2, t1] $ appVN 'quotRem [hi, hi']]
                    , Match (ConP 'GT [])
                        (GuardedB $ return
                           ( NormalG (appV '(&&)
                                        [ appV '(==) [VarE hi', litI 0]
                                        , appVN '(==) [lo', 'maxBound] ])
                           , CondE (appV '(==) [VarE t2, litI 0])
                               (CondE (appVN '(==) [t1, 'maxBound])
                                  (TupE
                                     [ appV '(+)
                                         [ appW [litI 0, VarE z] 
                                         , litI 1 ]
                                     , litI 0 ])
                                  (TupE
                                     [ appW [litI 0, VarE z]
                                     , appW [litI 0, VarE t1] ]))
                               (CondE (appVN '(==) [t1, 'maxBound])
                                  (TupE
                                     [ appV '(+)
                                         [appW [litI 0, VarE z], litI 2]
                                     , litI 1 ])
                                  (CondE
                                     (appV '(==)
                                        [ VarE t1
                                        , appV 'xor [VarE 'maxBound, litI 1]
                                        ])
                                     (TupE
                                        [ appV '(+)
                                            [appW [litI 0, VarE z], litI 2]
                                        , litI 0 ])
                                     (TupE
                                        [ appV '(+)
                                            [appW [litI 0,VarE z], litI 1]
                                        , appW [ litI 0
                                               , appV '(+) [VarE t1, litI 1] ]
                                        ])))
                           ))
                        [ val z $ appVN 'fromIntegral [hi]
                        , vals [t2, t1] $ appVN 'unwrappedAdd [z, lo] ]
                    , Match (ConP 'GT [])
                        (GuardedB $ return
                           ( NormalG (appV '(==) [VarE hi', litI 0])
                           , TupE [VarE t2, appW [litI 0, VarE t1]] ))
                        [vals [t2, t1] $ appVN div1 [hi, lo, lo']]
                    , match' (ConP 'GT [])
                        (CondE (appVN '(==) [t1, t2])
                               (TupE [litI 1, appVN '(-) [x, y]])
                               (TupE [ appW [litI 0, appVN 'fromIntegral [q2]]
                                     , appVN 'shiftR [r2, t2] ]))
                        [ val t1 $ appVN 'leadingZeroes [hi]
                        , val t2 $ appVN 'leadingZeroes [hi']
                        , val z $ appV 'shiftR
                                    [ VarE hi
                                    , appV '(-)
                                        [ appV 'bitSize
                                            [SigE (VarE 'undefined) hiT]
                                        , VarE t2 ]
                                    ]
                        , ValD (ConP cn [VarP hhh, VarP hll])
                            (NormalB $ appVN 'shiftL [x, t2]) [] 
                        , ValD (AsP v $ ConP cn [VarP lhh, VarP lll])
                            (NormalB $ appVN 'shiftL [y, t2]) []
                        , ValD (TupP [ TupP [LitP (IntegerL 0), VarP q1]
                                     , VarP r1 ])
                            (NormalB $ appVN div2 [z, hhh, lhh]) []
                        , vals [t4, t3] $
                            appV 'unwrappedMul
                              [appVN 'fromIntegral [q1], VarE lll]
                        , val t5 $ appW [appVN 'fromIntegral [t4], VarE t3]
                        , val t6 $ appWN [r1, hll]
                        , vals [t8, t7] $ appVN 'unwrappedAdd [t6, v]
                        , vals [t10, t9] $ appVN 'unwrappedAdd [t7, v]
                        , vals [q2, r2] $
                            CondE (appVN '(>) [t5, t6])
                              (CondE (appV '(==) [appVN 'loWord [t8], litI 0])
                                 (CondE (appVN '(>=) [t7, t5])
                                    (TupE [ appV '(-) [VarE q1, litI 1]
                                          , appVN '(-) [t7, t5] ])
                                    (CondE (appV '(==) [ appVN 'loWord [t10]
                                                       , litI 0 ])
                                       (TupE [ appV '(-) [VarE q1, litI 2]
                                             , appVN '(-) [t9, t5] ])
                                       (TupE [ appV '(-) [VarE q1, litI 2]
                                             , appV '(+)
                                                 [ appVN '(-) ['maxBound, t5]
                                                 , appV '(+) [VarE t9, litI 1]
                                                 ]
                                             ])))
                                 (TupE [ appV '(-) [VarE q1, litI 1]
                                       , appV '(+)
                                           [ appVN '(-) ['maxBound, t5]
                                           , appV '(+) [VarE t7, litI 1] ]
                                       ]))
                              (TupE [VarE q1, appVN '(-) [t6, t5]])
                        ]
                    ]))
              [ FunD div1 $ return $
                  Clause [VarP hhh, VarP hll, VarP by]
                    (NormalB (appV go [VarE hhh, VarE hll, litI 0]))
                    [ vals [t2, t1] $ appVN 'quotRem ['maxBound, by]
                    , FunD go $ return $
                        Clause [VarP h, VarP l, VarP c]
                          (NormalB
                             (CondE (appV '(==) [VarE z, litI 0])
                                (TupE [ appV '(+)
                                          [ VarE c
                                          , appV '(+)
                                              [ appW [ appVN 'fromIntegral [t8]
                                                     , VarE t7 ]
                                              , appW [litI 0, VarE t10] ]
                                          ]
                                      , VarE t9 ])
                                (appV go
                                   [ appVN 'fromIntegral [z]
                                   , VarE t5
                                   , appV '(+)
                                       [ VarE c
                                       , appW [ appVN 'fromIntegral [t8]
                                              , VarE t7 ]
                                       ]
                                   ])))
                          [ val h1 $ appVN 'fromIntegral [h]
                          , vals [t4, t3] $
                              appV 'unwrappedMul
                                [VarE h1, appV '(+) [VarE t1, litI 1]]
                          , vals [t6, t5] $ appVN 'unwrappedAdd [t3, l]
                          , val z $ appVN '(+) [t4, t6]
                          , vals [t8, t7] $ appVN 'unwrappedMul [h1, t2]
                          , vals [t10, t9] $ appVN 'quotRem [t5, by] ]
                    ]
              , FunD div2 $ return $
                  Clause [VarP hhh, VarP hll, VarP by]
                    (NormalB (appV go [ VarE hhh
                                      , VarE hll
                                      , TupE [litI 0, litI 0]]))
                    [ vals [t2, t1] $ appVN 'quotRem ['maxBound, by]
                    , FunD go $ return $
                        Clause [VarP h, VarP l, VarP c]
                          (NormalB
                             (CondE (appV '(==) [VarE z, litI 0])
                                (TupE [ appV addT
                                          [ VarE c
                                          , appV addT
                                              [ TupE [VarE t8 , VarE t7]
                                              , TupE [litI 0, VarE t10] ]
                                          ]
                                      , VarE t9 ])
                                (appV go
                                   [ VarE z
                                   , VarE t5
                                   , appV addT
                                       [ VarE c
                                       , TupE [VarE t8, VarE t7]
                                       ]
                                   ])))
                          [ vals [t4, t3] $
                              appV 'unwrappedMul
                                [VarE h, appV '(+) [VarE t1, litI 1]]
                          , vals [t6, t5] $ appVN 'unwrappedAdd [t3, l]
                          , val z $ appVN '(+) [t4, t6]
                          , vals [t8, t7] $ appVN 'unwrappedMul [h, t2]
                          , vals [t10, t9] $ appVN 'quotRem [t5, by] ]
                    , FunD addT $ return $
                        Clause [ TupP [VarP lhh, VarP lhl]
                               , TupP [VarP llh, VarP lll]
                               ]
                          (NormalB (TupE [ appV '(+)
                                             [ VarE t4
                                             , appVN '(+) [lhh, llh]
                                             ]
                                         , VarE t3
                                         ]))
                          [vals [t4, t3] $ appVN 'unwrappedAdd [lhl, lll]]
                    ]
              ]
        {-
          UNSIGNED:
            divMod = quotRem

          SIGNED:
            divMod x y =
              if x >= 0
              then
                if y >= 0
                then let (q, r) = quotRem (fromIntegral x ∷ U)
                                          (fromIntegral y) in
                       (fromIntegral q, fromIntegral r)
                else let (q, r) = quotRem (fromIntegral x ∷ U)
                                          (negate $ fromIntegral y)
                         q1 = fromIntegral (negate q)
                         r1 = fromIntegral r in
                       if r == 0
                       then (q1, r1)
                       else (q1 - 1, r1 + y)
              else
                if y >= 0
                then let (q, r) = quotRem (negate $ fromIntegral x ∷ U)
                                          (fromIntegral y)
                         q1 = fromIntegral (negate q)
                         r1 = fromIntegral (negate r) in
                       if r == 0
                       then (q1, r1)
                       else (q1 - 1, r1 + y)
                else let (q, r) = quotRem (negate $ fromIntegral x ∷ U)
                                          (negate $ fromIntegral y) in
                       (fromIntegral q, fromIntegral $ negate r)
        -}
        , if signed
          then
            funXY 'divMod $
              CondE (appV '(>=) [VarE x, litI 0])
                (CondE (appV '(>=) [VarE y, litI 0])
                   (LetE [vals [q, r] $
                            appV 'quotRem
                              [ SigE (appVN 'fromIntegral [x]) (ConT otp)
                              , appVN 'fromIntegral [y] ]]
                      (TupE [ appVN 'fromIntegral [q]
                            , appVN 'fromIntegral [r] ]))
                   (LetE [ vals [q, r] $
                             appV 'quotRem
                               [ SigE (appVN 'fromIntegral [x]) (ConT otp)
                               , appV 'fromIntegral [appVN 'negate [y]] ]
                         , val q1 $ appV 'fromIntegral [appVN 'negate [q]]
                         , val r1 $ appVN 'fromIntegral [r]
                         ]
                      (CondE (appV '(==) [VarE r, litI 0])
                         (TupE [VarE q1, VarE r1])
                         (TupE [ appV '(-) [VarE q1, litI 1]
                               , appVN '(+) [r1, y] ]))))
                (CondE (appV '(>=) [VarE y, litI 0])
                   (LetE [ vals [q, r] $
                             appV 'quotRem
                               [ SigE (appV 'fromIntegral [appVN 'negate [x]])
                                      (ConT otp)
                               , appVN 'fromIntegral [y] ]
                         , val q1 $ appV 'fromIntegral [appVN 'negate [q]]
                         , val r1 $ appV 'fromIntegral [appVN 'negate [r]]
                         ]
                      (CondE (appV '(==) [VarE r, litI 0])
                         (TupE [VarE q1, VarE r1])
                         (TupE [ appV '(-) [VarE q1, litI 1]
                               , appVN '(+) [r1, y] ])))
                   (LetE [vals [q, r] $
                            appV 'quotRem
                              [ SigE (appV 'fromIntegral [appVN 'negate [x]])
                                     (ConT otp)
                              , appV 'fromIntegral [appVN 'negate [y]] ]]
                      (TupE [ appVN 'fromIntegral [q]
                            , appV 'fromIntegral [appVN 'negate [r]] ])))
          else
            fun 'divMod $ VarE 'quotRem
        , inline 'divMod
        ]
    , inst ''Show [tp]
        [ fun 'show $ appVN '(.) ['show, 'toInteger]
        , inline 'show ]
    , inst ''Hashable [tp]
        {- hash (W hi lo) = hash hi `combine` hash lo -}
        [ funHiLo 'hash $ appV 'combine [appVN 'hash [hi], appVN 'hash [lo]]
        , inline 'hash
        , inline 'hashWithSalt ]
    , inst ''Ix [tp]
        {- range (x, y) = enumFromTo x y -}
        [ funTup 'range $ appVN 'enumFromTo [x, y]
        , inline 'range
        {- unsafeIndex (x, _) z = fromIntegral z - fromIntegral x -}
        , funTupLZ 'unsafeIndex $
            appV '(-) [appVN 'fromIntegral [z], appVN 'fromIntegral [x]]
        , inline 'unsafeIndex
        {- inRange (x, y) z = z >= x && z <= y -}
        , funTupZ 'inRange $
            appV '(&&) [appVN '(>=) [z, x], appVN '(<=) [z, y]]
        , inline 'inRange ]
    , inst ''Bits [tp]
        {- bitSize _ = bitSize (undefined ∷ H) + bitSize (undefined ∷ L) -}
        [ fun_ 'bitSize $
            appV '(+)
              [ appV 'bitSize [SigE (VarE 'undefined) hiT]
              , appV 'bitSize [SigE (VarE 'undefined) loT] ]
        , inline 'bitSize
        {- isSigned _ = SIGNED -}
        , fun_ 'isSigned $ ConE $ if signed then 'True else 'False
        , inline 'isSigned
        {- complement (W hi lo) = W (complement hi) (complement lo) -}
        , funHiLo 'complement $
            appW [appVN 'complement [hi], appVN 'complement [lo]]
        , inline 'complement
        {- xor (W hi lo) (W hi' lo') = W (xor hi hi') (xor lo lo') -}
        , funHiLo2 'xor $ appW [appVN 'xor [hi, hi'], appVN 'xor [lo, lo']]
        , inline 'xor
        {- (W hi lo) .&. (W hi' lo') = W (hi .&. hi') (lo .&. lo') -}
        , funHiLo2 '(.&.) $
            appW [appVN '(.&.) [hi, hi'], appVN '(.&.) [lo, lo']]
        , inline '(.&.)
        {- (W hi lo) .|. (W hi' lo') = W (hi .|. hi') (lo .|. lo') -}
        , funHiLo2 '(.|.) $
            appW [appVN '(.|.) [hi, hi'], appVN '(.|.) [lo, lo']]
        , inline '(.|.)
        {-
          shiftL (W hi lo) x =
              if y > 0
                then W (shiftL hi x .|. fromIntegral (shiftR lo y))
                       (shiftL lo x)
                else W (fromIntegral $ shiftL lo $ negate y) 0
            where y = bitSize (undefined ∷ L) - x
        -}
        , funHiLoX' 'shiftL
            (CondE (appV '(>) [VarE y, litI 0])
                   (appW
                      [ appV '(.|.)
                          [ appVN 'shiftL [hi, x]
                          , appV 'fromIntegral [appVN 'shiftR [lo, y]] ]
                      , appVN 'shiftL [lo, x] ])
                   (appW [ appV 'fromIntegral
                             [appV 'shiftL [VarE lo, appVN 'negate [y]]]
                         , litI 0 ]))
            [val y $
               appV '(-) [ appV 'bitSize [SigE (VarE 'undefined) loT]
                         , VarE x ]]
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
        , funHiLoX' 'shiftR
            (appW [ appVN 'shiftR [hi, x]
                  , CondE (appV '(>=) [VarE y, litI 0])
                          (appV '(.|.)
                             [ appV 'shiftL
                                 [appVN 'fromIntegral [hi], VarE y]
                             , appVN 'shiftR [lo, x] ])
                          (VarE z) ])
            [ val y $ appV '(-) [ appV 'bitSize [SigE (VarE 'undefined) loT]
                                , VarE x ]
            , val z $
                if signed
                then appV 'fromIntegral
                       [appV 'shiftR
                          [ SigE (appVN 'fromIntegral [hi])
                                 (AppT (ConT ''SignedWord) loT)
                          , appVN 'negate [y] ]]
                else appV 'shiftR [ appVN 'fromIntegral [hi]
                                  , appVN 'negate [y] ]
            ]
        {-
          UNSIGNED:
            rotateL (W hi lo) x =
                if y >= 0
                then W (fromIntegral (shiftL lo y) .|. shiftR hi z)
                     W (shiftL (fromIntegral hi) (bitSize (undefined ∷ L) - z)
                        .|. shiftR lo z)
                else W (fromIntegral (shiftR lo $ negate y) .|. shiftL hi x)
                       (shift (fromIntegral hi) (bitSize (undefined ∷ L) - z)
                        .|. shiftL lo x
                        .|. shiftR lo z)
              where y = x - bitSize (undefined ∷ L)
                    z = bitSize (undefined ∷ W) - x
          SIGNED:
            rotateL (W hi lo) x = W (fromIntegral hi') lo'
              where U hi' lo' = rotateL (U (fromIntegral hi) lo) x
        -}
        , if signed
          then
           funHiLoX' 'rotateL
             (appW [appVN 'fromIntegral [hi'], VarE lo'])
             [ValD (ConP ocn [VarP hi', VarP lo'])
                   (NormalB $
                      appV 'rotateL
                        [ appC ocn [appVN 'fromIntegral [hi], VarE lo]
                        , VarE x ]) []]
          else 
            funHiLoX' 'rotateL
              (CondE (appV '(>=) [VarE y, litI 0])
                 (appW
                    [ appV '(.|.)
                        [ appV 'fromIntegral [appVN 'shiftL [lo, y]]
                        , appVN 'shiftR [hi, z] ]
                    , appV '(.|.)
                        [ appV 'shiftL
                            [ appVN 'fromIntegral [hi]
                            , appV '(-)
                                [ appV 'bitSize [SigE (VarE 'undefined) loT]
                                , VarE z ]
                            ]
                        , appVN 'shiftR [lo, z] ]
                    ])
                 (appW
                    [ appV '(.|.)
                        [ appV 'fromIntegral
                            [appV 'shiftR [VarE lo, appVN 'negate [y]]]
                        , appVN 'shiftL [hi, x] ]
                    , appV '(.|.)
                        [ appV 'shift
                            [ appVN 'fromIntegral [hi]
                            , appV '(-)
                                [ appV 'bitSize [SigE (VarE 'undefined) loT]
                                , VarE z] ]
                        , appV '(.|.)
                            [appVN 'shiftL [lo, x], appVN 'shiftR [lo, z]] ]
                    ]))
              [ val y $
                  appV '(-) [ VarE x
                            , appV 'bitSize [SigE (VarE 'undefined) loT] ]
              , val z $
                  appV '(-)
                    [ appV 'bitSize [SigE (VarE 'undefined) (ConT tp)]
                    , VarE x ]
              ]
        {- rotateR x y = rotateL x $ bitSize (undefined ∷ W) - y -}
        , funXY 'rotateR $
            appV 'rotateL
              [ VarE x
              , appV '(-)
                  [appV 'bitSize [SigE (VarE 'undefined) (ConT tp)], VarE y]
              ]
        , inline 'rotateR
        {-
          bit x = if y >= 0 then W (bit y) 0 else W 0 (bit x)
            where y = x - bitSize (undefined ∷ LoWord W)
        -}
        , funX' 'bit (CondE (appV '(>=) [VarE y, litI 0])
                            (appW [appVN 'bit [y], litI 0])
                            (appW [litI 0, appVN 'bit [x]]))
            [val y $
               appV '(-) [ VarE x
                         , appV 'bitSize [SigE (VarE 'undefined) loT] ]]
        , inline 'bit
        {-
          setBit (W hi lo) x =
              if y >= 0 then W (setBit hi y) lo else W hi (setBit lo x)
            where y = x - bitSize (undefined ∷ L)
        -}
        , funHiLoX' 'setBit
            (CondE (appV '(>=) [VarE y, litI 0])
                   (appW [appVN 'setBit [hi, y], VarE lo])
                   (appW [VarE hi, appVN 'setBit [lo, x]]))
            [val y $
               appV '(-) [ VarE x
                         , appV 'bitSize [SigE (VarE 'undefined) loT] ]]
        , inline 'setBit
        {-
          clearBit (W hi lo) x =
              if y >= 0 then W (clearBit hi y) lo
                        else W hi (clearBit lo x)
            where y = x - bitSize (undefined ∷ L)
        -}
        , funHiLoX' 'clearBit
            (CondE (appV '(>=) [VarE y, litI 0])
                   (appW [appVN 'clearBit [hi, y], VarE lo])
                   (appW [VarE hi, appVN 'clearBit [lo, x]]))
            [val y $
               appV '(-) [ VarE x
                         , appV 'bitSize [SigE (VarE 'undefined) loT] ]]
        , inline 'clearBit
        {-
          complementBit (W hi lo) x =
              if y >= 0 then W (complementBit hi y) lo
                        else W hi (complementBit lo x)
            where y = x - bitSize (undefined ∷ L)
        -}
        , funHiLoX' 'complementBit
            (CondE (appV '(>=) [VarE y, litI 0])
                   (appW [appVN 'complementBit [hi, y], VarE lo])
                   (appW [VarE hi, appVN 'complementBit [lo, x]]))
            [val y $
               appV '(-) [ VarE x
                         , appV 'bitSize [SigE (VarE 'undefined) loT] ]]
        , inline 'complementBit
        {-
          testBit (W hi lo) x =
              if y >= 0 then testBit hi y else testBit lo x
            where y = x - bitSize (undefined ∷ L)
        -}
        , funHiLoX' 'testBit
            (CondE (appV '(>=) [VarE y, litI 0])
                   (appVN 'testBit [hi, y])
                   (appVN 'testBit [lo, x]))
            [val y $
               appV '(-) [ VarE x
                         , appV 'bitSize [SigE (VarE 'undefined) loT] ]]
        , inline 'testBit
#if MIN_VERSION_base(4,5,0)
        {- popCount (W hi lo) = popCount hi + popCount lo -}
        , funHiLo 'popCount
            (appV '(+) [appVN 'popCount [hi], appVN 'popCount [lo]])
        , inline 'popCount
#endif
        ]
    , inst ''LeadingZeroes [tp]
        {-
          UNSIGNED:
            leadingZeroes (W hi lo) =
                if x == y then y + leadingZeroes lo else x
              where x = leadingZeroes hi
                    y = bitSize (undefined ∷ H)
          SIGNED:
            leadingZeroes (W hi lo) = leadingZeroes (U (fromIntegral hi) lo)
        -}
        [ if signed
          then
            funHiLo 'leadingZeroes
              (appV 'leadingZeroes
                 [appC ocn [appVN 'fromIntegral [hi], VarE lo]])
          else
            funHiLo' 'leadingZeroes
              (CondE (appVN '(==) [x, y])
                     (appV '(+) [VarE y, appVN 'leadingZeroes [lo]])
                     (VarE x))
              [ val x $ appVN 'leadingZeroes [hi]
              , val y $ appV 'bitSize [SigE (VarE 'undefined) hiT]
              ]
        , inline 'leadingZeroes
        ]
    ]
  where
    x    = mkName "x"
    y    = mkName "y"
    z    = mkName "z"
    t1   = mkName "t1"
    t2   = mkName "t2"
    t3   = mkName "t3"
    t4   = mkName "t4"
    t5   = mkName "t5"
    t6   = mkName "t6"
    t7   = mkName "t7"
    t8   = mkName "t8"
    t9   = mkName "t9"
    t10  = mkName "t10"
    v    = mkName "v"
    q    = mkName "q"
    q1   = mkName "q1"
    q2   = mkName "q2"
    r    = mkName "r"
    r1   = mkName "r1"
    r2   = mkName "r2"
    lll  = mkName "lll"
    llh  = mkName "llh"
    lhl  = mkName "lhl"
    lhh  = mkName "lhh"
    hll  = mkName "hll"
    hlh  = mkName "hlh"
    hhl  = mkName "hhl"
    hhh  = mkName "hhh"
    h    = mkName "h"
    h1   = mkName "h1"
    l    = mkName "l"
    div1 = mkName "div1"
    div2 = mkName "div2"
    addT = mkName "addT"
    by   = mkName "by"
    go   = mkName "go"
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
    funXY' n e ds = FunD n [Clause [VarP x, VarP y] (NormalB e) ds]
    funXY n e     = funXY' n e []
    funTup n e    = FunD n [Clause [TupP [VarP x, VarP y]] (NormalB e) []]
    funTupZ n e   =
      FunD n [Clause [TupP [VarP x, VarP y], VarP z] (NormalB e) []]
    funTupLZ n e  =
      FunD n [Clause [TupP [VarP x, WildP], VarP z] (NormalB e) []]
    funLo n e     = FunD n [Clause [ConP cn [WildP, VarP lo]] (NormalB e) []]
    funHi n e     = FunD n [Clause [ConP cn [VarP hi, WildP]] (NormalB e) []]
    funHiLo n e   = funHiLo' n e []
    funHiLo' n e ds  =
      FunD n [Clause [ConP cn [VarP hi, VarP lo]] (NormalB e) ds]
    funHiLoX' n e ds =
      FunD n [Clause [ConP cn [VarP hi, VarP lo], VarP x] (NormalB e) ds]
    funHiLo2 n e     = funHiLo2' n e []
    funHiLo2' n e ds =
      FunD n [Clause [ ConP cn [VarP hi, VarP lo]
                     , ConP cn [VarP hi', VarP lo'] ]
                     (NormalB e) ds]
    funHiLo2XY' n e ds =
      FunD n [Clause [ AsP x (ConP cn [VarP hi, VarP lo])
                     , AsP y (ConP cn [VarP hi', VarP lo']) ]
                     (NormalB e) ds]
    match' p e ds = Match p (NormalB e) ds
    match p e     = match' p e []
#ifdef HAVE_TH_INLINABLE
    inline n = PragmaD $ InlineP n $ InlineSpec Inline False Nothing
    inlinable n = PragmaD $ InlineP n $ InlineSpec Inlinable False Nothing
#else
    inline n = PragmaD $ InlineP n $ InlineSpec True False Nothing
#endif
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

