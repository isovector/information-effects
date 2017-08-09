{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE NoImplicitPrelude    #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE RebindableSyntax     #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Main where

import Prelude (IO, putStrLn, Either (..), (.), Num (..), ($), error, show, Int, fst, snd)

type Bool = Either () ()

pattern True :: Bool
pattern True = Left ()

pattern False :: Bool
pattern False = Right ()

data Iso a b = Iso
  { to   :: a -> b
  , from :: b -> a
  }

type Iso' a = Iso a a

(>>) :: Iso a b -> Iso b c -> Iso a c
(>>) = trans

return = error "not applicable here, sucka"

(|>) :: Iso a b -> Iso b c -> Iso a c
(|>) = trans

swapProd :: Iso (a, b) (b, a)
swapProd = Iso swap' swap'
  where
    swap' (a, b) = (b, a)

swapCoprod :: Iso (Either a b) (Either b a)
swapCoprod = Iso swap' swap'
  where
    swap' (Left a)  = Right a
    swap' (Right b) = Left b

assocCoprod :: Iso (Either a (Either b c)) (Either (Either a b) c)
assocCoprod = Iso assocl assocr
  where
    assocl (Left a)          = Left (Left a)
    assocl (Right (Left b))  = Left (Right b)
    assocl (Right (Right c)) = (Right c)

    assocr (Left (Left a))  = (Left a)
    assocr (Left (Right b)) = (Right (Left b))
    assocr (Right c)        = (Right (Right c))

assocProd :: Iso (a, (b, c)) ((a, b), c)
assocProd = Iso assocl assocr
  where
    assocl (a, (b, c)) = ((a, b), c)
    assocr ((a, b), c) = (a, (b, c))

unit :: Iso ((), a) a
unit = Iso unite uniti
  where
    unite ((), a) = a
    uniti a = ((), a)

distribFactor :: Iso (Either a b, c) (Either (a, c) (b, c))
distribFactor = Iso distrib factor
  where
    distrib (Left a, c) = Left (a, c)
    distrib (Right b, c) = Right (b, c)

    factor (Left (a, c))  = (Left a, c)
    factor (Right (b, c)) = (Right b, c)

sym :: Iso a b -> Iso b a
sym iso = Iso (from iso) (to iso)

trans :: Iso a b -> Iso b c -> Iso a c
trans ab bc = Iso (to bc . to ab) (from ab . from bc)

id :: Iso' a
id = Iso (\a -> a) (\a -> a)

parProd :: Iso a b -> Iso c d -> Iso (a, c) (b, d)
parProd ab cd = Iso (\(a, c) -> (to ab a, to cd c))
                    (\(b, d) -> (from ab b, from cd d))

parCoprod :: Iso a b -> Iso c d -> Iso (Either a c) (Either b d)
parCoprod ab cd = Iso to' from'
  where
    to' (Left a)    = Left (to ab a)
    to' (Right c)   = Right (to cd c)
    from' (Left b)  = Left (from ab b)
    from' (Right d) = Right (from cd d)

newtype Fix f = Fix { unfold :: f (Fix f) }

fold :: f (Fix f) -> Fix f
fold = Fix

foldUnfold :: Iso (f (Fix f)) (Fix f)
foldUnfold = Iso fold unfold

type Nat = Fix (Either ())


trace :: forall a b c. Iso (Either a b) (Either a c) -> Iso b c
trace comb = Iso (\b -> loopfwd (to comb (Right b)))
                 (\c -> loopbwd (from comb (Right c)))
  where
    loopfwd :: Either a c -> c
    loopfwd (Left a) = loopfwd (to comb (Left a))
    loopfwd (Right c) = c

    loopbwd :: Either a b -> b
    loopbwd (Left a) = loopbwd (from comb (Left a))
    loopbwd (Right c) = c


not :: Iso' Bool
not = swapCoprod

just :: Iso b (Either () b)
just = Iso Right (\(Right b) -> b)  -- intentionally partial

add1 :: Iso' Nat
add1 = trans just foldUnfold

sub1 :: Iso' Nat
sub1 = sym add1

false :: Iso () Bool
false = just

true :: Iso () Bool
true = trans just not

right :: Iso a (Either a a)
right = do
  sym unit
  parProd false id
  distribFactor
  parCoprod unit unit

zero :: Iso () Nat
zero = trace $ do
  swapCoprod
  foldUnfold
  right

isEven :: Iso' (Nat, Bool)
isEven = trace $ do
  parCoprod id (parProd (sym foldUnfold) id)
  sym distribFactor
  parProd swapCoprod id
  distribFactor
  parCoprod (parProd id not) (parProd foldUnfold id)

isZero :: Iso' (Nat, Bool)
isZero = do
  parProd (sym foldUnfold) id
  distribFactor
  parCoprod(parProd id not) id
  sym distribFactor
  parProd foldUnfold id


main :: IO ()
main = putStrLn $ show $ bimap nat2Int (\x -> x) $ to (parProd (zero) false >> isZero) ((), ())
  where
    bimap :: (a -> b) -> (c -> d) -> (a, c) -> (b, d)
    bimap f g (a, c) = (f a ,g c)

    nat2Int :: Nat -> Int
    nat2Int (Fix (Left ())) = 0
    nat2Int (Fix (Right n)) = 1 + nat2Int n

