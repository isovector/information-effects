{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE NoImplicitPrelude    #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Main where

import Prelude (IO, putStrLn, Either (..), (.), Num (..), ($), error)

type Bool = Either () ()

pattern True :: Bool
pattern True = Left ()

pattern False :: Bool
pattern False = Right ()

data Iso a b = Iso
  { to   :: a -> b
  , from :: b -> a
  }

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

id :: a -> a
id a = a

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

type Nat = Fix (Either ())

pattern Zero :: Nat
pattern Zero = Fix (Left ())

pattern Succ :: Nat -> Nat
pattern Succ n = Fix (Right n)

instance Num Nat where
  fromInteger 0 = Zero
  fromInteger n = Succ . fromInteger $ n - 1

  Zero + n = n
  Succ a + b = a + Succ b

  Zero * n   = Zero
  Succ a * b = b + (a * b)

  abs n = n

  signum _ = Succ Zero
  negate = error "bad"




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

main :: IO ()
main = putStrLn "hello"


