{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE NoImplicitPrelude    #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE RebindableSyntax     #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Main where

import qualified Debug.Trace as Dbg
import           Prelude (IO, putStrLn, (.), Num (..), ($), error, show, Int, fst, snd)
import qualified Prelude as Dbg (String, (++))
import qualified Prelude as P

data U = U

type Bool = U + U

infix 3 <=>

data a <=> b
  = Iso
  { to   :: a -> b
  , from :: b -> a
  }

data a * b = Pair a b
data a + b
  = InL a
  | InR b

return :: a <=> a
return = id

swapProd :: a * b <=> b * a
swapProd = Iso swap swap
  where
    swap (Pair a b) = (Pair b a)

swapCoprod :: a + b <=> b + a
swapCoprod = Iso swap swap
  where
    swap (InL a) = InR a
    swap (InR b) = InL b

assocCoprod :: a + (b + c) <=> (a + b) + c
assocCoprod = Iso assocl assocr
  where
    assocl (InL a)       = InL (InL a)
    assocl (InR (InL b)) = InL (InR b)
    assocl (InR (InR c)) = InR c

    assocr (InL (InL a)) = InL a
    assocr (InL (InR b)) = InR (InL b)
    assocr (InR c)       = InR (InR c)

assocProd :: a * (b * c) <=> (a * b) * c
assocProd = Iso assocl assocr
  where
    assocl (Pair a (Pair b c)) = (Pair (Pair a b) c)
    assocr (Pair (Pair a b) c) = (Pair a (Pair b c))

unit :: U * a <=> a
unit = Iso unite uniti
  where
    unite (Pair U a) = a
    uniti a = (Pair U a)

distrib :: (a + b) * c <=> (a * c) + (b * c)
distrib = Iso distrib factor
  where
    distrib (Pair (InL a) c) = InL (Pair a c)
    distrib (Pair (InR b) c) = InR (Pair b c)

    factor (InL (Pair a c)) = (Pair (InL a) c)
    factor (InR (Pair b c)) = (Pair (InR b) c)

sym :: (a <=> b) -> (b <=> a)
sym iso = Iso (from iso) (to iso)

(>>) :: (a <=> b) -> (b <=> c) -> (a <=> c)
(>>) ab bc = Iso (to bc . to ab) (from ab . from bc)

id :: a <=> a
id = Iso (\a -> a) (\a -> a)

parProd :: (a <=> b) -> (c <=> d) -> (a * c <=> b * d)
parProd ab cd = Iso (\(Pair a c) -> (Pair (to ab a) (to cd c)))
                    (\(Pair b d) -> (Pair (from ab b) (from cd d)))

parCoprod :: (a <=> b) -> (c <=> d) -> (a + c <=> b + d)
parCoprod ab cd = Iso to' from'
  where
    to' (InL a)   = InL (to ab a)
    to' (InR c)   = InR (to cd c)
    from' (InL b) = InL (from ab b)
    from' (InR d) = InR (from cd d)

newtype Fix f = Fix { unFix :: f (Fix f) }

fold :: (f (Fix f)) <=> (Fix f)
fold = Iso Fix unFix

type Nat = Fix ((+) U)

instance P.Show Nat where
  show f = show $ nat2Int f
    where
      nat2Int (Fix (InL U)) = 0
      nat2Int (Fix (InR n)) = 1 + nat2Int n


trace :: forall a b c. (a + b <=> a + c) -> (b <=> c)
trace comb = Iso (\b -> loopfwd (to comb (InR b)))
                 (\c -> loopbwd (from comb (InR c)))
  where
    loopfwd :: a + c -> c
    loopfwd (InL a) = loopfwd (to comb (InL a))
    loopfwd (InR c) = c

    loopbwd :: a + b -> b
    loopbwd (InL a) = loopbwd (from comb (InL a))
    loopbwd (InR c) = c


not :: Bool <=> Bool
not = swapCoprod

just :: b <=> U + b
just = Iso InR (\(InR b) -> b)  -- intentionally partial

add1 :: Nat <=> Nat
add1 = just >> fold

sub1 :: Nat <=> Nat
sub1 = sym add1

false :: U <=> Bool
false = just

true :: U <=> Bool
true = just >> not

right :: a <=> a + a
right = do
  sym unit
  parProd false id
  distrib
  parCoprod unit unit

zero :: U <=> Nat
zero = trace $ do
  swapCoprod
  fold
  right

isZero :: Nat * Bool <=> Nat * Bool
isZero = do
  parProd (sym fold) id
  distrib
  parCoprod(parProd id not) id
  sym distrib
  parProd fold id

move1 :: Nat * Nat <=> (Nat * Nat) + Nat
move1 = do
  parProd (sym fold) id
  distrib
  parCoprod unit (parProd id add1)
  swapCoprod

copoint :: a + a <=> a * Bool
copoint = do
  parCoprod (sym unit) (sym unit)
  sym distrib
  swapProd


debug :: Dbg.String -> (a <=> a)
debug msg = Iso (Dbg.trace msg)
                (Dbg.trace ("~" Dbg.++ msg))

main :: IO ()
main = putStrLn "hello"

-- main :: IO ()
-- main = putStrLn $ show $ to (parProd (zero >> add1 >> add1) true >> isEven) (Pair U U)
--   where
--     bimap :: (a -> b) -> (c -> d) -> (a * c) -> (b * d)
--     bimap f g (Pair a c) = Pair (f a) (g c)


sw :: a * (b * c) <=> b * (a * c)
sw = do
  assocProd
  parProd swapProd id
  sym assocProd

iterNat :: (a <=> a) -> (Nat * a <=> Nat * a)
iterNat step = do
  sym unit
  trace $ do
    sym distrib
    parProd (swapCoprod >> fold) id
    sw
    parProd (sym fold >> swapCoprod) id
    distrib
    parCoprod (parProd id (parProd id step) >> sw) id
  unit

isEven :: Nat * Bool <=> Nat * Bool
isEven = iterNat not

