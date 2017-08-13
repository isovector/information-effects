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
infix 6 +
infix 7 *

infix 6 .+
infix 7 .*
infix 1 >>

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

swapT :: a * b <=> b * a
swapT = Iso swap swap
  where
    swap (Pair a b) = (Pair b a)

swapP :: a + b <=> b + a
swapP = Iso swap swap
  where
    swap (InL a) = InR a
    swap (InR b) = InL b

assocP :: a + (b + c) <=> (a + b) + c
assocP = Iso assocl assocr
  where
    assocl (InL a)       = InL (InL a)
    assocl (InR (InL b)) = InL (InR b)
    assocl (InR (InR c)) = InR c

    assocr (InL (InL a)) = InL a
    assocr (InL (InR b)) = InR (InL b)
    assocr (InR c)       = InR (InR c)

assocT :: a * (b * c) <=> (a * b) * c
assocT = Iso assocl assocr
  where
    assocl (Pair a (Pair b c)) = (Pair (Pair a b) c)
    assocr (Pair (Pair a b) c) = (Pair a (Pair b c))

unite :: U * a <=> a
unite = Iso unite uniti
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

(.*) :: (a <=> b) -> (c <=> d) -> (a * c <=> b * d)
(.*) ab cd = Iso (\(Pair a c) -> (Pair (to ab a) (to cd c)))
                    (\(Pair b d) -> (Pair (from ab b) (from cd d)))

(.+) :: (a <=> b) -> (c <=> d) -> (a + c <=> b + d)
(.+) ab cd = Iso to' from'
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
not = swapP

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
  sym unite
  false .* id
  distrib
  unite .+ unite

zero :: U <=> Nat
zero = trace $ do
  swapP
  fold
  right

isZero :: Nat * Bool <=> Nat * Bool
isZero = do
  sym fold .* id
  distrib
  (id .* not) .+ id
  sym distrib
  fold .* id

move1 :: Nat * Nat <=> (Nat * Nat) + Nat
move1 = do
  sym fold .* id
  distrib
  unite .+ (id .* add1)
  swapP

copoint :: a + a <=> a * Bool
copoint = do
  sym unite .+ sym unite
  sym distrib
  swapT


debug :: Dbg.String -> (a <=> a)
debug msg = Iso (Dbg.trace msg)
                (Dbg.trace ("~" Dbg.++ msg))

main :: IO ()
main = putStrLn "hello"

-- main :: IO ()
-- main = putStrLn $ show $ to ((.*) (zero >> add1 >> add1) true >> isEven) (Pair U U)
--   where
--     bimap :: (a -> b) -> (c -> d) -> (a * c) -> (b * d)
--     bimap f g (Pair a c) = Pair (f a) (g c)


sw :: a * (b * c) <=> b * (a * c)
sw = do
  assocT
  swapT .* id
  sym assocT

iterNat :: (a <=> a) -> (Nat * a <=> Nat * a)
iterNat step = do
  sym unite
  trace $ do
    sym distrib
    (swapP >> fold) .* id
    sw
    (sym fold >> swapP) .* id
    distrib
    (id .* (id .* step) >> sw) .+ id
  unite

isEven :: Nat * Bool <=> Nat * Bool
isEven = iterNat not

