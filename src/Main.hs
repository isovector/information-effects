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
infixl 1 >>

data a <=> b
  = Iso
  { to   :: a -> b
  , from :: b -> a
  }

data a * b = Pair a b
data a + b
  = InL a
  | InR b

instance {-# OVERLAPPING #-} P.Show Bool where
  show (InL U) = "true"
  show (InR U) = "false"

instance (P.Show a, P.Show b) => P.Show (a * b) where
  show (Pair a b) = "(" P.++ show a P.++ " * " P.++ show b P.++ ")"

instance (P.Show a, P.Show b) => P.Show (a + b) where
  show (InL a) = "(inl " P.++ show a P.++ ")"
  show (InR a) = "(inr " P.++ show a P.++ ")"

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

injectR :: a <=> a + a
injectR = do
  sym unite
  false .* id
  distrib
  unite .+ unite

zero :: U <=> Nat
zero = trace $ do
  swapP
  fold
  injectR

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

myList :: U <=> List Bool
myList = do
  nil
  sym unite
  true .* id
  cons
  sym unite
  true .* id
  cons
  sym unite
  false .* id
  cons
  map not

main :: IO ()
main = putStrLn $ show $ to myList U


sw :: a * (b * c) <=> b * (a * c)
sw = do
  assocT
  swapT .* id
  sym assocT


sw2 :: (a * b) * (c * d) <=> (a * c) * (b * d)
sw2 = do
  sym assocT
  id .* sw
  assocT

iterNat :: (a <=> a) -> (Nat * a <=> Nat * a)
iterNat step = do
  sym unite
  trace $ do
    id                                -- (Nat * (Nat * a)) + (U * (Nat * a))
    sym distrib                       -- (Nat + U) * (Nat * a)
    (swapP >> fold) .* id             -- Nat * (Nat * a)
    sw                                -- Nat * (Nat * a)
    (sym fold >> swapP) .* id         -- (Nat + U) * (Nat * a)
    distrib                           -- (Nat * (Nat * a)) + (U * (Nat * a))
    (id .* (id .* step) >> sw) .+ id  -- (Nat * (Nat * a)) + (U * (Nat * a))
  unite

isEven :: Nat * Bool <=> Nat * Bool
isEven = iterNat not


data ListF a b
  = Nil
  | Cons a b

type List a = Fix (ListF a)

instance P.Show a => P.Show (List a) where
  show (Fix Nil) = "[]"
  show (Fix (Cons a b)) = show a P.++ ":" P.++ show b


liste :: List a <=> U + (a * List a)
liste = Iso to from
  where
    to (Fix Nil)          = InL U
    to (Fix (Cons a b))   = InR (Pair a b)
    from (InL U)          = Fix Nil
    from (InR (Pair a b)) = Fix (Cons a b)

cons :: a * List a <=> List a
cons = do
  just       -- U + (a * List a)
  sym liste  -- List

swapCbaP :: (a + b) + c <=> (c + b) + a
swapCbaP = do
  sym assocP   -- a + (b + c)
  swapP        -- (b + c) + a
  swapP .+ id  -- (c + b) + a

diverge :: a <=> b
diverge = trace $ do
                     -- (a + b) + a
  swapP .+ id        -- (b + a) + a
  swapCbaP           -- (a + a) + b
  sym injectR .+ id  -- a + b
  swapP              -- b + a
  injectR .+ id      -- (b + b) + a
  swapCbaP           -- (a + b) + b

nil :: U <=> List a
nil = trace $ do
                            -- (a * List a) + U
  swapP                     -- U + (a * List a)
  sym liste                 -- List a
  sym unite                 -- U * List a
  just .* id                -- (U + U) * List a
  distrib                   -- (U * List a) + (U * List a)
  (diverge .* id) .+ unite  -- (a * List a) + List a

reverse :: List a <=> List a
reverse = withUnit $ iterList id

iterList :: (a * z <=> b * z) -> (List a * z <=> List b * z)
iterList f = do
  sym unite
  trace $ do
                                -- ((b * List b) * (List a * z)) + (U * (List a * z))
    sym distrib                 -- ((b * List b) + U) * (List a * z)
    (swapP >> sym liste) .* id  -- List b * (List a * z)
    sw                          -- List a * (List b * z)
    liste .* id                 -- (U + (a * List a)) * (List b * z)
    distrib                     -- (U * (List b * z)) + ((a * List a) * (List b * z))
    (.+) id $                   -- (U * (List b * z)) +
      do
        swapT .* id             --    ((List a * a) * (List b * z))
        sw2                     --    ((List a * List b) * (a * z))
        id .* f                 --    ((List a * List b) * (b * z))
        sw2                     --    ((List a * b) * (List b * z))

    swapP                       -- ((List a * b) * (List b * z)) + (U * (List b * z))
    (swapT .* id >> sw2) .+ id  -- ((b * List b) * (List a * z)) + (U * (List b * z))
  unite

withUnit :: (a * U <=> b * U) -> (a <=> b)
withUnit f = do
  sym unite  -- U * a
  swapT      -- a * U
  f          -- b * U
  sym swapT  -- U * b
  unite      -- b

map :: (a <=> b) -> (List a <=> List b)
map f = do
  withUnit . iterList $ f .* id
  reverse

