{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}

module TypeClassesTuple where

import CycleQ
import Prelude (Bool (..))

data Tuple a b = Tuple a b

data Nat
  = Z
  | S Nat

(+) :: Nat -> Nat -> Nat
Z + y = y
(S x) + y = S (x + y)

data List a = a :> List a | Nil
infixl 4 :>

(++) :: List a -> List a -> List a
(++) Nil     ys = ys
(++) (x :> xs) ys = x :> (xs ++ ys)

foldr :: (a -> b -> b) -> b -> List a -> b
foldr k z Nil     = z
foldr k z (y :> ys) = y `k` foldr k z ys


(<>) :: Tuple Nat Nat -> Tuple Nat Nat -> Tuple Nat Nat
Tuple x1 y1 <> Tuple x2 y2 = Tuple (x1 + x2) (y1 + y2)

mempty = Tuple Z Z

mconcat :: List (Tuple Nat Nat) -> Tuple Nat Nat
mconcat = foldr (<>) mempty

fmap f (Tuple x y) = Tuple x (f y)

id :: a -> a
id x = x

(.)    :: (b -> c) -> (a -> b) -> a -> c
(.) f g = \x -> f (g x)

-- Semigroup laws
{-# ANN semigroupAssociativity defaultParams #-}
semigroupAssociativity :: Tuple Nat Nat -> Tuple Nat Nat -> Tuple Nat Nat -> Equation
semigroupAssociativity x y z = x <> (y <> z) === (x <> y) <> z

{-# ANN monoidRightIdentity defaultParams #-}
monoidRightIdentity :: Tuple Nat Nat -> Equation
monoidRightIdentity x = x <> mempty === x

{-# ANN monoidLeftIdentity defaultParams #-}
monoidLeftIdentity :: Tuple Nat Nat -> Equation
monoidLeftIdentity x = mempty <> x === x 

{-# ANN monoidConcatenation defaultParams #-}
monoidConcatenation :: List (Tuple Nat Nat) -> Equation
monoidConcatenation xs = mconcat xs === foldr (<>) mempty xs

-- Functor laws

{-# ANN fmapId defaultParams #-}
fmapId :: Tuple Nat Nat -> Equation
fmapId xs = fmap id xs === id xs

{-# ANN fmapComposition defaultParams #-}
fmapComposition :: (b -> c) -> (a -> b) -> Tuple Nat a -> Equation
fmapComposition f g xs = fmap (f . g) xs === (fmap f . fmap g) xs

-- Applicative laws
pure x = Tuple Z x

($) :: (a -> b) -> a -> b
f $ x = f x

(<*>) :: Tuple Nat (a -> b) -> Tuple Nat a -> Tuple Nat b
Tuple x1 f <*> Tuple x2 y = Tuple (x1 + x2) (f y)

{-# ANN appIdentity defaultParams #-}
appIdentity :: Tuple Nat a -> Equation
appIdentity v = (pure id <*> v) === v

{-# ANN appComposition defaultParams #-}
appComposition :: Tuple Nat (a2 -> b) -> Tuple Nat (a1 -> a2) -> Tuple Nat a1 -> Equation
appComposition u v w = (pure (.) <*> u <*> v <*> w) === (u <*> (v <*> w))

{-# ANN appHomomorphism defaultParams #-}
appHomomorphism :: forall b . (Nat -> b) -> Nat -> Equation
appHomomorphism f x = (pure f <*> (pure :: Nat -> Tuple Nat Nat) x) === pure (f x)

{-# ANN appInterchange defaultParams #-}
appInterchange :: Tuple Nat (a -> b) -> a -> Equation
appInterchange u y = (u <*> pure y) === (pure ($ y) <*> u)

return :: a -> Tuple Nat a
return = pure

(>>=) :: Tuple Nat a -> (a -> Tuple Nat b) -> Tuple Nat b
Tuple u a >>= k = case k a of Tuple v b -> Tuple (u + v) b

{-# ANN monadLeftIdentity defaultParams #-}
monadLeftIdentity :: a -> (a -> Tuple Nat b) -> Equation
monadLeftIdentity a k = (return a >>= k) === k a

{-# ANN monadRightIdentity defaultParams #-}
monadRightIdentity :: Tuple Nat b -> Equation
monadRightIdentity m = (m >>= return) === m

{-# ANN monadAssociativity defaultParams #-}
monadAssociativity :: Tuple Nat a1 -> p -> (a1 -> Tuple Nat a2) -> (a2 -> Tuple Nat b) -> Equation
monadAssociativity m x k h = (m >>= (\x -> k x >>= h)) === ((m >>= k) >>= h)