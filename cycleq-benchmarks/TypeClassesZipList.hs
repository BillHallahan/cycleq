{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}

module TypeClassesZipList where

import CycleQ
import Prelude (Bool (..))

data List a = a :> List a | Nil
infixl 4 :>

id :: a -> a
id x = x

(.)    :: (b -> c) -> (a -> b) -> a -> c
(.) f g = \x -> f (g x)

repeat :: a -> List a
{-# INLINE [0] repeat #-}
-- -- The pragma just gives the rules more chance to fire
repeat x = x :> repeat x

-- Applicative laws
pureList x    = (repeat x)

zipWith :: (a->b->c) -> List a->List b-> List c
zipWith _f Nil     _bs    = Nil
zipWith _f _as    Nil    = Nil
zipWith f  (a:>as) (b:>bs) = f a b :> zipWith f as bs

(<*>) :: List (a -> b) -> List a -> List b
fs <*> xs = zipWith id fs xs

($) :: (a -> b) -> a -> b
f $ x = f x

-- {-# ANN appIdentity defaultParams #-}
-- appIdentity :: List a -> Equation
-- appIdentity v = (pureList id <*> v) === v

-- {-# ANN appComposition defaultParams #-}
-- appComposition :: List (a1 -> b) -> List (a2 -> a1) -> List a2 -> Equation
-- appComposition u v w = (pureList (.) <*> u <*> v <*> w) === (u <*> (v <*> w))

-- {-# ANN appHomomorphism defaultParams #-}
-- appHomomorphism :: forall a b . (a -> b) -> a -> Equation
-- appHomomorphism f x = (pureList f <*> (pureList :: a -> List a) x) === pureList (f x)

-- {-# ANN appInterchange defaultParams #-}
-- appInterchange :: List (a -> b) -> a -> Equation
-- appInterchange u y = (u <*> pureList y) === (pureList ($ y) <*> u)