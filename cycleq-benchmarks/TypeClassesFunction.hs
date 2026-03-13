{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}

module TypeClassesFunction where

import CycleQ
import Prelude (Bool (..))

data List a = a :> List a | Nil
infixl 4 :>

fmap = (.)

(.)    :: (b -> c) -> (a -> b) -> a -> c
(.) f g = \x -> f (g x)

id :: a -> a
id x = x

const                   :: a -> b -> a
const x _               =  x

($) :: (a -> b) -> a -> b
f $ x = f x

mempty = id

foldr :: (a -> b -> b) -> b -> List a -> b
foldr k z Nil     = z
foldr k z (y :> ys) = y `k` foldr k z ys

mconcat = foldr (.) mempty

pure = const
(<*>) f g x = f x (g x)

return = pure
f >>= k = \ r -> k (f r) r

{-# ANN semigroupAssociativity defaultParams #-}
semigroupAssociativity :: a -> (a -> a) -> (a -> a) -> (a -> a) -> Equation
semigroupAssociativity e f g h = (f . (g . h)) e === ((f . g) . h) e

-- Function Functor
{-# ANN fmapId defaultParams #-}
fmapId :: e -> (e -> a) -> Equation
fmapId e f = (fmap id f) e === (id f) e

{-# ANN fmapComposition defaultParams #-}
fmapComposition :: e -> (b -> c) -> (a -> b) -> (e -> a) -> Equation
fmapComposition e f g xs = (fmap (f . g) xs) e === ((fmap f . fmap g) xs) e

--  Applicative
{-# ANN appIdentity defaultParams #-}
appIdentity :: e -> (e -> a) -> Equation
appIdentity e v = (pure id <*> v) e === v e

{-# ANN appComposition defaultParams #-}
appComposition :: e -> (e -> (a1 -> b)) -> (e -> (a2 -> a1)) -> (e -> a2) -> Equation
appComposition e u v w = (pure (.) <*> u <*> v <*> w) e === (u <*> (v <*> w)) e

{-# ANN appHomomorphism defaultParams #-}
appHomomorphism :: forall e f a b . e -> (a -> b) -> a -> Equation
appHomomorphism e f x = (pure f <*> (pure :: a -> (e -> a)) x) e === (pure (f x)) e

{-# ANN appInterchange defaultParams #-}
appInterchange :: e -> (e -> (a -> b)) -> a -> Equation
appInterchange e u y = (u <*> pure y) e === (pure ($ y) <*> u) e

--  Monad
{-# ANN monadLeftIdentity defaultParams #-}
monadLeftIdentity :: e -> a -> (a -> (e -> b)) -> Equation
monadLeftIdentity e a k = (return a >>= k) e === (k a) e

{-# ANN monadRightIdentity defaultParams #-}
monadRightIdentity :: e -> (e -> b) -> Equation
monadRightIdentity e m = ((m >>= return) e) === m e

{-# ANN monadAssociativity defaultParams #-}
monadAssociativity :: e -> (e -> a1) -> p -> (a1 -> (e -> a2)) -> (a2 -> (e -> b)) -> Equation
monadAssociativity e m x k h = (m >>= (\x -> k x >>= h)) e === ((m >>= k) >>= h) e
