{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}

module TypeClassesMaybe where

import CycleQ
import Prelude (Bool (..))

data  Maybe a  =  Nothing | Just a

data List a = a :> List a | Nil
infixl 4 :>

(++) :: List a -> List a -> List a
(++) Nil     ys = ys
(++) (x :> xs) ys = x :> (xs ++ ys)

foldr :: (a -> b -> b) -> b -> List a -> b
foldr k z Nil     = z
foldr k z (y :> ys) = y `k` foldr k z ys

data A = A

A <|> A = A

(<>) :: Maybe A -> Maybe A -> Maybe A
Nothing <> b       = b
a       <> Nothing = a
Just a  <> Just b  = Just (a <|> b)

mempty = Nothing

mconcat :: List (Maybe A) -> Maybe A
mconcat = foldr (<>) mempty

fmap _ Nothing       = Nothing
fmap f (Just a)      = Just (f a)

id :: a -> a
id x = x

(.)    :: (b -> c) -> (a -> b) -> a -> c
(.) f g = \x -> f (g x)

-- Semigroup laws
{-# ANN semigroupAssociativity defaultParams #-}
semigroupAssociativity :: Maybe A -> Maybe A -> Maybe A -> Equation
semigroupAssociativity x y z = x <> (y <> z) === (x <> y) <> z

{-# ANN monoidRightIdentity defaultParams #-}
monoidRightIdentity :: Maybe A -> Equation
monoidRightIdentity x = x <> mempty === x

{-# ANN monoidLeftIdentity defaultParams #-}
monoidLeftIdentity :: Maybe A -> Equation
monoidLeftIdentity x = mempty <> x === x 

{-# ANN monoidConcatenation defaultParams #-}
monoidConcatenation :: List (Maybe A) -> Equation
monoidConcatenation xs = mconcat xs === foldr (<>) mempty xs

-- Functor laws

{-# ANN fmapId defaultParams #-}
fmapId :: Maybe a -> Equation
fmapId xs = fmap id xs === id xs

{-# ANN fmapComposition defaultParams #-}
fmapComposition :: (b -> c) -> (a -> b) -> Maybe a -> Equation
fmapComposition f g xs = fmap (f . g) xs === (fmap f . fmap g) xs


-- Applicative laws
pure = Just

($) :: (a -> b) -> a -> b
f $ x = f x

(<*>) :: Maybe (a -> b) -> Maybe a -> Maybe b
Just f  <*> m       = fmap f m
Nothing <*> _m      = Nothing

{-# ANN appIdentity defaultParams #-}
appIdentity :: Maybe a -> Equation
appIdentity v = (pure id <*> v) === v

{-# ANN appComposition defaultParams #-}
appComposition :: Maybe (a1 -> b) -> Maybe (a2 -> a1) -> Maybe a2 -> Equation
appComposition u v w = (pure (.) <*> u <*> v <*> w) === (u <*> (v <*> w))

{-# ANN appHomomorphism defaultParams #-}
appHomomorphism :: forall a b . (a -> b) -> a -> Equation
appHomomorphism f x = (pure f <*> (pure :: a -> Maybe a) x) === pure (f x)

{-# ANN appInterchange defaultParams #-}
appInterchange :: Maybe (a -> b) -> a -> Equation
appInterchange u y = (u <*> pure y) === (pure ($ y) <*> u)

return :: a -> Maybe a
return = pure

(>>=) :: Maybe a -> (a -> Maybe b) -> Maybe b
(Just x) >>= k      = k x
Nothing  >>= _      = Nothing

{-# ANN monadLeftIdentity defaultParams #-}
monadLeftIdentity :: a -> (a -> Maybe b) -> Equation
monadLeftIdentity a k = (return a >>= k) === k a

{-# ANN monadRightIdentity defaultParams #-}
monadRightIdentity :: Maybe b -> Equation
monadRightIdentity m = (m >>= return) === m

{-# ANN monadAssociativity defaultParams #-}
monadAssociativity :: Maybe a1 -> p -> (a1 -> Maybe a2) -> (a2 -> Maybe b) -> Equation
monadAssociativity m x k h = (m >>= (\x -> k x >>= h)) === ((m >>= k) >>= h)