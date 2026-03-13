{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}

module TypeClassesList where

import CycleQ
import Prelude (Bool (..))

data List a = a :> List a | Nil
infixl 4 :>

(++) :: List a -> List a -> List a
(++) Nil     ys = ys
(++) (x :> xs) ys = x :> (xs ++ ys)

memptyList :: List a
memptyList = Nil

mconcatList :: List (List a) -> List a
mconcatList Nil = Nil
mconcatList (xs :> xss) = xs ++ mconcatList xss

foldr :: (a -> b -> b) -> b -> List a -> b
foldr k z Nil     = z
foldr k z (y :> ys) = y `k` foldr k z ys

map :: (a -> b) -> List a -> List b
map _ Nil     = Nil
map f (x:>xs) = f x :> map f xs

fmap = map

id :: a -> a
id x = x

(.)    :: (b -> c) -> (a -> b) -> a -> c
(.) f g = \x -> f (g x)

-- Semigroup laws
{-# ANN semigroupAssociativity defaultParams #-}
semigroupAssociativity :: List a -> List a -> List a -> Equation
semigroupAssociativity x y z = x ++ (y ++ z) === (x ++ y) ++ z

{-# ANN monoidRightIdentity defaultParams #-}
monoidRightIdentity :: List a -> Equation
monoidRightIdentity x = x ++ memptyList === x

{-# ANN monoidLeftIdentity defaultParams #-}
monoidLeftIdentity :: List a -> Equation
monoidLeftIdentity x = memptyList ++ x === x 

{-# ANN monoidConcatenation defaultParams #-}
monoidConcatenation :: List (List a) -> Equation
monoidConcatenation xs = mconcatList xs === foldr (++) memptyList xs

-- Functor laws

{-# ANN fmapId defaultParams #-}
fmapId :: List a -> Equation
fmapId xs = fmap id xs === id xs

{-# ANN fmapComposition defaultParams #-}
fmapComposition :: (b -> c) -> (a -> b) -> List a -> Equation
fmapComposition f g xs = fmap (f . g) xs === (fmap f . fmap g) xs

-- Applicative laws
pureList x    = x :> Nil

-- GHC's base defines (<*>) on lists as:
-- @ fs <*> xs = [f x | f <- fs, x <- xs] @
-- which does not work with the custom list type we need for CycleQ.
-- The below is the result of compiling this to G2's intermediate representation,
-- lambda lifting let-bound functions, and then adapting to work with List.
--
-- With build in list type:
-- @
-- (<**>) :: forall a . forall b . [a -> b] -> [a] -> [b]
-- f <**> xs = ds'2 f xs

-- ds'2 ds1'2 xs = case ds1'2 of
--             []  -> []
--             ds3 : ds4 -> ds5 xs ds3 ds4 xs

-- ds5 ds6 ds3 ds4 xs = case ds6 of
--             []  -> ds'2 ds4 xs
--             ds8 : ds9 -> (ds3 ds8):(ds5 ds9 ds3 ds4 xs)
-- @
-- 
-- Testing with built in list type:
--      ghci> ([\x -> x + 1, \y -> y * 2, \z -> z + 7] <*> [1..10]) == ([\x -> x + 1, \y -> y * 2, \z -> z + 7] <**> [1..10])
--      True
(<*>) :: List (a -> b) -> List a -> List b
f <*> xs = ds'2 f xs

ds'2 :: List (t -> a) -> List t -> List a
ds'2 ds1'2 xs = case ds1'2 of
            Nil  -> Nil
            ds3 :> ds4 -> ds5 xs ds3 ds4 xs

ds5 :: List t -> (t -> a) -> List (t -> a) -> List t -> List a
ds5 ds6 ds3 ds4 xs = case ds6 of
            Nil  -> ds'2 ds4 xs
            ds8 :> ds9 -> (ds3 ds8):>(ds5 ds9 ds3 ds4 xs)

($) :: (a -> b) -> a -> b
f $ x = f x

{-# ANN appIdentity defaultParams #-}
appIdentity :: List a -> Equation
appIdentity v = (pureList id <*> v) === v

{-# ANN appComposition defaultParams #-}
appComposition :: List (a1 -> b) -> List (a2 -> a1) -> List a2 -> Equation
appComposition u v w = (pureList (.) <*> u <*> v <*> w) === (u <*> (v <*> w))

{-# ANN appHomomorphism defaultParams #-}
appHomomorphism :: forall a b . (a -> b) -> a -> Equation
appHomomorphism f x = (pureList f <*> (pureList :: a -> List a) x) === pureList (f x)

{-# ANN appInterchange defaultParams #-}
appInterchange :: List (a -> b) -> a -> Equation
appInterchange u y = (u <*> pureList y) === (pureList ($ y) <*> u)

-- Definition found following the same method as (<*>)
-- ghci> ([1..10] >>= (\y -> [y + 1, y * 2, y + 18])) == ([1..10] >>== (\y -> [y + 1, y * 2, y + 18]))
-- True
(>>=) :: List a -> (a -> List b) -> List b
(>>=) xs'7 f'118 = ds'37 xs'7 f'118

ds'37 :: List t -> (t -> List a) -> List a
ds'37 ds1'28 f'118 = case ds1'28 of
            Nil  -> Nil
            ds3'5 :> ds4'4 -> ds5'4 (f'118 ds3'5) f'118 ds4'4

ds5'4 :: List a -> (t -> List a) -> List t -> List a
ds5'4 ds6'4 f'118 ds4'4 = case ds6'4 of
                        Nil  -> ds'37 ds4'4 f'118
                        ds8'3 :> ds9'3 -> ds8'3:>(ds5'4 ds9'3 f'118 ds4'4)

return :: a -> List a
return x = x :> Nil

{-# ANN monadLeftIdentity defaultParams #-}
monadLeftIdentity :: a -> (a -> List b) -> Equation
monadLeftIdentity a k = (return a >>= k) === k a

{-# ANN monadRightIdentity defaultParams #-}
monadRightIdentity :: List b -> Equation
monadRightIdentity m = (m >>= return) === m

{-# ANN monadAssociativity defaultParams #-}
monadAssociativity :: List a1 -> p -> (a1 -> List a2) -> (a2 -> List b) -> Equation
monadAssociativity m x k h = (m >>= (\x -> k x >>= h)) === ((m >>= k) >>= h)
