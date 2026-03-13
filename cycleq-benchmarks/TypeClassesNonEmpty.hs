{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}

module TypeClassesNonEmpty where

import CycleQ
import Prelude (Bool (..))

data List a = a :> List a | Nil
infixl 4 :>

data NonEmpty a = a :| List a

infixr 5 :|

(++) :: List a -> List a -> List a
(++) Nil     ys = ys
(++) (x :> xs) ys = x :> (xs ++ ys)

(a :| as) <> ~(b :| bs) = a :| (as ++ (b :> bs))

mapList :: (a -> b) -> List a -> List b
mapList _ Nil     = Nil
mapList f (x:>xs) = f x :> mapList f xs

fmap :: (a -> b) -> NonEmpty a -> NonEmpty b
fmap f (a :| as) = f a :| mapList f as

id :: a -> a
id x = x

(.)    :: (b -> c) -> (a -> b) -> a -> c
(.) f g = \x -> f (g x)

-- Semigroup laws
{-# ANN semigroupAssociativity defaultParams #-}
semigroupAssociativity :: NonEmpty a -> NonEmpty a -> NonEmpty a -> Equation
semigroupAssociativity x y z = x <> (y <> z) === (x <> y) <> z


-- Functor laws

{-# ANN fmapId defaultParams #-}
fmapId :: NonEmpty a -> Equation
fmapId xs = fmap id xs === id xs

{-# ANN fmapComposition defaultParams #-}
fmapComposition :: (b -> c) -> (a -> b) -> NonEmpty a -> Equation
fmapComposition f g xs = fmap (f . g) xs === (fmap f . fmap g) xs


-- Applicative laws
pureNonEmpty x    = x :| Nil

($) :: (a -> b) -> a -> b
f $ x = f x

(<*>) :: NonEmpty (a -> b) -> NonEmpty a -> NonEmpty b
m1 <*> m2 = (>>==) m1 (\x1 -> (>>==) m2 (\x2 -> (x1 x2) :| Nil))

{-# ANN appIdentity defaultParams #-}
appIdentity :: NonEmpty a -> Equation
appIdentity v = (pureNonEmpty id <*> v) === v

{-# ANN appComposition defaultParams #-}
appComposition :: NonEmpty (a1 -> b) -> NonEmpty (a2 -> a1) -> NonEmpty a2 -> Equation
appComposition u v w = (pureNonEmpty (.) <*> u <*> v <*> w) === (u <*> (v <*> w))

{-# ANN appHomomorphism defaultParams #-}
appHomomorphism :: forall a b . (a -> b) -> a -> Equation
appHomomorphism f x = (pureNonEmpty f <*> (pureNonEmpty :: a -> NonEmpty a) x) === pureNonEmpty (f x)

{-# ANN appInterchange defaultParams #-}
appInterchange :: NonEmpty (a -> b) -> a -> Equation
appInterchange u y = (u <*> pureNonEmpty y) === (pureNonEmpty ($ y) <*> u)

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

return :: a -> NonEmpty a
return x = x :| Nil

(>>==) :: NonEmpty a -> (a -> NonEmpty b) -> NonEmpty b
(a :| as) >>== f = case f a of
                        b :| bs -> b :| (bs ++ (as >>= ((\(c :| cs) -> c :> cs) . f)))


{-# ANN monadLeftIdentity defaultParams #-}
monadLeftIdentity :: a -> (a -> NonEmpty b) -> Equation
monadLeftIdentity a k = (return a >>== k) === k a

{-# ANN monadRightIdentity defaultParams #-}
monadRightIdentity :: NonEmpty b -> Equation
monadRightIdentity m = (m >>== return) === m

{-# ANN monadAssociativity defaultParams #-}
monadAssociativity :: NonEmpty a1 -> p -> (a1 -> NonEmpty a2) -> (a2 -> NonEmpty b) -> Equation
monadAssociativity m x k h = (m >>== (\x -> k x >>== h)) === ((m >>== k) >>== h)