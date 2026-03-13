{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}

module TypeClassesTree where

import CycleQ
import Prelude (Bool (..))

data Tree a = Node (Tree a) a (Tree a) | Leaf

id :: a -> a
id x = x

(.)    :: (b -> c) -> (a -> b) -> a -> c
(.) f g = \x -> f (g x)

fmap :: (a -> b) -> Tree a -> Tree b
fmap f (Node l x r) = Node (fmap f l) (f x) (fmap f r)
fmap f Leaf = Leaf

pure :: a -> Tree a
pure x = Node (pure x) x (pure x)
    
(<*>) :: Tree (a -> b) -> Tree a -> Tree b
Leaf <*> _ = Leaf
_ <*> Leaf = Leaf
Node l1 f1 r1 <*> Node l2 x2 r2 = Node (l1 <*> l2) (f1 x2) (r1 <*> r2)
  
-- Functor laws

{-# ANN fmapId defaultParams #-}
fmapId :: Tree a -> Equation
fmapId xs = fmap id xs === id xs

{-# ANN fmapComposition defaultParams #-}
fmapComposition :: (b -> c) -> (a -> b) -> Tree a -> Equation
fmapComposition f g xs = fmap (f . g) xs === (fmap f . fmap g) xs


($) :: (a -> b) -> a -> b
f $ x = f x

-- {-# ANN appIdentity defaultParams #-}
-- appIdentity :: Tree a -> Equation
-- appIdentity v = (pure id <*> v) === v

-- {-# ANN appComposition defaultParams #-}
-- appComposition :: Tree (a1 -> b) -> Tree (a2 -> a1) -> Tree a2 -> Equation
-- appComposition u v w = (pure (.) <*> u <*> v <*> w) === (u <*> (v <*> w))

-- {-# ANN appHomomorphism defaultParams #-}
-- appHomomorphism :: forall a b . (a -> b) -> a -> Equation
-- appHomomorphism f x = (pure f <*> (pure :: a -> Tree a) x) === pure (f x)

-- {-# ANN appInterchange defaultParams #-}
-- appInterchange :: Tree (a -> b) -> a -> Equation
-- appInterchange u y = (u <*> pure y) === (pure ($ y) <*> u)
