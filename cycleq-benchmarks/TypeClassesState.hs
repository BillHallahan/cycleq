{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}

module TypeClassesState where

import CycleQ
import Prelude (Bool (..))

data Identity a = Identity { runIdentity :: a }

data StateT s m a = StateT { runStateT :: s -> m (a,s) }

type State s = StateT s Identity

-- | Unwrap a state monad computation as a function.
-- (The inverse of 'state'.)
runState :: State s a   -- ^state-passing computation to execute
         -> s           -- ^initial state
         -> (a, s)      -- ^return value and final state
runState m = runIdentity . runStateT m

fmapIdentity :: (a -> b) -> Identity a -> Identity b
fmapIdentity f (Identity x) = Identity (f x) 

fmap :: (a -> b) -> State s a -> State s b
fmap f m = StateT $ \ s ->
    fmapIdentity (\ ~(a, s') -> (f a, s')) $ runStateT m s

id :: a -> a
id x = x

(.)    :: (b -> c) -> (a -> b) -> a -> c
(.) f g = \x -> f (g x)

($) :: (a -> b) -> a -> b
f $ x = f x

{-
(++) :: List a -> List a -> List a
(++) Nil     ys = ys
(++) (x :> xs) ys = x :> (xs ++ ys)

(a :| as) <> ~(b :| bs) = a :| (as ++ (b :> bs))

mapList :: (a -> b) -> List a -> List b
mapList _ Nil     = Nil
mapList f (x:>xs) = f x :> mapList f xs

-- Semigroup laws
{-# ANN semigroupAssociativity defaultParams #-}
semigroupAssociativity :: NonEmpty a -> NonEmpty a -> NonEmpty a -> Equation
semigroupAssociativity x y z = x <> (y <> z) === (x <> y) <> z
-}

-- Functor laws

{-# ANN fmapId defaultParams #-}
fmapId :: s -> State s a -> Equation
fmapId s xs = runState (fmap id xs) s === runState (id xs) s

{-# ANN fmapComposition defaultParams #-}
fmapComposition :: s -> (b -> c) -> (a -> b) -> State s a -> Equation
fmapComposition s f g xs = runState (fmap (f . g) xs) s === runState ((fmap f . fmap g) xs) s

-- Applicative laws
pure a = StateT $ \ s -> identReturn (a, s)

identReturn = Identity

identMonad :: Identity a -> (a -> Identity b) -> Identity b
m `identMonad` k  = k (runIdentity m)

-- Test:
-- runIdentity $ runStateT ((pure (\x -> x + 1)) <*> pure (9 :: Int) :: StateT Int Identity Int) 4
-- (10,4)
(<*>) :: (StateT s'54 Identity (a'770 -> b'284)) -> (StateT s'54 Identity a'770) -> (StateT s'54 Identity b'284)
eta <*> eta1 = case eta of
      StateT mf -> case eta1 of
            StateT mx -> (\ds'13 -> StateT ds'13) $ (\s1 -> identMonad (mf s1) (\ds'12 -> identMonad (mx (case ds'12 of
                  (f'118, s') -> s')) (\ds1'9 -> identReturn ((,) (case ds'12 of
                  (f'118, s') -> f'118 (case ds1'9 of
                        (x'14, s'') -> x'14)) (case ds1'9 of
                  (x'13, s'') -> s'')))))

{-# ANN appIdentity defaultParams #-}
appIdentity :: s -> State s a -> Equation
appIdentity s v = runState (pure id <*> v) s === runState v s

{-# ANN appComposition defaultParams #-}
appComposition :: s -> State s (a1 -> b) -> State s (a2 -> a1) -> State s a2 -> Equation
appComposition s u v w = runState (pure (.) <*> u <*> v <*> w) s === runState (u <*> (v <*> w)) s

{-# ANN appHomomorphism defaultParams #-}
appHomomorphism :: forall s a b . s -> (a -> b) -> a -> Equation
appHomomorphism s f x = runState (pure f <*> (pure :: a -> State s a) x) s === runState (pure (f x)) s

{-# ANN appInterchange defaultParams #-}
appInterchange :: s -> State s (a -> b) -> a -> Equation
appInterchange s u y = runState (u <*> pure y) s === runState (pure ($ y) <*> u) s

(>>=) :: (StateT s'55 Identity a'830) -> (a'830 -> (StateT s'55 Identity b'318)) -> (StateT s'55 Identity b'318)
eta >>= eta1 = ($) (\ds'9 -> StateT ds'9) (\s1 -> identMonad (case eta of
      StateT ds'8 -> ds'8 s1) (\ds'7 -> case eta1 (case ds'7 of
      (a1, s') -> a1) of
      StateT ds1'6 -> ds1'6 (case ds'7 of
            (a1'6, s') -> s')))

return = pure

{-# ANN monadLeftIdentity defaultParams #-}
monadLeftIdentity :: s -> a -> (a -> State s b) -> Equation
monadLeftIdentity s a k = runState (return a >>= k) s === runState (k a) s

{-# ANN monadRightIdentity defaultParams #-}
monadRightIdentity :: s -> State s b -> Equation
monadRightIdentity s m = runState (m >>= return) s === runState m s

{-# ANN monadAssociativity defaultParams #-}
monadAssociativity :: s -> State s a1 -> p -> (a1 -> State s a2) -> (a2 -> State s b) -> Equation
monadAssociativity s m x k h = runState (m >>= (\x -> k x >>= h)) s === runState ((m >>= k) >>= h) s
