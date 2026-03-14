{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}

module TypeClassesReader where

import CycleQ
import Prelude (Bool (..))

id :: a -> a
id x = x

(.)    :: (b -> c) -> (a -> b) -> a -> c
(.) f g = \x -> f (g x)

($) :: (a -> b) -> a -> b
f $ x = f x

const x _ = x

data Identity a = Identity { runIdentity :: a }

fmapIdentity :: (a -> b) -> Identity a -> Identity b
fmapIdentity f (Identity x) = Identity (f x) 

identReturn = Identity

identMonad :: Identity a -> (a -> Identity b) -> Identity b
m `identMonad` k  = k (runIdentity m)

-- | The reader monad transformer,
-- which adds a read-only environment to the given monad.
--
-- The 'return' function ignores the environment, while @m '>>=' k@
-- passes the inherited environment to both subcomputations:
--
-- <<images/bind-ReaderT.svg>>
--
--
-- @ReaderT r m@ is strict if and only if @m@ is.
data ReaderT r m a = ReaderT { runReaderT :: r -> m a }

-- | The parameterizable reader monad, which is non-strict.
--
-- Computations are functions of a shared environment.
--
-- The 'return' function ignores the environment, while @m '>>=' k@
-- passes the inherited environment to both subcomputations:
--
-- <<images/bind-ReaderT.svg>>
--
type Reader r = ReaderT r Identity

-- | Runs a @Reader@ and extracts the final value from it.
-- (The inverse of 'reader'.)
runReader
    :: Reader r a       -- ^ A @Reader@ to run.
    -> r                -- ^ An initial environment.
    -> a
runReader m = runIdentity . runReaderT m
{-# INLINE runReader #-}

-- | Transform the computation inside a @ReaderT@.
--
-- * @'runReaderT' ('mapReaderT' f m) = f . 'runReaderT' m@
mapReaderT :: (m a -> n b) -> ReaderT r m a -> ReaderT r n b
mapReaderT f m = ReaderT $ (f . runReaderT m)
{-# INLINE mapReaderT #-}

fmap :: (a -> b) -> Reader s a -> Reader s b
fmap f  = mapReaderT (fmapIdentity f )

pure :: a -> Reader r a
pure    = liftReaderT . identReturn

(<**>) :: Identity (a -> b) -> Identity a -> Identity b
(<**>) f x = Identity ((runIdentity f) (runIdentity x))

(<*>) :: Reader r (a1 -> a2) -> Reader r a1 -> Reader r a2
f <*> v = ReaderT $ (\ r -> runReaderT f r <**> runReaderT v r)

return   = liftReaderT . identReturn

m >>= k  = ReaderT $ (\r -> do
    runReaderT m r `identMonad` (\a -> runReaderT (k a) r))

liftReaderT :: m a -> ReaderT r m a
liftReaderT m = ReaderT (const m)
{-# INLINE liftReaderT #-}

{-# ANN fmapId defaultParams #-}
fmapId :: r -> Reader r a -> Equation
fmapId s xs = runReaderT (fmap id xs) s === runReaderT (id xs) s

{-# ANN fmapComposition defaultParams #-}
fmapComposition :: r -> (b -> c) -> (a -> b) -> Reader r a -> Equation
fmapComposition s f g xs = runReaderT (fmap (f . g) xs) s === runReaderT ((fmap f . fmap g) xs) s

{-# ANN appIdentity defaultParams #-}
appIdentity :: r -> Reader r a -> Equation
appIdentity s v = runReaderT (pure id <*> v) s === runReaderT v s

{-# ANN appComposition defaultParams #-}
appComposition :: r -> Reader r (a1 -> b) -> Reader r (a2 -> a1) -> Reader r a2 -> Equation
appComposition s u v w = runReaderT (pure (.) <*> u <*> v <*> w) s === runReaderT (u <*> (v <*> w)) s

{-# ANN appHomomorphism defaultParams #-}
appHomomorphism :: forall r a b . r -> (a -> b) -> a -> Equation
appHomomorphism s f x = runReaderT (pure f <*> (pure :: a -> Reader r a) x) s === runReaderT (pure (f x)) s

{-# ANN appInterchange defaultParams #-}
appInterchange :: r -> Reader r (a -> b) -> a -> Equation
appInterchange s u y = runReaderT (u <*> pure y) s === runReaderT (pure ($ y) <*> u) s

{-# ANN monadLeftIdentity defaultParams #-}
monadLeftIdentity :: r -> a -> (a -> Reader r b) -> Equation
monadLeftIdentity s a k = runReaderT (return a >>= k) s === runReaderT (k a) s

{-# ANN monadRightIdentity defaultParams #-}
monadRightIdentity :: r -> Reader r b -> Equation
monadRightIdentity s m = runReaderT (m >>= return) s === runReaderT m s

{-# ANN monadAssociativity defaultParams #-}
monadAssociativity :: r -> Reader r a1 -> p -> (a1 -> Reader r a2) -> (a2 -> Reader r b) -> Equation
monadAssociativity s m x k h = runReaderT (m >>= (\x -> k x >>= h)) s === runReaderT ((m >>= k) >>= h) s
