{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}

module Logic where

import           Control.Comonad.Cofree
import           Control.Monad.Free
import           Data.Functor.Identity
import           Prelude                hiding (and, not, or)
import qualified Prelude

-- Coproduct: sum of two functors!
data (f :+: g) e = InL (f e) | InR (g e)

instance (Functor f, Functor g) => Functor (f :+: g) where
  fmap f (InL k) = InL (fmap f k)
  fmap f (InR k) = InR (fmap f k)

-- Product: two functors together!
data (f :*: g) e = f e :*: g e

instance (Functor f, Functor g) => Functor (f :*: g) where
  fmap f (h :*: k) = fmap f h :*: fmap f k

-- "this functor contains this other functor"
class (Functor sub, Functor sup) => (sub :<: sup) where
  inj :: sub a -> sup a

instance (Functor f) => f :<: f where
  inj = id

instance {-# OVERLAPPING #-} (Functor f, Functor g) => f :<: (f :+: g) where
  inj = InL

instance {-# OVERLAPPING #-} (Functor h, f :<: g) => f :<: (h :+: g) where
  inj = InR . inj

-- A pairing between two functors is a way to annihilate them both and recover
-- a value from them.

class (Functor f, Functor g) => Pairing f g where
  pair :: (a -> b -> r) -> f a -> g b -> r

instance Pairing Identity Identity where
  pair f (Identity a) (Identity b) = f a b

instance Pairing ((->) a) ((,) a) where
  pair p f = uncurry (p . f)

instance Pairing ((,) a) ((->) a) where
  pair p f g = pair (flip p) g f

instance Pairing f g => Pairing (Cofree f) (Free g) where
  pair p (a :< _) (Pure x) = p a x
  pair p (_ :< fs) (Free gs) = pair (pair p) fs gs

instance (Pairing f f', Pairing g g') => Pairing (f :+: g) (f' :*: g') where
  pair p (InL x) (a :*: _) = pair p x a
  pair p (InR x) (_ :*: b) = pair p x b

instance (Pairing f f', Pairing g g') => Pairing (f :*: g) (f' :+: g') where
  pair p (a :*: _) (InL x) = pair p a x
  pair p (_ :*: b) (InR x) = pair p b x

-- in the DSL, we get:
-- data AddF k 
--   = Add        -- the command name
--     Int        -- an argument to pass to the command
--     (Bool -> k) -- (return value -> k)
-- 
-- -- which pairs with:
-- data CoAddF k 
--   = CoAdd      -- Interprets a command
--   (Int         -- Function that takes an argument
--   -> (Bool, k))-- Returns *at least* the k arg, as well as others.

-- Now we can define terms in our language as well as means of evaluating them.
-- We get literals for free from the `Pure` constructor in the Free monad.

data AndF k = forall f. (AndF :<: f) => And (Free f Bool) (Free f Bool) (Bool -> k)

instance Functor AndF where
  fmap f (And a b k) = And a b (f . k)

data OrF k = forall f. (OrF :<: f) => Or (Free f Bool) (Free f Bool) (Bool -> k)

instance Functor OrF where
  fmap f (Or a b k) = Or a b (f . k)

(.||) :: (OrF :<: f) => Free f Bool -> Free f Bool -> Free f Bool
a .|| b = Free . inj $ Or a b Pure

(.&&) :: (AndF :<: f) => Free f Bool -> Free f Bool -> Free f Bool
a .&& b = Free . inj $ And a b Pure

true :: Functor f => Free f Bool
true = Pure True

false :: Functor f => Free f Bool
false = Pure False

testProgram :: (AndF :<: f) => Free f Bool
testProgram = do
  asdf <- true .&& false
  hmmm <- false .&& true
  wat  <- pure asdf .&& pure hmmm
  return asdf

test1 :: (AndF :<: f, OrF :<: f) => Free f Bool
test1 = do
  asdf <- true .|| false
  wat <- pure asdf .&& false .&& true
  pure asdf .|| pure wat
