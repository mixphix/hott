module Language.Hott.Monad
  ( MonadFresh (..)
  , MonadContext (..)
  , module Control.Applicative
  , module Control.Monad
  , module Control.Monad.Except
  , module Control.Monad.State
  , module Data.Functor
  )
where

import Control.Applicative
import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Data.Functor
import Data.Kind (Constraint, Type)

type MonadFresh :: (Type -> Type) -> Constraint
class (Monad m) => MonadFresh m where
  type Fresh m :: Type
  fresh :: m (Fresh m)

type MonadContext :: (Type -> Type) -> Constraint
class MonadContext m where
  type Context m :: Type
  context :: m (Context m)
