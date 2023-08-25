module Language.Hott.Monad
  ( MonadFresh (..)
  , module Control.Applicative
  , module Control.Monad
  , module Control.Monad.RWS
  , module Control.Monad.Except
  , module Data.Functor
  , guardError
  )
where

import Control.Applicative
import Control.Monad
import Control.Monad.Except
import Control.Monad.RWS
import Data.Bool
import Data.Functor
import Data.Kind

type MonadFresh :: (Type -> Type) -> Constraint
class (Monad m) => MonadFresh m where
  type Fresh m :: Type
  fresh :: m (Fresh m)
  default fresh :: (MonadState s m, Fresh m ~ s, Enum s) => m (Fresh m)
  fresh = get <* modify succ

guardError :: (MonadError e m) => e -> Bool -> m ()
guardError e = bool (throwError e) (pure ())
