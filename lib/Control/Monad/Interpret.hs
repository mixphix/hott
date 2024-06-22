module Control.Monad.Interpret
  ( Var (Var)
  , var
  , MonadInterpret
    ( recall
    , assume
    , fresh
    , repoint
    , infer
    , compute
    )
  , locally
  , suppose
  , supposeAll
  , InterpretT
  , runInterpretT
  , Interpret
  , runInterpret
  ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Data.Either
import Data.Eq
import Data.Foldable
import Data.Function
import Data.Functor
import Data.Functor.Identity
import Data.Maybe
import Data.Ord
import Data.Traversable
import GHC.Show

data Var i p = Var i p deriving (Eq, Ord, Show, Functor, Foldable, Traversable)
var :: (i -> p -> x) -> (Var i p -> x)
var f (Var i p) = f i p

class
  ( MonadError e m
  , MonadState n m
  ) =>
  MonadInterpret i e n p m
    | m -> i e n p
  where
  recall :: i -> m (Maybe p)
  assume :: Var i p -> m ()

  fresh :: (i -> m x) -> m x
  repoint :: p -> i -> (p -> m p)

  infer :: p -> m p
  compute :: p -> m p

locally :: (MonadInterpret i e n p m) => n -> m x -> m x
locally __ interpret = do
  n <- get
  x <- put __ >> interpret
  put n
  pure x
suppose :: (MonadInterpret i e n p m) => Var i p -> m x -> m x
suppose __ interpret = do
  n <- get
  x <- assume __ >> interpret
  put n
  pure x
supposeAll :: (MonadInterpret i e n p m) => [Var i p] -> m x -> m x
supposeAll __ interpret = case __ of
  [] -> interpret
  v : vs -> suppose v (supposeAll vs interpret)

type InterpretT i e n p m x = ExceptT e (StateT n m) x
type Interpret i e n p x = InterpretT i e n p Identity x

runInterpretT :: (Monad m) => (InterpretT i e n p m x -> n -> m (Either e x, n))
runInterpretT m c =
  runStateT (runExceptT m) c <&> \case
    (Left e, n) -> (Left e, n)
    (Right x, n) -> (Right x, n)

runInterpret :: Interpret i e n p x -> n -> (Either e x, n)
runInterpret = (runIdentity .) . runInterpretT
