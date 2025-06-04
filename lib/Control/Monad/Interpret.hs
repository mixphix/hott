module Control.Monad.Interpret
  ( Var (Var)
  , var
  , MonadInterpret
    ( recall
    , assume
    , fresh
    , repoint
    , (===)
    , infer
    , compute
    )
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
import Data.Functor.Identity
import Data.Maybe
import Data.Ord
import Data.Traversable
import GHC.Show
import Text.Read (Read)

data Var i p = Var i p
  deriving (Eq, Ord, Show, Read, Functor, Foldable, Traversable)
var :: (i -> p -> x) -> (Var i p -> x)
var f (Var i p) = f i p

class (MonadState n m) => MonadInterpret i n p m | m -> i n p where
  recall :: i -> m (Maybe p)
  assume :: Var i p -> m ()

  fresh :: (i -> m x) -> m x
  repoint :: p -> i -> (p -> m p)
  (===) :: p -> p -> m ()

  infer :: p -> m p
  compute :: p -> m p

suppose :: (MonadInterpret i n p m) => Var i p -> m x -> m x
suppose __ interpret = do
  n <- get
  x <- assume __ >> interpret
  put n
  pure x
supposeAll :: (MonadInterpret i n p m) => [Var i p] -> m x -> m x
supposeAll __ interpret = case __ of
  [] -> interpret
  v : vs -> suppose v (supposeAll vs interpret)

type InterpretT e n p m x = ExceptT e (StateT n m) x
type Interpret e n p x = InterpretT e n p Identity x

runInterpretT ::
  (Monad m) => (InterpretT e n p m x -> n -> m (Either e x, n))
runInterpretT = runStateT . runExceptT

runInterpret :: Interpret e n p x -> n -> (Either e x, n)
runInterpret = (runIdentity .) . runInterpretT
