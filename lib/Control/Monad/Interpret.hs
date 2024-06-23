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
import Control.Monad.State
import Control.Monad.Writer
import Data.Eq
import Data.Foldable
import Data.Function
import Data.Functor.Identity
import Data.Maybe
import Data.Ord
import Data.Traversable
import GHC.Show

data Var i p = Var i p deriving (Eq, Ord, Show, Functor, Foldable, Traversable)
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

locally :: (MonadInterpret i n p m) => n -> m x -> m x
locally __ interpret = do
  n <- get
  x <- put __ >> interpret
  put n
  pure x
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

type InterpretT i e n p m x = WriterT [e] (StateT n m) x
type Interpret i e n p x = InterpretT i e n p Identity x

runInterpretT :: (Monad m) => (InterpretT i e n p m x -> n -> m ((x, [e]), n))
runInterpretT = runStateT . runWriterT

runInterpret :: Interpret i e n p x -> n -> ((x, [e]), n)
runInterpret = (runIdentity .) . runInterpretT
