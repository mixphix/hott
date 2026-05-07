module Control.Monad.Interpret
  ( Var (Var)
  , var
  , MonadInterpret
    ( assume
    , typeof
    , define
    , recall
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
  -- | Assume that the type is inhabited by the identifier.
  assume :: Var i p -> m ()
  -- | Look up the type of an identifier, if it exists.
  typeof :: i -> m (Maybe p)
  -- | Give the definition of an identifier.
  define :: Var i p -> m ()
  -- | Look up the definition of an identifier, if it exists.
  recall :: i -> m (Maybe p)

  -- | Generate and use a fresh identifier.
  fresh :: (i -> m x) -> m x
  -- | Alpha-conversion.
  repoint :: p -> i -> (p -> m p)
  -- | Equivalence up to alpha-conversion.
  (===) :: p -> p -> m ()

  -- | Find the type of a point.
  infer :: p -> m p
  -- | Calculate the beta-reduction.
  compute :: p -> m p

-- |
-- Suppose for the sake of the argument that the type is inhabited by the identifier.
-- Then, reset the original context.
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
