module Control.Monad.Interpret
  ( Var (Var)
  , Misparse (misparse)
  , MonadInterpret
    ( acknowledge
    , lookup
    , fresh
    , repoint
    , infer
    , (√)
    , compute
    )
  , locally
  , localVar
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
import Data.Function
import Data.Functor
import Data.Functor.Identity
import Data.Maybe
import Data.Ord
import Data.Text (Text)
import GHC.Show
import Text.Parsec (ParseError, ParsecT)
import Text.Parsec qualified as Parsec

data Var i x = Var i x deriving (Eq, Ord, Show)

class Misparse e where
  misparse :: ParseError -> e

class
  (MonadError e m, MonadState n m, Misparse e) =>
  MonadInterpret i e n p m
    | m -> i e n p
  where
  lookup :: i -> m (Maybe p)
  acknowledge :: Var i p -> m ()

  fresh :: (i -> m x) -> m x
  repoint :: p -> i -> (p -> m p)

  infer :: p -> m p
  (√) :: p -> p -> m ()
  compute :: p -> m p

locally :: (MonadInterpret i e n p m) => n -> m x -> m x
locally new interpret = do
  n <- get
  put new
  x <- interpret
  put n
  pure x
localVar :: (MonadInterpret i e n p m) => Var i p -> m x -> m x
localVar var interpret = do
  n <- get
  acknowledge var
  x <- interpret
  put n
  pure x

type InterpretT i e n p m x = ParsecT Text () (ExceptT e (StateT n m)) x
type Interpret i e n p x = InterpretT i e n p Identity x

runInterpretT ::
  (Monad m, Misparse e) =>
  (InterpretT i e n p m x -> n -> Text -> m (Either e x, n))
runInterpretT i c src =
  runStateT (runExceptT (Parsec.runParserT i () "" src)) c <&> \case
    (Left e, n) -> (Left e, n)
    (Right (Left e), n) -> (Left (misparse e), n)
    (Right (Right x), n) -> (Right x, n)

runInterpret ::
  (Misparse e) => Interpret i e n p x -> n -> Text -> (Either e x, n)
runInterpret = ((runIdentity .) .) . runInterpretT
