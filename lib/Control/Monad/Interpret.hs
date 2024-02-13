module Control.Monad.Interpret
  ( Var (Var)
  , MonadInterpret (..)
  , locally
  , localVar
  , InterpretT
  , runInterpretT
  , Interpret
  , runInterpret
  , Misparse (..)
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
import Data.Kind (Constraint, Type)
import Data.Maybe
import Data.Ord
import Data.Text (Text)
import GHC.Show
import Text.Parsec (ParseError, ParsecT)
import Text.Parsec qualified as Parsec

data Var x = Var Text x deriving (Eq, Ord, Show)

class Misparse e where
  misparse :: ParseError -> e

type MonadInterpret :: Type -> Type -> Type -> (Type -> Type) -> Constraint
class (MonadError e m, Misparse e) => MonadInterpret e n p m | m -> e n p where
  context :: m n
  default context :: (MonadState n m) => m n
  context = get
  setContext :: n -> m ()
  default setContext :: (MonadState n m) => n -> m ()
  setContext = put

  acknowledge :: Var p -> m ()
  lookup :: Text -> m (Maybe p)

  fresh :: m Text
  repoint :: p -> p -> Text -> m p

  infer :: p -> m p
  check :: p -> p -> m ()

locally :: (MonadInterpret e n p m) => n -> m x -> m x
locally ctx act = do
  c0 <- context
  setContext ctx
  x <- act
  setContext c0
  pure x
localVar :: (MonadInterpret e n p m) => Var p -> m x -> m x
localVar var act = do
  ctx <- context
  acknowledge var
  x <- act
  setContext ctx
  pure x

type InterpretT :: Type -> Type -> Type -> (Type -> Type) -> Type -> Type
type InterpretT e n p m x = ParsecT Text () (ExceptT e (StateT n m)) x
type Interpret e n p x = InterpretT e n p Identity x

runInterpretT ::
  (Monad m, Misparse e) =>
  (InterpretT e n p m x -> n -> Text -> m (Either e x, n))
runInterpretT i c src =
  runStateT (runExceptT (Parsec.runParserT i () "" src)) c <&> \case
    (Left f, ctx) -> (Left f, ctx)
    (Right (Left f), ctx) -> (Left (misparse f), ctx)
    (Right (Right x), ctx) -> (Right x, ctx)

runInterpret ::
  (Misparse e) => Interpret e n p x -> n -> Text -> (Either e x, n)
runInterpret = ((runIdentity .) .) . runInterpretT
