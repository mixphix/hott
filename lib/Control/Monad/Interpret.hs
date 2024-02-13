module Control.Monad.Interpret
  ( Var (Var)
  , MonadInterpret (..)
  , locally
  , localVar
  , InterpretT
  , runInterpretT
  , Interpret
  , runInterpret
  , HasParseErrors (..)
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
import Text.Parsec (ParsecT)
import Text.Parsec qualified as Parsec

data Var x = Var Text x deriving (Eq, Ord, Show)

class HasParseErrors e where
  parseFailure :: Parsec.ParseError -> e

type MonadInterpret :: Type -> Type -> (Type -> Type) -> Constraint
class
  (MonadError e m, HasParseErrors e) =>
  MonadInterpret e p m
    | m -> p e
  where
  data Context p :: Type

  context :: m (Context p)
  default context :: (MonadState (Context p) m) => m (Context p)
  context = get
  setContext :: Context p -> m ()
  default setContext :: (MonadState (Context p) m) => Context p -> m ()
  setContext = put

  acknowledge :: Var p -> m ()
  lookup :: Text -> m (Maybe p)

  fresh :: m Text
  repoint :: p -> p -> Text -> m p

  infer :: p -> m p
  check :: p -> p -> m ()

locally :: (MonadInterpret e p m) => Context p -> m x -> m x
locally ctx act = do
  c0 <- context
  setContext ctx
  x <- act
  setContext c0
  pure x
localVar :: (MonadInterpret e p m) => Var p -> m x -> m x
localVar var act = do
  ctx <- context
  acknowledge var
  x <- act
  setContext ctx
  pure x

type InterpretT :: Type -> Type -> (Type -> Type) -> Type -> Type
type InterpretT e p m x =
  ParsecT Text () (ExceptT e (StateT (Context p) m)) x
type Interpret e p x = InterpretT e p Identity x

runInterpretT ::
  (Monad m, HasParseErrors e) =>
  (InterpretT e p m x -> Context p -> Text -> m (Either e x, Context p))
runInterpretT i c src =
  runStateT (runExceptT (Parsec.runParserT i () "" src)) c <&> \case
    (Left f, ctx) -> (Left f, ctx)
    (Right (Left f), ctx) -> (Left (parseFailure f), ctx)
    (Right (Right x), ctx) -> (Right x, ctx)

runInterpret ::
  (HasParseErrors e) =>
  (Interpret e p x -> Context p -> Text -> (Either e x, Context p))
runInterpret = ((runIdentity .) .) . runInterpretT
