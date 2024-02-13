module Control.Monad.Interpret
  ( Var (Var)
  , MonadInterpret (..)
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

class HasParseErrors fail where
  parseFailure :: Parsec.ParseError -> fail

type MonadInterpret :: Type -> (Type -> Type) -> Constraint
class
  ( Monad m
  , MonadError (Failure p) m
  , HasParseErrors (Failure p)
  ) =>
  MonadInterpret p m
  where
  data Failure p :: Type
  failure :: Failure p -> m x
  failure = throwError

  type Label p :: Type
  fresh :: m (Label p)
  repoint :: p -> p -> Label p -> m p

  data Context p :: Type
  context :: m (Context p)
  lookup :: Label p -> m (Maybe p)
  acknowledge :: Var p -> m ()
  locally :: Context p -> m x -> m x
  default locally :: (MonadState (Context p) m) => Context p -> m x -> m x
  locally ctx act = do
    c0 <- get
    put ctx
    x <- act
    put c0
    pure x
  localVar :: Var p -> m x -> m x
  default localVar :: (MonadState (Context p) m) => Var p -> m x -> m x
  localVar var act = do
    ctx <- context
    acknowledge var
    x <- act
    put ctx
    pure x

  infer :: p -> m p
  check :: p -> p -> m ()

type InterpretT :: Type -> (Type -> Type) -> Type -> Type
type InterpretT p m x =
  ParsecT Text () (ExceptT (Failure p) (StateT (Context p) m)) x
type Interpret p x = InterpretT p Identity x

runInterpretT ::
  (Monad m, HasParseErrors (Failure p)) =>
  (InterpretT p m x -> Context p -> Text -> m (Either (Failure p) x, Context p))
runInterpretT i c src =
  runStateT (runExceptT (Parsec.runParserT i () "" src)) c <&> \case
    (Left f, ctx) -> (Left f, ctx)
    (Right (Left f), ctx) -> (Left (parseFailure f), ctx)
    (Right (Right x), ctx) -> (Right x, ctx)

runInterpret ::
  (HasParseErrors (Failure p)) =>
  (Interpret p x -> Context p -> Text -> (Either (Failure p) x, Context p))
runInterpret = ((runIdentity .) .) . runInterpretT
