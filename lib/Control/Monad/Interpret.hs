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
  , MonadError (Failure l) m
  , HasParseErrors (Failure l)
  ) =>
  MonadInterpret l m
  where
  data Failure l :: Type
  failure :: Failure l -> m x
  failure = throwError

  type Label l :: Type
  fresh :: m (Label l)
  repoint :: l -> l -> Label l -> m l

  data Context l :: Type
  context :: m (Context l)
  lookup :: Label l -> m (Maybe l)

  acknowledge :: Var l -> m ()
  locally :: Context l -> m x -> m x
  default locally :: (MonadState (Context l) m) => Context l -> m x -> m x
  locally ctx act = do
    c0 <- get
    put ctx
    x <- act
    put c0
    pure x
  localVar :: Var l -> m x -> m x
  default localVar :: (MonadState (Context l) m) => Var l -> m x -> m x
  localVar var act = do
    ctx <- context
    acknowledge var
    x <- act
    put ctx
    pure x

  infer :: l -> m l
  check :: l -> l -> m ()

type InterpretT :: Type -> (Type -> Type) -> Type -> Type
type InterpretT l m x =
  ParsecT Text () (ExceptT (Failure l) (StateT (Context l) m)) x
type Interpret l x = InterpretT l Identity x

runInterpretT ::
  (Monad m, HasParseErrors (Failure l)) =>
  (InterpretT l m x -> Context l -> Text -> m (Either (Failure l) x, Context l))
runInterpretT i c src = do
  let exceptT = Parsec.runParserT i () "" src
      stateT = runExceptT exceptT
   in runStateT stateT c >>= \case
        (Left f, ctx) -> pure (Left f, ctx)
        (Right (Left f), ctx) -> pure (Left (parseFailure f), ctx)
        (Right (Right x), ctx) -> pure (Right x, ctx)

runInterpret ::
  (HasParseErrors (Failure l)) =>
  (Interpret l x -> Context l -> Text -> (Either (Failure l) x, Context l))
runInterpret = ((runIdentity .) .) . runInterpretT
