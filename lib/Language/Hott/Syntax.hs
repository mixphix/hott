module Language.Hott.Syntax
  ( Name (..)
  , Var (..)
  , Point (..)
  , InferError (..)
  , MonadInfer (..)
  , InferT (..)
  , Infer
  , InterpretT (..)
  , Interpret
  , runInferT
  , runInterpretT
  , (-->)
  , (**)
  , negate
  , (===)
  ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Data.Bool
import Data.Either
import Data.Eq
import Data.Function
import Data.Functor.Identity
import Data.Kind (Constraint, Type)
import Data.Map.Strict (Map, (!?))
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.Ord
import Data.Semigroup (Semigroup ((<>)))
import Data.Text (Text, pack)
import Data.Tuple
import GHC.Enum
import GHC.Show
import Numeric.Natural (Natural)
import Text.Parsec qualified as Parsec

newtype Name = Name Text
  deriving (Eq, Ord, Show)

data Var x = Var Name x
  deriving (Eq, Ord, Show)

data Point
  = U Natural
  | Point Text
  | Pi (Var Point) Point
  | Lam (Var Point) Point
  | App Point Point
  | Sig (Var Point) Point
  | Pair Point Point
  | Proj
      (Var Point)
      (Var Point)
      (Var (Var Point))
      Point
  | Sum Point Point
  | InL Point
  | InR Point
  | Empty
  | Singleton
  | Single
  | Naturals
  | Zero
  | Succ Point
  | IndN
      (Var Point)
      Point
      (Var (Var Point))
      Point
  | Equality Point Point Point
  | Refl Point
  | Path
      Point
      (Var (Var (Var Point)))
      (Var Point)
      Point
      Point
      Point
  | FunExt Point Point
  | UA Natural Point Point
  deriving (Eq, Ord, Show)

data InferError l
  = Crash
  | NotInContext Name
  | AlreadyBound Name l
  | Unequal l l
  | UniverseMismatch l Natural l Natural
  | NotAType l l
  | NotAFunction l
  | NotAPair l
  | NotANatural l
  | ParseError Parsec.ParseError

type MonadInfer :: Type -> (Type -> Type) -> Constraint
class (Monad m, MonadError (InferError l) m) => MonadInfer l m where
  failure :: InferError l -> m x
  failure = throwError

  type Fresh l :: Type
  fresh :: m (Fresh l)
  repoint :: l -> l -> Fresh l -> m l

  type Context l :: Type
  context :: m (Context l)
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
  default check :: (Eq l) => l -> l -> m ()
  check a t = do
    ta <- infer a
    unless (t == ta) $ failure (Unequal t ta)

given :: (MonadInfer Point m) => (Name -> m (Var Point))
given name =
  context >>= \ctx -> case ctx !? name of
    Nothing -> failure (NotInContext name)
    Just tx -> pure (Var name tx)

universe :: (MonadInfer Point m) => Point -> m Natural
universe point =
  infer point >>= \case
    U i -> pure i
    t -> failure (NotAType point t)

sameUniverse :: (MonadInfer Point m) => Var Point -> Point -> m Natural
sameUniverse (Var _ p0) p1 = do
  u0 <- universe p0
  u1 <- universe p1
  unless (u0 == u1) $ failure (UniverseMismatch p0 u0 p1 u1)
  pure u0

typ :: (MonadInfer Point m) => Point -> m ()
typ = void . universe

(===) :: (MonadInfer Point m) => Point -> m Point -> m ()
p0 === run = do
  p1 <- run
  unless (p0 == p1) $ failure (Unequal p0 p1)

(-->) :: (MonadInfer Point m) => Point -> Point -> m Point
a --> b = do
  ui <- universe a
  ui' <- universe b
  x <- (<>) "_" <$> fresh
  let fun = Pi (Var (Name x) a) b
  unless (ui == ui') $ failure (UniverseMismatch a ui b ui')
  pure fun

(**) :: (MonadInfer Point m) => Point -> Point -> m Point
a ** b = do
  ui <- universe a
  ui' <- universe b
  x <- (<>) "_" <$> fresh
  let pair = Sig (Var (Name x) a) b
  unless (ui == ui') $ failure (UniverseMismatch a ui b ui')
  pure pair

negate :: (MonadInfer Point m) => Point -> m Point
negate point = do
  typ point
  x <- fresh
  pure (Pi (Var (Name x) point) Empty)

type InferT :: Type -> (Type -> Type) -> Type -> Type
newtype InferT l m x = Infer
  {getInferT :: ExceptT (InferError l) (State (Map Name l, Natural)) x}
  deriving
    ( Functor
    , Applicative
    , Monad
    , MonadError (InferError l)
    , MonadState (Map Name l, Natural)
    )
type Infer l = InferT l Identity

runInferT ::
  InferT l m x ->
  (Map Name l, Natural) ->
  (Either (InferError l) x, (Map Name l, Natural))
runInferT (Infer i) = runState (runExceptT i)

type InterpretT :: Type -> (Type -> Type) -> Type -> Type
newtype InterpretT l m x = Interpret
  {getInterpretT :: Parsec.ParsecT Text () (InferT l m) x}
  deriving
    ( Functor
    , Applicative
    , Monad
    , MonadError (InferError l)
    , MonadState (Map Name l, Natural)
    )
type Interpret l = InterpretT l Identity

runInterpretT ::
  InterpretT l m x ->
  Text ->
  (Map Name l, Natural) ->
  Either (InferError l) (x, (Map Name l, Natural))
runInterpretT (Interpret p) src init =
  case runInferT (Parsec.runParserT p () "" src) init of
    (Left x, _) -> Left x
    (Right (Left x), _) -> Left (ParseError x)
    (Right (Right x), ctx) -> Right (x, ctx)

instance (Monad m) => MonadInfer Point (InterpretT Point m) where
  type Fresh Point = Text
  fresh = do
    (ctx, freshness) <- get
    put (ctx, succ freshness)
    pure (pack $ "_" <> show freshness)
  repoint point with name = case point of
    U n -> pure (U n)
    Point p | p == name -> pure with
    Point p -> pure (Point p)
    Pi a@(Var (Name x) ta) tb ->
      if x == name
        then do
          x' <- fresh
          p <-
            Pi . (Var (Name x'))
              <$> repoint ta (Point x') x
              <*> repoint tb (Point x') x
          repoint p with name
        else Pi a <$> (repoint tb with name)
    Lam a@(Var (Name x) ta) b ->
      if x == name
        then do
          x' <- fresh
          p <-
            Lam . (Var (Name x'))
              <$> repoint ta (Point x') x
              <*> repoint b (Point x') x
          repoint p with name
        else Lam a <$> repoint b with name
    App p0 p1 -> App <$> repoint p0 with name <*> repoint p1 with name
    Sig a@(Var (Name x) ta) tb ->
      if x == name
        then do
          x' <- fresh
          p <-
            Pi . (Var (Name x'))
              <$> (repoint ta (Point x') x)
              <*> (repoint tb (Point x') x)
          repoint p with name
        else Pi a <$> repoint tb with name
    Pair a b -> Pair <$> repoint a with name <*> repoint b with name
    Proj
      sig@(Var (Name p) tp)
      c@(Var (Name z) tc)
      proj@(Var (Name x) (Var (Name y) g))
      pair
        | p == name -> do
            p' <- fresh
            tp' <- repoint tp (Point p') p
            repoint (Proj (Var (Name p') tp') c proj pair) with name
        | z == name -> do
            z' <- fresh
            tc' <- repoint tc (Point z') z
            repoint (Proj sig (Var (Name z') tc') proj pair) with name
        | x == name -> do
            x' <- fresh
            g' <- repoint g (Point x') x
            repoint (Proj sig c (Var (Name x') (Var (Name y) g')) pair) with name
        | y == name -> do
            y' <- fresh
            g' <- repoint g (Point y') y
            repoint (Proj sig c (Var (Name x) (Var (Name y') g')) pair) with name
        | otherwise -> do
            tp' <- repoint tp with name
            tc' <- repoint tc with name
            g' <- repoint g with name
            pair' <- repoint pair with name
            let sig' = Var (Name p) tp'
                c' = Var (Name z) tc'
                proj' = Var (Name x) (Var (Name y) g')
            pure (Proj sig' c' proj' pair')
    Sum ta tb -> Sum <$> repoint ta with name <*> repoint tb with name
    InL a -> InL <$> repoint a with name
    InR b -> InL <$> repoint b with name
    Empty -> pure Empty
    Singleton -> pure Singleton
    Single -> pure Single
    Naturals -> pure Naturals
    Zero -> pure Zero
    Succ n -> pure (Succ n)
    IndN c@(Var (Name z) tc) c0 cs@(Var (Name x) (Var (Name y) c1)) n
      | z == name -> do
          z' <- fresh
          tc' <- repoint tc (Point z') z
          repoint (IndN (Var (Name z') tc') c0 cs n) with name
      | x == name -> do
          x' <- fresh
          c1' <- repoint c1 (Point x') x
          repoint (IndN c c0 (Var (Name x') (Var (Name y) c1')) n) with name
      | y == name -> do
          y' <- fresh
          c1' <- repoint c1 (Point y') y
          repoint (IndN c c0 (Var (Name x) (Var (Name y') c1')) n) with name
      | otherwise -> do
          tc' <- repoint tc with name
          c1' <- repoint c1 with name
          pure (IndN (Var (Name z) tc') c0 (Var (Name x) (Var (Name y) c1')) n)
    Equality ta a b ->
      Equality
        <$> repoint ta with name
        <*> repoint a with name
        <*> repoint b with name
    Refl a -> Refl <$> repoint a with name
    Path
      ta
      pc@(Var (Name x) (Var (Name y) (Var (Name p) tc)))
      (Var (Name z) c)
      a
      b
      path
        | x == name -> do
            x' <- fresh
            tc' <- repoint tc (Point x') x
            repoint
              ( Path
                  ta
                  (Var (Name x') (Var (Name y) (Var (Name p) tc')))
                  (Var (Name z) c)
                  a
                  b
                  path
              )
              with
              name
        | y == name -> do
            y' <- fresh
            tc' <- repoint tc (Point y') y
            repoint
              ( Path
                  ta
                  (Var (Name x) (Var (Name y') (Var (Name p) tc')))
                  (Var (Name z) c)
                  a
                  b
                  path
              )
              with
              name
        | p == name -> do
            p' <- fresh
            tc' <- repoint tc (Point p') x
            repoint
              ( Path
                  ta
                  (Var (Name x) (Var (Name y) (Var (Name p') tc')))
                  (Var (Name z) c)
                  a
                  b
                  path
              )
              with
              name
        | z == name -> do
            z' <- fresh
            c' <- repoint c (Point z') z
            repoint
              ( Path
                  ta
                  pc
                  (Var (Name z') c')
                  a
                  b
                  path
              )
              with
              name
        | otherwise -> do
            tc' <- repoint tc with name
            c' <- repoint c with name
            a' <- repoint a with name
            b' <- repoint b with name
            path' <- repoint path with name
            pure
              ( Path
                  ta
                  (Var (Name x) (Var (Name y) (Var (Name p) tc')))
                  (Var (Name z) c')
                  a'
                  b'
                  path'
              )
    FunExt f g -> FunExt <$> repoint f with name <*> repoint g with name
    UA i ta tb -> UA i <$> repoint ta with name <*> repoint tb with name

  type Context Point = Map Name Point
  context = gets fst
  acknowledge (Var name ty) = do
    (ctx, freshness) <- get
    case ctx !? name of
      Nothing -> put (Map.insert name ty ctx, freshness)
      Just _ -> failure (AlreadyBound name ty)
  locally c act = do
    (ctx, freshness) <- get
    put (c, freshness)
    x <- act
    put (ctx, freshness)
    pure x
  localVar var act = do
    (ctx, freshness) <- get
    acknowledge var
    x <- act
    put (ctx, freshness)
    pure x

  infer point = case point of
    U n -> pure (U (succ n))
    Point x -> do
      Var _ tx <- given (Name x)
      pure tx
    Pi (Var x ta) tb -> U <$> sameUniverse (Var x ta) tb
    Lam (Var x ta) b -> do
      typ ta
      tb <- localVar (Var x ta) $ infer b
      pure (Pi (Var x ta) tb)
    App (Pi (Var (Name x) ta) tb) a -> do
      ta === infer a
      typ tb
      repoint tb a x
    App f _ -> failure (NotAFunction f)
    Sig (Var x ta) tb -> U <$> sameUniverse (Var x ta) tb
    Pair a b -> do
      ta <- infer a
      x <- fresh
      tb <- localVar (Var (Name x) ta) do
        infer =<< repoint b a x
      pure (Sig (Var (Name x) ta) tb)
    Proj
      (Var _ tp@(Sig (Var _ ta) tb))
      (Var (Name z) tc)
      (Var (Name x) (Var (Name y) g))
      p@(Pair a b) -> do
        tp === infer p
        localVar (Var (Name z) tp) $ typ tc
        localVar (Var (Name x) ta) $ localVar (Var (Name y) tb) do
          c' <- repoint tc p z
          g' <- repoint g a x >>= \g_ -> repoint g_ b y
          c' === infer g'
          pure c'
    Proj (Var _ (Sig _ _)) _ _ p -> failure (NotAPair p)
    Proj (Var _ tp) _ _ _ -> failure (NotAPair tp)
    Sum ta tb -> U <$> sameUniverse (Var (Name "") ta) tb
    InL a -> do
      ta <- infer a
      ui <- infer ta
      b <- fresh
      acknowledge (Var (Name b) ui)
      pure (Sum ta (Point b))
    InR b -> do
      tb <- infer b
      ui <- infer tb
      a <- fresh
      acknowledge (Var (Name a) ui)
      pure (Sum (Point a) tb)
    Empty -> pure (U 0)
    Singleton -> pure (U 0)
    Single -> pure Singleton
    Naturals -> pure (U 0)
    Zero -> pure Naturals
    Succ n -> do
      Naturals === infer n
      pure Naturals
    IndN (Var (Name z) tc) c0 (Var (Name x) (Var (Name y) cs)) m -> case m of
      Zero -> do
        localVar (Var (Name z) Naturals) $ typ tc
        tc' <- repoint tc Zero x
        tc' === infer c0
        pure tc'
      Succ n -> do
        localVar (Var (Name z) Naturals) $ typ tc
        tc' <- repoint tc (Succ n) z
        localVar (Var (Name x) Naturals) $ localVar (Var (Name y) tc') do
          cs' <- repoint cs (Succ n) x
          tc' === infer cs'
        pure tc'
      _ -> failure (NotANatural m)
    Equality ta a b -> do
      ta === infer a
      ta === infer b
      U <$> universe ta
    Refl a -> do
      ta <- infer a
      pure (Equality ta a a)
    Path
      ta
      (Var (Name x) (Var (Name y) (Var (Name p) tc)))
      (Var (Name z) c)
      a
      b
      path -> do
        ta === infer a
        ta === infer b
        Equality ta a b === infer path
        tc' <-
          repoint tc (Point z) x
            >>= (\tc_ -> repoint tc_ (Point z) y)
            >>= (\tc__ -> repoint tc__ (Refl (Point z)) p)
        localVar (Var (Name z) ta) $ tc' === infer c
        pure tc'
    FunExt _f _g -> failure Crash
    UA _i _ta _tb -> failure Crash
