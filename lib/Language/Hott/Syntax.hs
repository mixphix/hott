module Language.Hott.Syntax
  ( InferError (..)
  , MonadInfer (..)
  , InferT (..)
  , Infer
  , InterpretT (..)
  , Interpret
  , runInferT
  , runInterpretT
  , given
  , typ
  , universe
  , sameUniverse
  , (===)
  , (-->)
  , (**)
  , negate
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
import Data.Semigroup (Semigroup ((<>)))
import Data.String
import Data.Text (Text)
import Data.Tuple
import GHC.Enum
import GHC.Show
import Numeric.Natural (Natural)
import Text.Parsec qualified as Parsec

import Language.Hott (Var (Var))
import Language.Hott qualified as Hott (Lbl, Point (..))

data InferError l
  = Crash
  | NotInContext (Label l)
  | AlreadyBound (Label l) l
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

  type Label l :: Type
  fresh :: m (Label l)
  repoint :: l -> l -> Label l -> m l

  type Context l :: Type
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
  default check :: (Eq l) => l -> l -> m ()
  check a t = do
    ta <- infer a
    unless (t == ta) $ failure (Unequal t ta)

given :: (MonadInfer Hott.Point m) => Hott.Lbl -> m (Var Hott.Point)
given name =
  context >>= \ctx -> case ctx !? name of
    Nothing -> failure (NotInContext name)
    Just tx -> pure (Var name tx)

typ :: (MonadInfer Hott.Point m) => Hott.Point -> m ()
typ = void . universe

universe :: (MonadInfer Hott.Point m) => Hott.Point -> m Natural
universe point =
  infer point >>= \case
    Hott.U i -> pure i
    t -> failure (NotAType point t)

sameUniverse ::
  (MonadInfer Hott.Point m) => Var Hott.Point -> Hott.Point -> m Natural
sameUniverse (Var _ p0) p1 = do
  u0 <- universe p0
  u1 <- universe p1
  unless (u0 == u1) $ failure (UniverseMismatch p0 u0 p1 u1)
  pure u0

(===) :: (MonadInfer Hott.Point m) => Hott.Point -> m Hott.Point -> m ()
p0 === run = do
  p1 <- run
  unless (p0 == p1) $ failure (Unequal p0 p1)

(-->) :: (MonadInfer Hott.Point m) => Hott.Point -> Hott.Point -> m Hott.Point
a --> b = do
  ui <- universe a
  ui' <- universe b
  x <- (<>) "_" <$> fresh
  let fun = Hott.Pi (Var x a) b
  unless (ui == ui') $ failure (UniverseMismatch a ui b ui')
  pure fun

(**) :: (MonadInfer Hott.Point m) => Hott.Point -> Hott.Point -> m Hott.Point
a ** b = do
  ui <- universe a
  ui' <- universe b
  x <- (<>) "_" <$> fresh
  let pair = Hott.Sig (Var x a) b
  unless (ui == ui') $ failure (UniverseMismatch a ui b ui')
  pure pair

negate :: (MonadInfer Hott.Point m) => Hott.Point -> m Hott.Point
negate point = do
  typ point
  x <- fresh
  pure (Hott.Pi (Var x point) Hott.Empty)

type InferT :: Type -> (Type -> Type) -> Type -> Type
newtype InferT l m x = Infer
  {getInferT :: ExceptT (InferError l) (State (Map Hott.Lbl l, Natural)) x}
  deriving
    ( Functor
    , Applicative
    , Monad
    , MonadError (InferError l)
    , MonadState (Map Hott.Lbl l, Natural)
    )
type Infer l = InferT l Identity

runInferT ::
  InferT l m x ->
  (Map Hott.Lbl l, Natural) ->
  (Either (InferError l) x, (Map Hott.Lbl l, Natural))
runInferT (Infer i) = runState (runExceptT i)

type InterpretT :: Type -> (Type -> Type) -> Type -> Type
newtype InterpretT l m x = Interpret
  {getInterpretT :: Parsec.ParsecT Text () (InferT l m) x}
  deriving
    ( Functor
    , Applicative
    , Monad
    , MonadError (InferError l)
    , MonadState (Map Hott.Lbl l, Natural)
    )
type Interpret l = InterpretT l Identity

runInterpretT ::
  InterpretT l m x ->
  Text ->
  (Map Hott.Lbl l, Natural) ->
  Either (InferError l) (x, (Map Hott.Lbl l, Natural))
runInterpretT (Interpret p) src init =
  case runInferT (Parsec.runParserT p () "" src) init of
    (Left x, _) -> Left x
    (Right (Left x), _) -> Left (ParseError x)
    (Right (Right x), ctx) -> Right (x, ctx)

instance (Monad m) => MonadInfer Hott.Point (InterpretT Hott.Point m) where
  type Label Hott.Point = Hott.Lbl
  fresh = do
    (ctx, freshness) <- get
    put (ctx, succ freshness)
    pure ("_" <> fromString (show freshness))
  lookup name = gets ((!? name) . fst)
  repoint point with name = case point of
    Hott.U n -> pure (Hott.U n)
    Hott.Point p -> pure if p == name then with else Hott.Point p
    Hott.Pi (Var x ta) tb
      | x == name -> bind fresh \x' -> (>>= go) do
          pure (Hott.Pi . (Var x'))
            `ap` repoint ta (Hott.Point x') x
            `ap` repoint tb (Hott.Point x') x
      | otherwise -> pure (Hott.Pi . Var x) `ap` go ta `ap` go tb
    Hott.Lam (Var x ta) b
      | x == name -> bind fresh \x' -> (>>= go) do
          pure (Hott.Lam . (Var x'))
            `ap` repoint ta (Hott.Point x') x
            `ap` repoint b (Hott.Point x') x
      | otherwise -> pure (Hott.Lam . Var x) `ap` go ta `ap` go b
    Hott.App p0 p1 -> liftM2 Hott.App (go p0) (go p1)
    Hott.Sig (Var x ta) tb
      | x == name -> bind fresh \x' -> (>>= go) do
          pure (Hott.Sig . (Var x'))
            `ap` repoint ta (Hott.Point x') x
            `ap` repoint tb (Hott.Point x') x
      | otherwise -> pure (Hott.Sig . Var x) `ap` go ta `ap` go tb
    Hott.Pair a b -> pure Hott.Pair `ap` go a `ap` go b
    Hott.Proj sig@(Var p tp) c@(Var z tc) proj@(Var x (Var y g)) pair
      | p == name -> bind fresh \p' -> do
          tp' <- repoint tp (Hott.Point p') p
          go (Hott.Proj (Var p' tp') c proj pair)
      | z == name -> bind fresh \z' -> do
          tc' <- repoint tc (Hott.Point z') z
          go (Hott.Proj sig (Var z' tc') proj pair)
      | x == name -> bind fresh \x' -> do
          g' <- repoint g (Hott.Point x') x
          go (Hott.Proj sig c (Var x' (Var y g')) pair)
      | y == name -> bind fresh \y' -> do
          g' <- repoint g (Hott.Point y') y
          go (Hott.Proj sig c (Var x (Var y' g')) pair)
      | otherwise ->
          pure Hott.Proj
            `ap` (Var p <$> go tp)
            `ap` (Var z <$> go tc)
            `ap` (Var x . Var y <$> go g)
            `ap` (go pair)
    Hott.Sum ta tb -> pure Hott.Sum `ap` go ta `ap` go tb
    Hott.InL a -> Hott.InL <$> go a
    Hott.InR b -> Hott.InR <$> go b
    Hott.Empty -> pure Hott.Empty
    Hott.Singleton -> pure Hott.Singleton
    Hott.Single -> pure Hott.Single
    Hott.Naturals -> pure Hott.Naturals
    Hott.Zero -> pure Hott.Zero
    Hott.Succ n -> pure (Hott.Succ n)
    Hott.IndN (Var z tc) c0 cs@(Var x (Var y c1)) n
      | z == name -> bind fresh \z' -> do
          tc' <- repoint tc (Hott.Point z') z
          go (Hott.IndN (Var z' tc') c0 cs n)
      | x == name -> bind fresh \x' -> do
          c1' <- repoint c1 (Hott.Point x') x
          go (Hott.IndN (Var z tc) c0 (Var x' (Var y c1')) n)
      | y == name -> bind fresh \y' -> do
          c1' <- repoint c1 (Hott.Point y') y
          go (Hott.IndN (Var z tc) c0 (Var x (Var y' c1')) n)
      | otherwise ->
          pure Hott.IndN
            `ap` (Var z <$> go tc)
            `ap` (go c0)
            `ap` (Var x . Var y <$> go c1)
            `ap` (go n)
    Hott.Equality ta a b ->
      Hott.Equality <$> go ta <*> go a <*> go b
    Hott.Refl a -> Hott.Refl <$> go a
    Hott.Path ta (Var x (Var y (Var p tc))) (Var z c) a b path
      | x == name -> bind fresh \x' -> do
          tc' <- repoint tc (Hott.Point x') x
          go (Hott.Path ta (Var x' (Var y (Var p tc'))) (Var z c) a b path)
      | y == name -> bind fresh \y' -> do
          tc' <- repoint tc (Hott.Point y') y
          go (Hott.Path ta (Var x (Var y' (Var p tc'))) (Var z c) a b path)
      | p == name -> bind fresh \p' -> do
          tc' <- repoint tc (Hott.Point p') x
          go (Hott.Path ta (Var x (Var y (Var p' tc'))) (Var z c) a b path)
      | z == name -> bind fresh \z' -> do
          c' <- repoint c (Hott.Point z') z
          go (Hott.Path ta (Var x (Var y (Var p tc))) (Var z' c') a b path)
      | otherwise ->
          pure Hott.Path
            `ap` (go ta)
            `ap` (Var x . Var y . Var p <$> go tc)
            `ap` (Var z <$> go c)
            `ap` (go a)
            `ap` (go b)
            `ap` (go path)
    Hott.FunExt f g -> Hott.FunExt <$> go f <*> go g
    Hott.UA i ta tb -> Hott.UA i <$> go ta <*> go tb
   where
    go x = go x
    bind = (>>=)

  type Context Hott.Point = Map Hott.Lbl Hott.Point
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
    Hott.U n -> pure (Hott.U (succ n))
    Hott.Point x -> do
      Var _ tx <- given x
      pure tx
    Hott.Pi (Var x ta) tb -> Hott.U <$> sameUniverse (Var x ta) tb
    Hott.Lam (Var x ta) b -> do
      typ ta
      tb <- localVar (Var x ta) $ infer b
      pure (Hott.Pi (Var x ta) tb)
    Hott.App (Hott.Pi (Var x ta) tb) a -> do
      ta === infer a
      typ tb
      repoint tb a x
    Hott.App f _ -> failure (NotAFunction f)
    Hott.Sig (Var x ta) tb -> Hott.U <$> sameUniverse (Var x ta) tb
    Hott.Pair a b -> do
      ta <- infer a
      x <- fresh
      tb <- localVar (Var x ta) do
        infer =<< repoint b a x
      pure (Hott.Sig (Var x ta) tb)
    Hott.Proj
      (Var _ tp@(Hott.Sig (Var _ ta) tb))
      (Var z tc)
      (Var x (Var y g))
      p@(Hott.Pair a b) -> do
        tp === infer p
        localVar (Var z tp) $ typ tc
        localVar (Var x ta) $ localVar (Var y tb) do
          c' <- repoint tc p z
          g' <- repoint g a x >>= \g_ -> repoint g_ b y
          c' === infer g'
          pure c'
    Hott.Proj (Var _ (Hott.Sig _ _)) _ _ p -> failure (NotAPair p)
    Hott.Proj (Var _ tp) _ _ _ -> failure (NotAPair tp)
    Hott.Sum ta tb -> Hott.U <$> sameUniverse (Var "" ta) tb
    Hott.InL a -> do
      ta <- infer a
      ui <- infer ta
      b <- fresh
      acknowledge (Var b ui)
      pure (Hott.Sum ta (Hott.Point b))
    Hott.InR b -> do
      tb <- infer b
      ui <- infer tb
      a <- fresh
      acknowledge (Var a ui)
      pure (Hott.Sum (Hott.Point a) tb)
    Hott.Empty -> pure (Hott.U 0)
    Hott.Singleton -> pure (Hott.U 0)
    Hott.Single -> pure Hott.Singleton
    Hott.Naturals -> pure (Hott.U 0)
    Hott.Zero -> pure Hott.Naturals
    Hott.Succ n -> do
      Hott.Naturals === infer n
      pure Hott.Naturals
    Hott.IndN (Var z tc) c0 (Var x (Var y cs)) m -> case m of
      Hott.Zero -> do
        localVar (Var z Hott.Naturals) $ typ tc
        tc' <- repoint tc Hott.Zero x
        tc' === infer c0
        pure tc'
      Hott.Succ n -> do
        localVar (Var z Hott.Naturals) $ typ tc
        tc' <- repoint tc (Hott.Succ n) z
        localVar (Var x Hott.Naturals) $ localVar (Var y tc') do
          cs' <- repoint cs (Hott.Succ n) x
          tc' === infer cs'
        pure tc'
      _ -> failure (NotANatural m)
    Hott.Equality ta a b -> do
      ta === infer a
      ta === infer b
      Hott.U <$> universe ta
    Hott.Refl a -> do
      ta <- infer a
      pure (Hott.Equality ta a a)
    Hott.Path ta (Var x (Var y (Var p tc))) (Var z c) a b path -> do
      ta === infer a
      ta === infer b
      Hott.Equality ta a b === infer path
      tc' <- do
        tc1 <- repoint tc (Hott.Point z) x
        tc2 <- repoint tc1 (Hott.Point z) y
        repoint tc2 (Hott.Refl (Hott.Point z)) p
      localVar (Var z ta) $ tc' === infer c
      pure tc'
    Hott.FunExt _f _g -> failure Crash
    Hott.UA _i _ta _tb -> failure Crash
