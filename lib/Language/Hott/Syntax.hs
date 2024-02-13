module Language.Hott.Syntax
  ( Lbl (..)
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
import Data.Semigroup (Semigroup ((<>)))
import Data.String
import Data.Text (Text)
import Data.Tuple
import GHC.Enum
import GHC.Show
import Numeric.Natural (Natural)
import Text.Parsec qualified as Parsec

import Language.Hott

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

given :: (MonadInfer Point m) => Lbl -> m (Var Point)
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
  let fun = Pi (Var x a) b
  unless (ui == ui') $ failure (UniverseMismatch a ui b ui')
  pure fun

(**) :: (MonadInfer Point m) => Point -> Point -> m Point
a ** b = do
  ui <- universe a
  ui' <- universe b
  x <- (<>) "_" <$> fresh
  let pair = Sig (Var x a) b
  unless (ui == ui') $ failure (UniverseMismatch a ui b ui')
  pure pair

negate :: (MonadInfer Point m) => Point -> m Point
negate point = do
  typ point
  x <- fresh
  pure (Pi (Var x point) Empty)

type InferT :: Type -> (Type -> Type) -> Type -> Type
newtype InferT l m x = Infer
  {getInferT :: ExceptT (InferError l) (State (Map Lbl l, Natural)) x}
  deriving
    ( Functor
    , Applicative
    , Monad
    , MonadError (InferError l)
    , MonadState (Map Lbl l, Natural)
    )
type Infer l = InferT l Identity

runInferT ::
  InferT l m x ->
  (Map Lbl l, Natural) ->
  (Either (InferError l) x, (Map Lbl l, Natural))
runInferT (Infer i) = runState (runExceptT i)

type InterpretT :: Type -> (Type -> Type) -> Type -> Type
newtype InterpretT l m x = Interpret
  {getInterpretT :: Parsec.ParsecT Text () (InferT l m) x}
  deriving
    ( Functor
    , Applicative
    , Monad
    , MonadError (InferError l)
    , MonadState (Map Lbl l, Natural)
    )
type Interpret l = InterpretT l Identity

runInterpretT ::
  InterpretT l m x ->
  Text ->
  (Map Lbl l, Natural) ->
  Either (InferError l) (x, (Map Lbl l, Natural))
runInterpretT (Interpret p) src init =
  case runInferT (Parsec.runParserT p () "" src) init of
    (Left x, _) -> Left x
    (Right (Left x), _) -> Left (ParseError x)
    (Right (Right x), ctx) -> Right (x, ctx)

instance (Monad m) => MonadInfer Point (InterpretT Point m) where
  type Label Point = Lbl
  fresh = do
    (ctx, freshness) <- get
    put (ctx, succ freshness)
    pure ("_" <> fromString (show freshness))
  lookup name = gets ((!? name) . fst)
  repoint point with name = case point of
    U n -> pure (U n)
    Point p -> pure if p == name then with else Point p
    Pi (Var x ta) tb
      | x == name -> bind fresh \x' -> (>>= go) do
          pure (Pi . (Var x'))
            `ap` repoint ta (Point x') x
            `ap` repoint tb (Point x') x
      | otherwise -> pure (Pi . Var x) `ap` go ta `ap` go tb
    Lam (Var x ta) b
      | x == name -> bind fresh \x' -> (>>= go) do
          pure (Lam . (Var x'))
            `ap` repoint ta (Point x') x
            `ap` repoint b (Point x') x
      | otherwise -> pure (Lam . Var x) `ap` go ta `ap` go b
    App p0 p1 -> liftM2 App (go p0) (go p1)
    Sig (Var x ta) tb
      | x == name -> bind fresh \x' -> (>>= go) do
          pure (Sig . (Var x'))
            `ap` repoint ta (Point x') x
            `ap` repoint tb (Point x') x
      | otherwise -> pure (Sig . Var x) `ap` go ta `ap` go tb
    Pair a b -> liftM2 Pair (go a) (go b)
    Proj sig@(Var p tp) c@(Var z tc) proj@(Var x (Var y g)) pair
      | p == name -> bind fresh \p' -> do
          tp' <- repoint tp (Point p') p
          go (Proj (Var p' tp') c proj pair)
      | z == name -> bind fresh \z' -> do
          tc' <- repoint tc (Point z') z
          go (Proj sig (Var z' tc') proj pair)
      | x == name -> bind fresh \x' -> do
          g' <- repoint g (Point x') x
          go (Proj sig c (Var x' (Var y g')) pair)
      | y == name -> bind fresh \y' -> do
          g' <- repoint g (Point y') y
          go (Proj sig c (Var x (Var y' g')) pair)
      | otherwise ->
          pure Proj
            `ap` (Var p <$> go tp)
            `ap` (Var z <$> go tc)
            `ap` (Var x . Var y <$> go g)
            `ap` (go pair)
    Sum ta tb -> Sum <$> go ta <*> go tb
    InL a -> InL <$> go a
    InR b -> InL <$> go b
    Empty -> pure Empty
    Singleton -> pure Singleton
    Single -> pure Single
    Naturals -> pure Naturals
    Zero -> pure Zero
    Succ n -> pure (Succ n)
    IndN (Var z tc) c0 cs@(Var x (Var y c1)) n
      | z == name -> bind fresh \z' -> do
          tc' <- repoint tc (Point z') z
          go (IndN (Var z' tc') c0 cs n)
      | x == name -> bind fresh \x' -> do
          c1' <- repoint c1 (Point x') x
          go (IndN (Var z tc) c0 (Var x' (Var y c1')) n)
      | y == name -> bind fresh \y' -> do
          c1' <- repoint c1 (Point y') y
          go (IndN (Var z tc) c0 (Var x (Var y' c1')) n)
      | otherwise ->
          pure IndN
            `ap` (Var z <$> go tc)
            `ap` (go c0)
            `ap` (Var x . Var y <$> go c1)
            `ap` (go n)
    Equality ta a b ->
      Equality <$> go ta <*> go a <*> go b
    Refl a -> Refl <$> go a
    Path ta (Var x (Var y (Var p tc))) (Var z c) a b path
      | x == name -> bind fresh \x' -> do
          tc' <- repoint tc (Point x') x
          go (Path ta (Var x' (Var y (Var p tc'))) (Var z c) a b path)
      | y == name -> bind fresh \y' -> do
          tc' <- repoint tc (Point y') y
          go (Path ta (Var x (Var y' (Var p tc'))) (Var z c) a b path)
      | p == name -> bind fresh \p' -> do
          tc' <- repoint tc (Point p') x
          go (Path ta (Var x (Var y (Var p' tc'))) (Var z c) a b path)
      | z == name -> bind fresh \z' -> do
          c' <- repoint c (Point z') z
          go (Path ta (Var x (Var y (Var p tc))) (Var z' c') a b path)
      | otherwise ->
          pure Path
            `ap` (go ta)
            `ap` (Var x . Var y . Var p <$> go tc)
            `ap` (Var z <$> go c)
            `ap` (go a)
            `ap` (go b)
            `ap` (go path)
    FunExt f g -> FunExt <$> go f <*> go g
    UA i ta tb -> UA i <$> go ta <*> go tb
   where
    go x = go x
    bind = (>>=)

  type Context Point = Map Lbl Point
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
      Var _ tx <- given x
      pure tx
    Pi (Var x ta) tb -> U <$> sameUniverse (Var x ta) tb
    Lam (Var x ta) b -> do
      typ ta
      tb <- localVar (Var x ta) $ infer b
      pure (Pi (Var x ta) tb)
    App (Pi (Var x ta) tb) a -> do
      ta === infer a
      typ tb
      repoint tb a x
    App f _ -> failure (NotAFunction f)
    Sig (Var x ta) tb -> U <$> sameUniverse (Var x ta) tb
    Pair a b -> do
      ta <- infer a
      x <- fresh
      tb <- localVar (Var x ta) do
        infer =<< repoint b a x
      pure (Sig (Var x ta) tb)
    Proj
      (Var _ tp@(Sig (Var _ ta) tb))
      (Var z tc)
      (Var x (Var y g))
      p@(Pair a b) -> do
        tp === infer p
        localVar (Var z tp) $ typ tc
        localVar (Var x ta) $ localVar (Var y tb) do
          c' <- repoint tc p z
          g' <- repoint g a x >>= \g_ -> repoint g_ b y
          c' === infer g'
          pure c'
    Proj (Var _ (Sig _ _)) _ _ p -> failure (NotAPair p)
    Proj (Var _ tp) _ _ _ -> failure (NotAPair tp)
    Sum ta tb -> U <$> sameUniverse (Var "" ta) tb
    InL a -> do
      ta <- infer a
      ui <- infer ta
      b <- fresh
      acknowledge (Var b ui)
      pure (Sum ta (Point b))
    InR b -> do
      tb <- infer b
      ui <- infer tb
      a <- fresh
      acknowledge (Var a ui)
      pure (Sum (Point a) tb)
    Empty -> pure (U 0)
    Singleton -> pure (U 0)
    Single -> pure Singleton
    Naturals -> pure (U 0)
    Zero -> pure Naturals
    Succ n -> do
      Naturals === infer n
      pure Naturals
    IndN (Var z tc) c0 (Var x (Var y cs)) m -> case m of
      Zero -> do
        localVar (Var z Naturals) $ typ tc
        tc' <- repoint tc Zero x
        tc' === infer c0
        pure tc'
      Succ n -> do
        localVar (Var z Naturals) $ typ tc
        tc' <- repoint tc (Succ n) z
        localVar (Var x Naturals) $ localVar (Var y tc') do
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
    Path ta (Var x (Var y (Var p tc))) (Var z c) a b path -> do
      ta === infer a
      ta === infer b
      Equality ta a b === infer path
      tc' <- do
        tc1 <- repoint tc (Point z) x
        tc2 <- repoint tc1 (Point z) y
        repoint tc2 (Refl (Point z)) p
      localVar (Var z ta) $ tc' === infer c
      pure tc'
    FunExt _f _g -> failure Crash
    UA _i _ta _tb -> failure Crash
