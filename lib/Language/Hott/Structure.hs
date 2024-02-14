module Language.Hott.Structure
  ( I (..)
  , E (..)
  , N (..)
  , P (..)
  , M (..)
  , runM
  , typ
  , universe
  , sameUniverse
  , (-->)
  , (**)
  -- , negate
  )
where

import Control.Applicative
import Control.Block
import Control.Monad
import Control.Monad.Except
import Control.Monad.Interpret
import Control.Monad.State
import Data.Bool
import Data.Either
import Data.Eq
import Data.Foldable
import Data.Function
import Data.Int
import Data.Map (Map)
import Data.Map.Strict (insert, (!?))
import Data.Maybe
import Data.Ord
import Data.Semigroup (Semigroup ((<>)))
import Data.Semigroup qualified as Sg
import Data.String
import Data.Text (Text)
import GHC.Enum
import GHC.Show
import Numeric.Natural (Natural)
import Text.Parsec (ParseError)

-- | Identifier
newtype I = I Text deriving newtype (IsString, Eq, Ord, Semigroup, Show)

-- | Error
data E
  = Crash
  | UnknownIdentifier I
  | AlreadyBound I P
  | Unequal P P
  | UniverseMismatch P Natural P Natural
  | NotAType P P
  | NotAFunction P
  | NotASigmaType P
  | NotAPair P
  | NotANatural P
  | NotAConstructor P
  | ArgLengthMismatch P
  | MistypedConstructor P
  | Misparse ParseError
  deriving (Eq, Show)

instance Misparse E where misparse = Misparse

-- | eNvironment
data N = N {gamma :: Map I P, state :: Natural} deriving (Eq, Ord, Show)

-- | Point
data P
  = U Natural
  | --
    Point I
  | --
    Func I P P
  | Lambda I P P
  | Apply P P
  | --
    Sigma I P P
  | Pair P P
  | Proj (Var I P) (Var I P) (Var I (Var I P)) P
  | --
    Sum I [Var I [Var I P]]
  | Ctor I Int I [Var I P] -- expressions
  | Case I I [Either P (Var I P)] -- patterns
  | --
    Naturals
  | Zero
  | Succ P
  | Peano I P P (Var I (Var I P)) P
  | --
    Equality P P P
  | Refl P
  | Path P (Var I (Var I (Var I P))) (Var I P) P P P
  | --
    FunExt P P
  | UA Natural P P
  deriving (Eq, Ord, Show)

-- Monad
newtype M x = M (Interpret I E N P x)
  deriving newtype (Functor, Applicative, Monad, MonadError E, MonadState N)

runM :: M x -> N -> Text -> (Either E x, N)
runM (M t) = runInterpret t

instance MonadInterpret I E N P M where
  fresh go = do
    n <- get
    put (N n.gamma (succ n.state))
    go ("_" <> fromString (show n.state))

  repoint with this = \case
    U u -> pure (U u)
    --
    Point p -> pure if this == p then with else Point p
    --
    Func x ta tb
      | this == x ->
          go =<< fresh \__ -> do
            liftM2 (Func __) (repoint (Point __) x ta) (repoint (Point __) x tb)
      | otherwise -> liftM2 (Func x) (go ta) (go tb)
    Lambda x ta b
      | this == x ->
          go =<< fresh \__ -> do
            liftM2 (Func __) (repoint (Point __) x ta) (repoint (Point __) x b)
      | otherwise -> liftM2 (Lambda x) (go ta) (go b)
    Apply p0 p1 -> liftM2 Apply (go p0) (go p1)
    --
    Sigma x ta tb
      | this == x ->
          go =<< fresh \__ -> do
            liftM2 (Func __) (repoint (Point __) x ta) (repoint (Point __) x tb)
      | otherwise -> liftM2 (Sigma x) (go ta) (go tb)
    Pair a b -> liftM2 Pair (go a) (go b)
    Proj (Var p tp) (Var z tc) (Var x (Var y g)) pair
      | this == p ->
          go =<< fresh \__ -> do
            tp' <- repoint (Point __) p tp
            pure (Proj (Var __ tp') (Var z tc) (Var x (Var y g)) pair)
      | this == z ->
          go =<< fresh \__ -> do
            tc' <- repoint (Point __) z tc
            pure (Proj (Var p tp) (Var __ tc') (Var x (Var y g)) pair)
      | this == x ->
          go =<< fresh \__ -> do
            g' <- repoint (Point __) x g
            pure (Proj (Var p tp) (Var z tc) (Var __ (Var y g')) pair)
      | this == y ->
          go =<< fresh \__ -> do
            g' <- repoint (Point __) y g
            pure (Proj (Var p tp) (Var z tc) (Var x (Var __ g')) pair)
      | otherwise ->
          liftM4
            Proj
            (Var p <$> go tp)
            (Var z <$> go tc)
            (Var x . Var y <$> go g)
            (go pair)
    --
    -- the type name `t` should be unique by construction,
    -- so there should not be any conflicting `I` values
    Sum t ctors
      | this == t ->
          go =<< fresh \__ -> do
            Sum __ <$> for ctors do
              traverse (traverse (traverse (repoint (Point __) t)))
      | otherwise ->
          Sum t <$> for ctors do
            traverse (traverse (traverse go))
    Ctor t ar ctor fields
      | this == t ->
          go =<< fresh \__ -> do
            Ctor __ ar ctor <$> for fields do
              traverse (repoint (Point __) t)
      | this == ctor ->
          go =<< fresh \__ -> do
            Ctor t ar __ <$> for fields do
              traverse go
      | otherwise ->
          Ctor t ar ctor <$> for fields do
            traverse go
    Case t ctor pats
      | this == t ->
          go =<< fresh \__ -> do
            Case __ ctor <$> for pats do
              traverse (traverse (repoint (Point __) t))
      | this == ctor ->
          go =<< fresh \__ -> do
            Case t __ <$> for pats do
              traverse (traverse (repoint (Point __) ctor))
      | otherwise ->
          Case t ctor <$> for pats do
            traverse (traverse go)
    --
    --
    Naturals -> pure Naturals
    Zero -> pure Zero
    Succ m -> pure (Succ m)
    Peano z tc c0 (Var x (Var y c1)) m
      | this == z ->
          go =<< fresh \__ -> do
            tc' <- repoint (Point __) z tc
            pure (Peano __ tc' c0 (Var x (Var y c1)) m)
      | this == x ->
          go =<< fresh \__ -> do
            c1' <- repoint (Point __) x c1
            pure (Peano z tc c0 (Var __ (Var y c1')) m)
      | this == y ->
          go =<< fresh \__ -> do
            c1' <- repoint (Point __) y c1
            pure (Peano z tc c0 (Var x (Var __ c1')) m)
      | otherwise ->
          liftM4 (Peano z) (go tc) (go c0) (Var x . Var y <$> go c1) (go m)
    --
    Equality ta a b -> liftM3 Equality (go ta) (go a) (go b)
    Refl a -> Refl <$> go a
    Path ta (Var x (Var y (Var p tc))) (Var z c) a b path
      | this == x ->
          go =<< fresh \__ -> do
            tc' <- repoint (Point __) x tc
            pure (Path ta (Var __ (Var y (Var p tc'))) (Var z c) a b path)
      | this == y ->
          go =<< fresh \__ -> do
            tc' <- repoint (Point __) y tc
            pure (Path ta (Var x (Var __ (Var p tc'))) (Var z c) a b path)
      | this == p ->
          go =<< fresh \__ -> do
            tc' <- repoint (Point __) x tc
            pure (Path ta (Var x (Var y (Var __ tc'))) (Var z c) a b path)
      | this == z ->
          go =<< fresh \__ -> do
            c' <- repoint (Point __) z c
            pure (Path ta (Var x (Var y (Var p tc))) (Var __ c') a b path)
      | otherwise ->
          liftM6
            Path
            (go ta)
            (Var x . Var y . Var p <$> go tc)
            (Var z <$> go c)
            (go a)
            (go b)
            (go path)
    --
    FunExt f g -> liftM2 FunExt (go f) (go g)
    UA i ta tb -> liftM2 (UA i) (go ta) (go tb)
   where
    go = repoint with this
    liftM6 z ma mb mc md me mf = do
      a <- ma
      b <- mb
      c <- mc
      d <- md
      e <- me
      f <- mf
      pure (z a b c d e f)

  lookup this = get <&> \n -> n.gamma !? this

  acknowledge (Var x tx) = bind (lookup x) \case
    Nothing -> modify \n -> n{gamma = insert x tx n.gamma}
    Just p -> throwError (AlreadyBound x p)

  infer point = case point of
    U u -> pure (U (succ u))
    --
    Point i -> maybe (throwError (UnknownIdentifier i)) pure =<< lookup i
    --
    Func _ ta tb -> U <$> sameUniverse ta tb
    Lambda x ta b -> do
      typ ta
      tb <- localVar (Var x ta) $ infer b
      pure (Func x ta tb)
    Apply (Lambda x ta b) a -> do
      a √ ta
      localVar (Var x ta) $ repoint a x =<< infer b
    Apply f _ -> throwError (NotAFunction f)
    --
    Sigma _ ta tb -> U <$> sameUniverse ta tb
    Pair a b -> do
      ta <- infer a
      fresh \__ -> localVar (Var __ ta) do
        tb <- infer =<< repoint a __ b
        pure (Sigma __ ta tb)
    Proj (Var _ (Sigma q ta tb)) (Var z tc) (Var x (Var y g)) (Pair a b) -> do
      Pair a b √ Sigma q ta tb
      localVar (Var z (Sigma q ta tb)) $ typ tc
      localVar (Var x ta) $ localVar (Var y tb) do
        c' <- repoint (Pair a b) z tc
        g' <- repoint a x g >>= repoint b y
        g' √ c'
        pure c'
    Proj (Var _ (Sigma _ _ _)) _ _ p -> throwError (NotAPair p)
    Proj (Var _ tp) _ _ _ -> throwError (NotASigmaType tp)
    --
    Sum t ctors -> do
      ui <-
        fmap Sg.getMax . fold <$> ifor ctors \ar (Var i fields) -> do
          u <- universe =<< infer (Ctor t ar i fields)
          pure (Just (Sg.Max u))
      u <- maybe (pure 0) universe =<< lookup t
      pure (U (fromMaybe u ui))
    Ctor t ar ctor fields -> do
      when (ar /= length fields) $ throwError (NotAConstructor point)
      bind (lookup ctor) \case
        Nothing -> throwError (UnknownIdentifier ctor)
        Just π -> do
          unless (π == Point t) $ throwError (MistypedConstructor π)
          traverse_ acknowledge fields
          pure (Point t)
    Case t ctor pats -> bind (lookup ctor) \case
      Nothing -> throwError (UnknownIdentifier ctor)
      Just π -> do
        unless (π == Point t) $ throwError (MistypedConstructor π)
        let applied = (=<<) . (compute .) . flip Apply
        p <- reduceR (pure π) pats \case
          Left p -> applied p
          Right (Var _ p) -> applied p
        p √ Point t
        pure (Point t)
    --
    Naturals -> pure (U 0)
    Zero -> pure Naturals
    Succ m -> m √ Naturals >> pure Naturals
    Peano z tc c0 (Var x (Var y c1)) nat -> do
      localVar (Var z Naturals) $ typ tc
      case nat of
        Zero -> do
          tc' <- repoint Zero x tc
          c0 √ tc'
          pure tc'
        Succ m -> do
          tc' <- repoint (Succ m) z tc
          localVar (Var x Naturals) $ localVar (Var y tc') do
            c1' <- repoint (Succ m) x c1
            c1' √ tc'
            pure tc'
        _ -> throwError (NotANatural nat)
    --
    Equality ta a b -> do
      a √ ta
      b √ ta
      U <$> universe ta
    Refl a -> do
      ta <- infer a
      pure (Equality ta a a)
    Path ta (Var x (Var y (Var p tc))) (Var z c) a b path -> do
      a √ ta
      b √ ta
      path √ Equality ta a b
      tc' <-
        repoint (Point z) x tc
          >>= repoint (Point z) y
          >>= repoint (Refl (Point z)) p
      localVar (Var z ta) (c √ tc')
      pure tc'
    --
    FunExt _f _g -> throwError Crash
    UA _i _ta _tb -> throwError Crash

  a √ t = do
    ta <- infer a
    unless (t == ta) (throwError (Unequal t ta))

  compute = \case
    Apply (Lambda x ta b) a -> a √ ta >> repoint a x b
    Apply f _ -> throwError (NotAFunction f)
    --
    Proj (Var _ (Sigma q ta tb)) (Var z tc) (Var x (Var y g)) (Pair a b) -> do
      Pair a b √ Sigma q ta tb
      localVar (Var z (Sigma q ta tb)) $ typ tc
      localVar (Var x ta) $ localVar (Var y tb) do
        c' <- repoint (Pair a b) z tc
        g' <- repoint a x g >>= repoint b y
        g' √ c'
        pure g'
    Proj (Var _ (Sigma _ _ _)) _ _ p -> throwError (NotAPair p)
    Proj (Var _ tp) _ _ _ -> throwError (NotASigmaType tp)
    --
    Peano z tc c0 (Var x (Var y c1)) nat -> do
      localVar (Var z Naturals) $ typ tc
      case nat of
        Zero -> pure c0
        Succ m -> do
          tc' <- repoint (Succ m) z tc
          localVar (Var x Naturals) $ localVar (Var y tc') do
            c1' <- repoint (Succ m) x c1
            c1' √ tc'
            pure c1'
        _ -> throwError (NotANatural nat)
    p -> pure p

typ :: P -> M ()
typ = void . universe

universe :: P -> M Natural
universe point =
  infer point >>= \case
    U u -> pure u
    t -> throwError (NotAType point t)

sameUniverse :: P -> P -> M Natural
sameUniverse p0 p1 = do
  u0 <- universe p0
  u1 <- universe p1
  unless (u0 == u1) (throwError (UniverseMismatch p0 u0 p1 u1))
  pure u0

(-->) :: P -> P -> M P
ta --> tb = sameUniverse ta tb >> fresh \__ -> pure (Func __ ta tb)

(**) :: P -> P -> M P
ta ** tb = sameUniverse ta tb >> fresh \__ -> pure (Sigma __ ta tb)

-- negate :: P -> M P
-- negate tx = typ tx >> fresh \x -> pure (Func x tx Bottom)
