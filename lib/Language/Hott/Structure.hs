module Language.Hott.Structure
  ( I (..)
  , E (..)
  , N (..)
  , P (..)
  , M (..)
  , runM
  , given
  , typ
  , universe
  , sameUniverse
  , (===)
  , (-->)
  , (**)
  , negate
  )
where

import Control.Applicative
import Control.Monad
import Control.Monad.Except
import Control.Monad.Interpret
import Control.Monad.State
import Data.Bool
import Data.Either
import Data.Eq
import Data.Function
import Data.Functor
import Data.Functor.Identity
import Data.Map (Map)
import Data.Map.Strict (insert, (!?))
import Data.Maybe
import Data.Ord
import Data.Semigroup (Semigroup ((<>)))
import Data.String
import Data.Text (Text)
import GHC.Enum
import GHC.Show
import Numeric.Natural (Natural)
import Text.Parsec (ParseError, ParsecT)

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
  | NotAPiType P
  | NotASigmaType P
  | NotAPair P
  | NotANatural P
  | Misparse ParseError
  deriving (Eq, Show)

instance Misparse E where misparse = Misparse

-- | eNvironment
data N = N {gamma :: Map I P, state :: Natural} deriving (Eq, Ord, Show)

-- | Point
data P
  = U Natural
  | Point I
  | Pi (Var I P) P
  | Lambda (Var I P) P
  | Apply P P
  | Sigma (Var I P) P
  | Pair P P
  | Proj (Var I P) (Var I P) (Var I (Var I P)) P
  | Sum P P
  | InL P
  | InR P
  | Empty
  | Singleton
  | Single
  | Naturals
  | Zero
  | Succ P
  | IndN (Var I P) P (Var I (Var I P)) P
  | Equality P P P
  | Refl P
  | Path P (Var I (Var I (Var I P))) (Var I P) P P P
  | FunExt P P
  | UA Natural P P
  deriving (Eq, Ord, Show)

-- Monad
newtype M x = M (ParsecT Text () (ExceptT E (StateT N Identity)) x)
  deriving newtype
    (Functor, Applicative, Monad, MonadError E, MonadState N)

runM :: M x -> N -> Text -> (Either E x, N)
runM (M t) = runInterpret t

instance MonadInterpret I E N P M where
  fresh = do
    n <- get
    put (N n.gamma (succ n.state))
    pure $ "_" <> fromString (show n.state)
  repoint point with this = case point of
    U u -> pure (U u)
    Point p -> pure if p == this then with else Point p
    Pi (Var x ta) tb
      | x == this -> goWith \x' -> do
          pure (Pi . (Var x'))
            `ap` repoint ta (Point x') x
            `ap` repoint tb (Point x') x
      | otherwise ->
          pure (Pi . Var x)
            `ap` go ta
            `ap` go tb
    Lambda (Var x ta) b
      | x == this -> goWith \x' -> do
          pure (Lambda . (Var x'))
            `ap` repoint ta (Point x') x
            `ap` repoint b (Point x') x
      | otherwise ->
          pure (Lambda . Var x)
            `ap` go ta
            `ap` go b
    Apply p0 p1 ->
      pure Apply
        `ap` go p0
        `ap` go p1
    Sigma (Var x ta) tb
      | x == this -> goWith \x' -> do
          pure (Sigma . (Var x'))
            `ap` repoint ta (Point x') x
            `ap` repoint tb (Point x') x
      | otherwise ->
          pure (Sigma . Var x)
            `ap` go ta
            `ap` go tb
    Pair a b ->
      pure Pair
        `ap` go a
        `ap` go b
    Proj sig@(Var p tp) c@(Var z tc) proj@(Var x (Var y g)) pair
      | p == this -> goWith \p' -> do
          tp' <- repoint tp (Point p') p
          pure $ Proj (Var p' tp') c proj pair
      | z == this -> goWith \z' -> do
          tc' <- repoint tc (Point z') z
          pure $ Proj sig (Var z' tc') proj pair
      | x == this -> goWith \x' -> do
          g' <- repoint g (Point x') x
          pure $ Proj sig c (Var x' (Var y g')) pair
      | y == this -> goWith \y' -> do
          g' <- repoint g (Point y') y
          pure $ Proj sig c (Var x (Var y' g')) pair
      | otherwise ->
          pure Proj
            `ap` (Var p <$> go tp)
            `ap` (Var z <$> go tc)
            `ap` (Var x . Var y <$> go g)
            `ap` go pair
    Sum ta tb ->
      pure Sum
        `ap` go ta
        `ap` go tb
    InL a -> InL <$> go a
    InR b -> InR <$> go b
    Empty -> pure Empty
    Singleton -> pure Singleton
    Single -> pure Single
    Naturals -> pure Naturals
    Zero -> pure Zero
    Succ m -> pure (Succ m)
    IndN (Var z tc) c0 cs@(Var x (Var y c1)) m
      | z == this -> goWith \z' -> do
          tc' <- repoint tc (Point z') z
          pure $ IndN (Var z' tc') c0 cs m
      | x == this -> goWith \x' -> do
          c1' <- repoint c1 (Point x') x
          pure $ IndN (Var z tc) c0 (Var x' (Var y c1')) m
      | y == this -> goWith \y' -> do
          c1' <- repoint c1 (Point y') y
          pure $ IndN (Var z tc) c0 (Var x (Var y' c1')) m
      | otherwise ->
          pure IndN
            `ap` (Var z <$> go tc)
            `ap` go c0
            `ap` (Var x . Var y <$> go c1)
            `ap` go m
    Equality ta a b ->
      pure Equality
        `ap` go ta
        `ap` go a
        `ap` go b
    Refl a -> Refl <$> go a
    Path ta (Var x (Var y (Var p tc))) (Var z c) a b path
      | x == this -> goWith \x' -> do
          tc' <- repoint tc (Point x') x
          pure $ Path ta (Var x' (Var y (Var p tc'))) (Var z c) a b path
      | y == this -> goWith \y' -> do
          tc' <- repoint tc (Point y') y
          pure $ Path ta (Var x (Var y' (Var p tc'))) (Var z c) a b path
      | p == this -> goWith \p' -> do
          tc' <- repoint tc (Point p') x
          pure $ Path ta (Var x (Var y (Var p' tc'))) (Var z c) a b path
      | z == this -> goWith \z' -> do
          c' <- repoint c (Point z') z
          pure $ Path ta (Var x (Var y (Var p tc))) (Var z' c') a b path
      | otherwise ->
          pure Path
            `ap` go ta
            `ap` (Var x . Var y . Var p <$> go tc)
            `ap` (Var z <$> go c)
            `ap` go a
            `ap` go b
            `ap` go path
    FunExt f g ->
      pure FunExt
        `ap` go f
        `ap` go g
    UA i ta tb ->
      pure (UA i)
        `ap` go ta
        `ap` go tb
   where
    go :: P -> M P
    go x = repoint x with this

    goWith :: (I -> M P) -> M P
    goWith = (fresh >>=) . (go <=<)

  acknowledge (Var x tx) = do
    c <- get
    case c.gamma !? x of
      Nothing -> put (N (insert x tx c.gamma) c.state)
      Just p -> throwError $ AlreadyBound x p
  lookup this = get <&> \n -> n.gamma !? this

  infer point = case point of
    U u -> pure $ U (succ u)
    Point x -> do
      Var _ tx <- given x
      pure tx
    Pi (Var x ta) tb -> U <$> sameUniverse (Var x ta) tb
    Lambda (Var x ta) b -> do
      typ ta
      tb <- localVar (Var x ta) $ infer b
      pure $ Pi (Var x ta) tb
    Apply (Pi (Var x ta) tb) a -> do
      ta === infer a
      typ tb
      repoint tb a x
    Apply f _ -> throwError $ NotAPiType f
    Sigma (Var x ta) tb -> U <$> sameUniverse (Var x ta) tb
    Pair a b -> do
      ta <- infer a
      x <- fresh
      tb <- localVar (Var x ta) do
        infer =<< repoint b a x
      pure $ Sigma (Var x ta) tb
    Proj
      (Var _ tp@(Sigma (Var _ ta) tb))
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
    Proj (Var _ (Sigma _ _)) _ _ p ->
      throwError $ NotASigmaType p
    Proj (Var _ tp) _ _ _ -> throwError $ NotAPair tp
    Sum ta tb -> U <$> sameUniverse (Var "" ta) tb
    InL a -> do
      ta <- infer a
      ui <- infer ta
      b <- fresh
      acknowledge (Var b ui)
      pure $ Sum ta (Point b)
    InR b -> do
      tb <- infer b
      ui <- infer tb
      a <- fresh
      acknowledge (Var a ui)
      pure $ Sum (Point a) tb
    Empty -> pure (U 0)
    Singleton -> pure (U 0)
    Single -> pure Singleton
    Naturals -> pure (U 0)
    Zero -> pure Naturals
    Succ m -> do
      Naturals === infer m
      pure Naturals
    IndN (Var z tc) c0 (Var x (Var y cs)) mm -> case mm of
      Zero -> do
        localVar (Var z Naturals) $ typ tc
        tc' <- repoint tc Zero x
        tc' === infer c0
        pure tc'
      Succ m -> do
        localVar (Var z Naturals) $ typ tc
        tc' <- repoint tc (Succ m) z
        localVar (Var x Naturals) $ localVar (Var y tc') do
          cs' <- repoint cs (Succ m) x
          tc' === infer cs'
        pure tc'
      _ -> throwError $ NotANatural mm
    Equality ta a b -> do
      ta === infer a
      ta === infer b
      U <$> universe ta
    Refl a -> do
      ta <- infer a
      pure $ Equality ta a a
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
    FunExt _f _g -> throwError Crash
    UA _i _ta _tb -> throwError Crash
  check a t = do
    ta <- infer a
    unless (t == ta) do
      throwError $ Unequal t ta

given :: I -> M (Var I P)
given i =
  lookup i >>= \case
    Nothing -> throwError $ UnknownIdentifier i
    Just tx -> pure $ Var i tx

typ :: P -> M ()
typ = void . universe

universe :: P -> M Natural
universe point =
  infer point >>= \case
    U u -> pure u
    t -> throwError $ NotAType point t

sameUniverse :: Var I P -> P -> M Natural
sameUniverse (Var _ p0) p1 = do
  u0 <- universe p0
  u1 <- universe p1
  unless (u0 == u1) do
    throwError $ UniverseMismatch p0 u0 p1 u1
  pure u0

(===) :: P -> M P -> M ()
p0 === run = do
  p1 <- run
  unless (p0 == p1) do
    throwError $ Unequal p0 p1

(-->) :: P -> P -> M P
a --> b = do
  ui <- universe a
  ui' <- universe b
  x <- (<>) "_" <$> fresh
  let fun = Pi (Var x a) b
  unless (ui == ui') do
    throwError $ UniverseMismatch a ui b ui'
  pure fun

(**) :: P -> P -> M P
a ** b = do
  ui <- universe a
  ui' <- universe b
  x <- (<>) "_" <$> fresh
  let pair = Sigma (Var x a) b
  unless (ui == ui') do
    throwError $ UniverseMismatch a ui b ui'
  pure pair

negate :: P -> M P
negate point = do
  typ point
  x <- fresh
  pure $ Pi (Var x point) Empty
