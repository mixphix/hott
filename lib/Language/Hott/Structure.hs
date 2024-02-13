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
  | Pi I P P
  | Lambda I P P
  | Apply P P
  | Sigma I P P
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
  | Peano I P P (Var I (Var I P)) P
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
  fresh go = do
    n <- get
    put (N n.gamma (succ n.state))
    go $ "_" <> fromString (show n.state)
  repoint point with this = case point of
    U u -> pure (U u)
    Point p -> pure if p == this then with else Point p
    Pi x ta tb
      | x == this -> fresh \ø -> do
          ta' <- repoint ta (Point ø) x
          tb' <- repoint tb (Point ø) x
          go (Pi ø ta' tb')
      | otherwise -> liftM2 (Pi x) (go ta) (go tb)
    Lambda x ta b
      | x == this -> fresh \ø -> do
          ta' <- repoint ta (Point ø) x
          b' <- repoint b (Point ø) x
          go (Lambda ø ta' b')
      | otherwise -> liftM2 (Lambda x) (go ta) (go b)
    Apply p0 p1 -> liftM2 Apply (go p0) (go p1)
    Sigma x ta tb
      | x == this -> fresh \ø -> do
          ta' <- repoint ta (Point ø) x
          tb' <- repoint tb (Point ø) x
          go (Pi ø ta' tb')
      | otherwise -> liftM2 (Sigma x) (go ta) (go tb)
    Pair a b -> liftM2 Pair (go a) (go b)
    Proj sig@(Var p tp) c@(Var z tc) proj@(Var x (Var y g)) pair
      | p == this -> fresh \ø -> do
          to <- repoint tp (Point ø) p
          go $ Proj (Var ø to) c proj pair
      | z == this -> fresh \ø -> do
          tc' <- repoint tc (Point ø) z
          go $ Proj sig (Var ø tc') proj pair
      | x == this -> fresh \ø -> do
          g' <- repoint g (Point ø) x
          go $ Proj sig c (Var ø (Var y g')) pair
      | y == this -> fresh \ø -> do
          g' <- repoint g (Point ø) y
          go $ Proj sig c (Var x (Var ø g')) pair
      | otherwise ->
          liftM4
            Proj
            (Var p <$> go tp)
            (Var z <$> go tc)
            (Var x . Var y <$> go g)
            (go pair)
    Sum ta tb -> liftM2 Sum (go ta) (go tb)
    InL a -> InL <$> go a
    InR b -> InR <$> go b
    Empty -> pure Empty
    Singleton -> pure Singleton
    Single -> pure Single
    Naturals -> pure Naturals
    Zero -> pure Zero
    Succ m -> pure (Succ m)
    Peano z tc c0 cs@(Var x (Var y c1)) m
      | z == this -> fresh \ø -> do
          tc' <- repoint tc (Point ø) z
          go $ Peano ø tc' c0 cs m
      | x == this -> fresh \ø -> do
          c1' <- repoint c1 (Point ø) x
          go $ Peano z tc c0 (Var ø (Var y c1')) m
      | y == this -> fresh \ø -> do
          c1' <- repoint c1 (Point ø) y
          go $ Peano z tc c0 (Var x (Var ø c1')) m
      | otherwise ->
          liftM4
            (Peano z)
            (go tc)
            (go c0)
            (Var x . Var y <$> go c1)
            (go m)
    Equality ta a b -> liftM3 Equality (go ta) (go a) (go b)
    Refl a -> Refl <$> go a
    Path ta (Var x (Var y (Var p tc))) (Var z c) a b path
      | x == this -> fresh \ø -> do
          tc' <- repoint tc (Point ø) x
          go $ Path ta (Var ø (Var y (Var p tc'))) (Var z c) a b path
      | y == this -> fresh \ø -> do
          tc' <- repoint tc (Point ø) y
          go $ Path ta (Var x (Var ø (Var p tc'))) (Var z c) a b path
      | p == this -> fresh \ø -> do
          tc' <- repoint tc (Point ø) x
          go $ Path ta (Var x (Var y (Var ø tc'))) (Var z c) a b path
      | z == this -> fresh \ø -> do
          c' <- repoint c (Point ø) z
          go $ Path ta (Var x (Var y (Var p tc))) (Var ø c') a b path
      | otherwise ->
          liftM6
            Path
            (go ta)
            (Var x . Var y . Var p <$> go tc)
            (Var z <$> go c)
            (go a)
            (go b)
            (go path)
    FunExt f g -> liftM2 FunExt (go f) (go g)
    UA i ta tb -> liftM2 (UA i) (go ta) (go tb)
   where
    go :: P -> M P
    go x = repoint x with this
    liftM6 z ma mb mc md me mf = do
      a <- ma
      b <- mb
      c <- mc
      d <- md
      e <- me
      f <- mf
      pure (z a b c d e f)
  lookup this = get <&> \n -> n.gamma !? this
  acknowledge (Var x tx) = (>>=) (lookup x) \case
    Nothing -> modify \n -> n{gamma = insert x tx n.gamma}
    Just p -> throwError $ AlreadyBound x p

  infer point = case point of
    U u -> pure $ U (succ u)
    Point i -> maybe (throwError $ UnknownIdentifier i) pure =<< lookup i
    Pi x ta tb -> U <$> sameUniverse (Var x ta) tb
    Lambda x ta b -> do
      typ ta
      tb <- localVar (Var x ta) $ infer b
      pure $ Pi x ta tb
    Apply (Pi x ta tb) a -> do
      check a ta 
      typ tb
      repoint tb a x
    Apply f _ -> throwError $ NotAPiType f
    Sigma x ta tb -> U <$> sameUniverse (Var x ta) tb
    Pair a b -> do
      ta <- infer a
      fresh \ø -> do
        tb <- localVar (Var ø ta) $ infer =<< repoint b a ø
        pure $ Sigma ø ta tb
    Proj (Var _ p@(Sigma _ ta tb)) (Var z tc) (Var x (Var y g)) (Pair a b) -> do
      check (Pair a b) p 
      localVar (Var z p) $ typ tc
      localVar (Var x ta) $ localVar (Var y tb) do
        c' <- repoint tc (Pair a b) z
        g' <- repoint g a x >>= \g_ -> repoint g_ b y
        check g' c' 
        pure c'
    Proj (Var _ (Sigma _ _ _)) _ _ p -> throwError $ NotASigmaType p
    Proj (Var _ tp) _ _ _ -> throwError $ NotAPair tp
    Sum ta tb -> U <$> sameUniverse (Var "" ta) tb
    InL a -> do
      ta <- infer a
      ui <- infer ta
      fresh \ø -> do
        acknowledge (Var ø ui)
        pure $ Sum ta (Point ø)
    InR b -> do
      tb <- infer b
      ui <- infer tb
      fresh \ø -> do
        acknowledge (Var ø ui)
        pure $ Sum (Point ø) tb
    Empty -> pure (U 0)
    Singleton -> pure (U 0)
    Single -> pure Singleton
    Naturals -> pure (U 0)
    Zero -> pure Naturals
    Succ m -> check m Naturals >> pure Naturals
    Peano z tc c0 (Var x (Var y cs)) nat -> case nat of
      Zero -> do
        localVar (Var z Naturals) $ typ tc
        tc' <- repoint tc Zero x
        check c0 tc'
        pure tc'
      Succ m -> do
        localVar (Var z Naturals) $ typ tc
        tc' <- repoint tc (Succ m) z
        localVar (Var x Naturals) $ localVar (Var y tc') do
          cs' <- repoint cs (Succ m) x
          check cs' tc'
        pure tc'
      _ -> throwError $ NotANatural nat
    Equality ta a b -> do
      check a ta 
      check b ta 
      U <$> universe ta
    Refl a -> do
      ta <- infer a
      pure $ Equality ta a a
    Path ta (Var x (Var y (Var p tc))) (Var z c) a b path -> do
      check a ta 
      check b ta 
      check path (Equality ta a b)
      tc' <- do
        tc1 <- repoint tc (Point z) x
        tc2 <- repoint tc1 (Point z) y
        repoint tc2 (Refl (Point z)) p
      localVar (Var z ta) $ check c tc'
      pure tc'
    FunExt _f _g -> throwError Crash
    UA _i _ta _tb -> throwError Crash
  check a t = do
    ta <- infer a
    unless (t == ta) (throwError $ Unequal t ta)

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
  unless (u0 == u1) (throwError $ UniverseMismatch p0 u0 p1 u1)
  pure u0

(-->) :: P -> P -> M P
ta --> tb = fresh \ø -> sameUniverse (Var ø ta) tb $> Pi ("_" <> ø) ta tb

(**) :: P -> P -> M P
ta ** tb = fresh \ø -> sameUniverse (Var ø ta) tb $> Sigma ("_" <> ø) ta tb

negate :: P -> M P
negate tx = typ tx >> fresh \x -> pure $ Pi x tx Empty
