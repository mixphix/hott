module Language.Hott.Structure
  ( I (..)
  , E (..)
  , N (..)
  , P (..)
  , M (..)
  , runM
  , n0
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
import Control.Monad.Interpret
import Control.Monad.State
import Control.Monad.Writer (MonadWriter)
import Control.Monad.Writer qualified
import Data.Bool
import Data.Eq
import Data.Function
import Data.Functor
import Data.List qualified as List
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.Ord
import Data.Semigroup (Semigroup ((<>)))
import Data.String
import Data.Text (Text)
import GHC.Enum
import GHC.Err (undefined)
import GHC.Show
import Numeric.Natural (Natural)

tell :: (MonadWriter w m) => w -> m x
tell e = Control.Monad.Writer.tell e $> undefined

-- | Identifier
newtype I = I Text deriving newtype (IsString, Eq, Ord, Semigroup, Show)

-- | Error
data E
  = Crash
  | SyntaxError P P
  | Disequality P P
  | UnknownIdentifier I
  | AlreadyBound I P
  | UniverseMismatch Natural Natural
  | TypeMismatch P P
  | NotAType P P
  | NotAFunction P
  | NotASigmaType P
  | NotAPair P
  | NotANatural P
  | NotAnInjection P
  | InjectionMismatch P P
  | NonidenticalRefl P P P
  | NotAReflection P
  | NotAPath P
  deriving (Eq, Show)

-- | eNvironment
data N = N {gamma :: Map I P, state :: Natural} deriving (Eq, Ord, Show)

n0 :: N
n0 = N gamma 0
 where
  gamma =
    Map.fromList
      [ ("Unit", U 0)
      , ("()", Point "Unit")
      , ("Bool", U 0)
      , ("True", Point "Bool")
      , ("False", Point "Bool")
      ]

-- | Point
data P
  = U Natural
  | --
    Point I
  | --
    Func (Var I P) P
  | Lambda (Var I P) P
  | Apply P P
  | --
    Sigma (Var I P) P
  | Pair P P
  | Proj (Var I P) (Var I P) (Var I (Var I P)) P
  | --
    Coproduct P P
  | InL P
  | InR P
  | Match (Var I P) (Var I P) (Var I P) P
  | --
    Sum [Var I P]
  | Inj I P
  | Cases (Var I P) [Var I P] P
  | --
    Naturals
  | Zero
  | Succ P
  | Peano (Var I P) P (Var I (Var I P)) P
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
  deriving newtype (Functor, Applicative, Monad, MonadWriter [E], MonadState N)

runM :: M x -> N -> ((x, [E]), N)
runM (M t) = runInterpret t

instance MonadInterpret I N P M where
  recall :: I -> M (Maybe P)
  recall i = gets (Map.lookup i . gamma)

  assume :: Var I P -> M ()
  assume (Var i p) = bind (recall i) \case
    Nothing -> modify \n -> n{gamma = Map.insert i p n.gamma}
    Just ip -> tell [AlreadyBound i ip]

  fresh :: (I -> M x) -> M x
  fresh rec = do
    n <- get
    put (N n.gamma (succ n.state))
    rec ("_" <> fromString (show n.state))

  repoint :: P -> I -> (P -> M P)
  repoint with this = \case
    U u -> pure (U u)
    --
    Point p -> pure if this == p then with else Point p
    --
    Func (Var x ta) tb
      | this == x -> fresh \__ ->
          rec =<< liftM2
            do Func . Var __
            do repoint (Point __) x ta
            do repoint (Point __) x tb
      | otherwise -> liftM2 (Func . Var x) (rec ta) (rec tb)
    Lambda (Var x ta) b
      | this == x -> fresh \__ ->
          rec =<< liftM2
            do Lambda . Var __
            do repoint (Point __) x ta
            do repoint (Point __) x b
      | otherwise -> liftM2 (Lambda . Var x) (rec ta) (rec b)
    Apply p0 p1 -> liftM2 Apply (rec p0) (rec p1)
    --
    Sigma (Var x ta) tb
      | this == x -> fresh \__ ->
          rec =<< liftM2
            do Sigma . Var __
            do repoint (Point __) x ta
            do repoint (Point __) x tb
      | otherwise -> liftM2 (Sigma . Var x) (rec ta) (rec tb)
    Pair a b -> liftM2 Pair (rec a) (rec b)
    Proj (Var p tp) (Var z tc) (Var x (Var y g)) pair
      | this == p -> fresh \__ -> do
          tp' <- repoint (Point __) p tp
          rec $ Proj (Var __ tp') (Var z tc) (Var x (Var y g)) pair
      | this == z -> fresh \__ -> do
          tc' <- repoint (Point __) z tc
          rec $ Proj (Var p tp) (Var __ tc') (Var x (Var y g)) pair
      | this == x -> fresh \__ -> do
          g' <- repoint (Point __) x g
          rec $ Proj (Var p tp) (Var z tc) (Var __ (Var y g')) pair
      | this == y -> fresh \__ -> do
          g' <- repoint (Point __) y g
          rec $ Proj (Var p tp) (Var z tc) (Var x (Var __ g')) pair
      | otherwise ->
          liftM4
            Proj
            (Var p <$> rec tp)
            (Var z <$> rec tc)
            (Var x . Var y <$> rec g)
            (rec pair)
    --
    Coproduct ta tb -> liftM2 Coproduct (rec ta) (rec tb)
    InL a -> InL <$> rec a
    InR b -> InR <$> rec b
    Match (Var z tc) (Var x c) (Var y d) e
      | this == z -> fresh \__ -> do
          tc' <- repoint (Point __) z tc
          rec $ Match (Var __ tc') (Var x c) (Var y d) e
      | this == x -> fresh \__ -> do
          c' <- repoint (Point __) x c
          rec $ Match (Var z tc) (Var __ c') (Var y d) e
      | this == y -> fresh \__ -> do
          d' <- repoint (Point __) y d
          rec $ Match (Var z tc) (Var x c) (Var __ d') e
      | otherwise ->
          liftM4
            Match
            (Var z <$> rec tc)
            (Var x <$> rec c)
            (Var y <$> rec d)
            (rec e)
    --
    Sum vs -> Sum <$> traverse recV vs
    Inj i a
      | this == i -> fresh \__ -> do
          rec . Inj __ =<< repoint (Point __) i a
      | otherwise -> Inj i <$> rec a
    Cases (Var z tc) ps e
      | this == z -> fresh \__ -> do
          tc' <- repoint (Point __) z tc
          ps' <- traverse recV ps
          rec . Cases (Var __ tc') ps' =<< repoint (Point __) z e
      | otherwise ->
          liftM3
            Cases
            (Var z <$> rec tc)
            (traverse recV ps)
            (rec e)
    --
    Naturals -> pure Naturals
    Zero -> pure Zero
    Succ m -> Succ <$> rec m
    Peano (Var z tc) c0 (Var x (Var y c1)) m
      | this == z -> fresh \__ -> do
          tc' <- repoint (Point __) z tc
          rec $ Peano (Var __ tc') c0 (Var x (Var y c1)) m
      | this == x -> fresh \__ -> do
          c1' <- repoint (Point __) x c1
          rec $ Peano (Var z tc) c0 (Var __ (Var y c1')) m
      | this == y -> fresh \__ -> do
          c1' <- repoint (Point __) y c1
          rec $ Peano (Var z tc) c0 (Var x (Var __ c1')) m
      | otherwise ->
          liftM4
            Peano
            (Var z <$> rec tc)
            (rec c0)
            (Var x . Var y <$> rec c1)
            (rec m)
    --
    Equality ta a b -> liftM3 Equality (rec ta) (rec a) (rec b)
    Refl a -> Refl <$> rec a
    Path ta (Var x (Var y (Var p tc))) (Var z c) a b path
      | this == x -> fresh \__ -> do
          tc' <- repoint (Point __) x tc
          rec $ Path ta (Var __ (Var y (Var p tc'))) (Var z c) a b path
      | this == y -> fresh \__ -> do
          tc' <- repoint (Point __) y tc
          rec $ Path ta (Var x (Var __ (Var p tc'))) (Var z c) a b path
      | this == p -> fresh \__ -> do
          tc' <- repoint (Point __) x tc
          rec $ Path ta (Var x (Var y (Var __ tc'))) (Var z c) a b path
      | this == z -> fresh \__ -> do
          c' <- repoint (Point __) z c
          rec $ Path ta (Var x (Var y (Var p tc))) (Var __ c') a b path
      | otherwise ->
          liftM6
            Path
            (rec ta)
            (Var x . Var y . Var p <$> rec tc)
            (Var z <$> rec c)
            (rec a)
            (rec b)
            (rec path)
    --
    FunExt f g -> liftM2 FunExt (rec f) (rec g)
    UA i ta tb -> liftM2 (UA i) (rec ta) (rec tb)
   where
    rec = repoint with this
    recV (Var i p)
      | this == i =
          fresh \__ -> Var __ <$> (rec =<< repoint (Point __) i p)
      | otherwise = Var i <$> rec p
    liftM6 z ma mb mc md me mf = do
      a <- ma
      b <- mb
      c <- mc
      d <- md
      e <- me
      z a b c d e <$> mf

  infer :: P -> M P
  infer this = case this of
    U u -> pure (U (succ u))
    --
    Point i -> bind (recall i) \case
      Just p -> pure p
      Nothing -> tell [UnknownIdentifier i]
    --
    Func (Var x ta) tb -> suppose (Var x ta) do
      ua <- universe ta
      ub <- universe tb
      pure (U $ max ua ub)
    Lambda (Var x ta) b -> do
      typ ta
      tb <- suppose (Var x ta) (infer b)
      pure (Func (Var x ta) tb)
    Apply (Lambda (Var x ta) b) a -> do
      a √ ta
      suppose (Var x ta) do
        infer =<< repoint a x b
    Apply f _ -> tell [NotAFunction f]
    --
    Sigma (Var z ta) tb -> suppose (Var z ta) do
      U <$> sameUniverse ta tb
    Pair a b -> do
      ta <- infer a
      fresh \__ -> suppose (Var __ ta) do
        tb <- infer =<< repoint a __ b
        pure (Sigma (Var __ ta) tb)
    Proj (Var _ (Sigma (Var q ta) tb)) (Var z tc) (Var x (Var y g)) p@(Pair a b) -> do
      p √ Sigma (Var q ta) tb
      suppose (Var z (Sigma (Var q ta) tb)) (typ tc)
      suppose (Var x ta) $ suppose (Var y tb) do
        tc' <- repoint p z tc
        g' <- (repoint a x >=> repoint b y) g
        g' √ tc'
        pure tc'
    Proj (Var _ Sigma{}) _ _ p -> tell [NotAPair p]
    Proj (Var _ tp) _ _ _ -> tell [NotASigmaType tp]
    --
    Coproduct ta tb -> do
      ua <- universe ta
      ub <- universe tb
      pure (U $ max ua ub)
    InL a -> do
      ta <- infer a
      fresh $ pure . Coproduct ta . Point
    InR b -> do
      tb <- infer b
      fresh \__ -> pure (Coproduct (Point __) tb)
    Match (Var z tc) (Var x c) (Var y d) e -> case e of
      InL a -> do
        ta <- infer a
        fresh \__ -> suppose (Var z (Coproduct ta (Point __))) (typ tc)
        suppose (Var x ta) do
          tc' <- repoint e z tc
          c' <- repoint a x c
          c' √ tc'
          pure tc'
      InR b -> do
        tb <- infer b
        fresh \__ -> suppose (Var z (Coproduct (Point __) tb)) (typ tc)
        suppose (Var y tb) do
          tc' <- repoint e z tc
          d' <- repoint b y d
          d' √ tc'
          pure tc'
      _ -> tell [NotAnInjection e]
    --
    Sum vs -> do
      us <- traverse (var $ const universe) vs
      pure case us of
        [] -> U 0
        xs -> U (List.maximum xs)
    Inj i a -> bind (recall i) \case
      Just (Func (Var _ ta) tb) -> do
        a √ ta
        pure tb
      _ -> tell [UnknownIdentifier i]
    Cases (Var z tc) ps e -> case e of
      Inj i a -> do
        _ <- infer a
        bind (infer e) \case
          Sum vs -> case findPattern i ps of
            Nothing -> tell [InjectionMismatch e (Sum vs)]
            Just _ -> do
              suppose (Var z (Sum vs)) (typ tc)
              repoint e z tc
          _ -> tell [Crash]
      _ -> tell [NotAnInjection e]
    --
    Naturals -> pure (U 0)
    Zero -> pure Naturals
    Succ m -> m √ Naturals >> pure Naturals
    Peano (Var z tc) c0 (Var x (Var y c1)) nat -> do
      suppose (Var z Naturals) (typ tc)
      case nat of
        Zero -> do
          tc' <- repoint Zero z tc
          c0 √ tc'
          pure tc'
        Succ m -> do
          tc' <- repoint (Succ m) z tc
          suppose (Var x Naturals) $ suppose (Var y tc') do
            let ind = Peano (Var z tc) c0 (Var x (Var y c1)) m
            c1' <- (repoint m x >=> repoint ind y) c1
            c1' √ tc'
            pure tc'
        _ -> tell [NotANatural nat]
    --
    Equality ta a b -> do
      a √ ta
      b √ ta
      fmap U (universe ta)
    Refl a -> do
      ta <- infer a
      pure (Equality ta a a)
    Path ta (Var x (Var y (Var p tc))) (Var z c) a b path -> do
      a √ ta
      b √ ta
      path √ Equality ta a b
      tc' <-
        ( repoint (Point z) x
            >=> repoint (Point z) y
            >=> repoint (Refl (Point z)) p
          )
          tc
      suppose (Var z ta) (c √ tc')
      pure tc'
    --
    FunExt _f _g -> tell [Crash]
    UA _i _ta _tb -> tell [Crash]

  compute :: P -> M P
  compute = \case
    Apply (Lambda (Var x ta) b) a -> do
      a √ ta
      compute =<< repoint a x b
    Apply f _ -> tell [NotAFunction f]
    --
    Proj (Var _ s@(Sigma (Var _ ta) tb)) (Var z tc) (Var x (Var y g)) (Pair a b) -> do
      suppose (Var z s) (typ tc)
      Pair a b √ s
      suppose (Var x ta) $ suppose (Var y tb) do
        c' <- repoint (Pair a b) z tc
        g' <- (repoint a x >=> repoint b y) g
        g' √ c'
        compute g'
    Proj (Var _ Sigma{}) _ _ p -> tell [NotAPair p]
    Proj (Var _ tp) _ _ _ -> tell [NotASigmaType tp]
    --
    Match (Var z tc) (Var x c) (Var y d) e -> case e of
      InL a -> do
        ta <- infer a
        suppose (Var x ta) do
          tc' <- repoint (InL a) z tc
          c' <- repoint a x c
          c' √ tc'
          compute c'
      InR b -> do
        tb <- infer b
        suppose (Var y tb) do
          td' <- repoint (InR b) z tc
          d' <- repoint b y d
          d' √ td'
          compute d'
      _ -> tell [NotAnInjection e]
    --
    Cases (Var z tc) cs e -> case e of
      Inj i a -> bind (recall i) \case
        Just (Func (Var x tia) (Sum _)) -> do
          ta <- infer a
          unless (tia == ta) $ tell [TypeMismatch tia ta]
          case findPattern i cs of
            Nothing -> tell [UnknownIdentifier i]
            Just c -> suppose (Var x ta) do
              tc' <- repoint (Inj i a) z tc
              c' <- repoint a x c
              c' √ tc'
              compute c'
        _ -> tell [UnknownIdentifier i]
      _ -> tell [NotAnInjection e]
    --
    Peano (Var z tc) c0 (Var x (Var y c1)) nat -> do
      suppose (Var z Naturals) (typ tc)
      case nat of
        Zero -> compute c0
        Succ m -> do
          tc' <- repoint (Succ m) z tc
          suppose (Var x Naturals) $ suppose (Var y tc') do
            let ind = Peano (Var z tc) c0 (Var x (Var y c1)) m
            c1' <- (repoint m x >=> repoint ind y) c1
            c1' √ tc'
            compute c1'
        _ -> tell [NotANatural nat]
    --
    Path ta (Var x (Var y (Var p tc))) (Var z c) a b (Refl a') -> do
      unless (List.all (a' ==) [a, b]) $ tell [NonidenticalRefl a' a b]
      supposeAll
        [ Var x ta
        , Var y ta
        , Var p (Equality ta (Point x) (Point y))
        ]
        (typ tc)
      suppose (Var z ta) do
        tc' <-
          ( repoint (Point z) x
              >=> repoint (Point z) y
              >=> repoint (Refl (Point z)) p
            )
            tc
        c' <- repoint a z c
        c' √ tc'
        compute c'
    Path _ _ _ _ _ e -> tell [NotAReflection e]
    --
    p -> pure p

typ :: P -> M ()
typ = void . universe

(√) :: P -> P -> M ()
a √ t = infer a >>= \ta -> unless (t == ta) (tell [SyntaxError t ta])

universe :: P -> M Natural
universe point =
  infer point >>= \case
    U u -> pure u
    t -> tell [NotAType point t]

sameUniverse :: P -> P -> M Natural
sameUniverse p0 p1 = do
  u0 <- universe p0
  u1 <- universe p1
  unless (u0 == u1) $ tell [UniverseMismatch u0 u1]
  pure u0

findPattern :: I -> [Var I P] -> Maybe P
findPattern i ps =
  List.find (var \i_ _ -> i == i_) ps <&> \(Var _ p) -> p

(-->) :: P -> P -> M P
ta --> tb = sameUniverse ta tb >> fresh \__ -> pure (Func (Var __ ta) tb)

(**) :: P -> P -> M P
ta ** tb = sameUniverse ta tb >> fresh \__ -> pure (Sigma (Var __ ta) tb)

-- negate :: P -> M P
-- negate tx = typ tx >> fresh \x -> pure (Func x tx Bottom)
