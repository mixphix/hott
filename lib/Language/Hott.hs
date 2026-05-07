module Language.Hott
  ( I (..)
  , E (..)
  , N (..)
  , P (..)
  , M (..)
  , runM
  , evalM
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
import Control.Monad.Except
import Control.Monad.Interpret
import Control.Monad.State
import Data.Bool
import Data.Either
import Data.Eq
import Data.Function
import Data.List qualified as List
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.Ord
import Data.Semigroup (Semigroup ((<>)))
import Data.String
import Data.Text (Text)
import Data.Tuple
import GHC.Enum
import GHC.Show
import Numeric.Natural (Natural)
import Text.Read (Read)

-- | Identifier
newtype I = I Text deriving newtype (IsString, Eq, Ord, Semigroup, Show, Read)

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
  deriving (Eq, Show, Read)

-- | eNvironment
data N = N {gamma :: NonEmpty (Map I P), state :: Natural, definitions :: Map I P}
  deriving (Eq, Ord, Show)

n0 :: N
n0 = N (pure gamma) 0 Map.empty
 where
  gamma =
    Map.fromList
      [ ("Unit", U 0)
      , ("()", Point "Unit")
      , ("Bool", U 0)
      , ("True", Point "Bool")
      , ("False", Point "Bool")
      , ("Void", U 0)
      , ("Ordering", U 0)
      , ("LT", Point "Ordering")
      , ("EQ", Point "Ordering")
      , ("GT", Point "Ordering")
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
  deriving (Eq, Ord, Show, Read)

-- Monad
newtype M x = M (Interpret E N P x)
  deriving newtype (Functor, Applicative, Monad, MonadError E, MonadState N)

runM :: M x -> N -> (Either E x, N)
runM (M t) = runInterpret t

evalM :: M x -> N -> Either E x
evalM (M t) = fst . runInterpret t

-- scoped :: M x -> M x
-- scoped mx = do
--   n <- get
--   put n{gamma = Map.empty <| n.gamma}
--   x <- mx
--   put n
--   pure x

instance MonadInterpret I N P M where
  typeof :: I -> M (Maybe P)
  typeof i = gets \n -> asum (Map.lookup i <$> n.gamma)
  assume :: Var I P -> M ()
  assume (Var i p) = bind (typeof i) \case
    Nothing -> do
      typ p
      modify \n ->
        let g :| gs = n.gamma
         in n{gamma = Map.insert i p g :| gs}
    Just ip -> throwError (AlreadyBound i ip)
  define :: Var I P -> M ()
  define (Var i p) = bind (typeof i) \case
    Nothing -> do
      ip <- infer p
      case ip of
        U _ -> do
          assume (Var i ip)
          modify \n ->
            n{definitions = Map.insert i p n.definitions}
        t -> do
          typ t
          assume (Var i ip)
          modify \n ->
            n{definitions = Map.insert i p n.definitions}
    Just ip -> throwError (AlreadyBound i ip)
  recall :: I -> M (Maybe P)
  recall i = gets \n -> Map.lookup i n.definitions

  fresh :: (I -> M x) -> M x
  fresh rec = do
    n <- get
    put (N n.gamma (succ n.state) n.definitions)
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
    liftM6 z ma mb mc md me mf = do
      a <- ma
      b <- mb
      c <- mc
      d <- md
      e <- me
      z a b c d e <$> mf

  (===) :: P -> P -> M ()
  a === b = case (a, b) of
    (U m, U n) -> do
      unless (m == n) $ throwError (UniverseMismatch m n)
    (Point i, Point j) -> do
      unless (i == j) $ throwError (Disequality a b)
    (Func (Var v0 a0) b0, Func (Var v1 a1) b1) -> fresh \__ -> do
      a0_ <- repoint (Point __) v0 a0
      b0_ <- repoint (Point __) v0 b0
      let f0 = Func (Var __ a0_) b0_
      a1_ <- repoint (Point __) v1 a1
      b1_ <- repoint (Point __) v1 b1
      let f1 = Func (Var __ a1_) b1_
      unless (f0 == f1) $ throwError (Disequality a b)
    (Lambda (Var v0 a0) b0, Lambda (Var v1 a1) b1) -> fresh \__ -> do
      a0_ <- repoint (Point __) v0 a0
      b0_ <- repoint (Point __) v0 b0
      let f0 = Lambda (Var __ a0_) b0_
      a1_ <- repoint (Point __) v1 a1
      b1_ <- repoint (Point __) v1 b1
      let f1 = Lambda (Var __ a1_) b1_
      unless (f0 == f1) $ throwError (Disequality a b)
    (Sigma (Var v0 a0) b0, Sigma (Var v1 a1) b1) -> fresh \__ -> do
      a0_ <- repoint (Point __) v0 a0
      b0_ <- repoint (Point __) v0 b0
      let f0 = Sigma (Var __ a0_) b0_
      a1_ <- repoint (Point __) v1 a1
      b1_ <- repoint (Point __) v1 b1
      let f1 = Sigma (Var __ a1_) b1_
      unless (f0 == f1) $ throwError (Disequality a b)
    (Pair a0 b0, Pair a1 b1) -> do
      a0 === a1
      b0 === b1
    ( Proj (Var q0 t0) (Var z0 c0) (Var x0 (Var y0 g0)) p0
      , Proj (Var q1 t1) (Var z1 c1) (Var x1 (Var y1 g1)) p1
      ) -> fresh \_q -> fresh \_z -> fresh \_x -> fresh \_y -> do
        t0_ <- repoint (Point _q) q0 t0
        c0_ <- repoint (Point _z) z0 c0
        g0_ <- (repoint (Point _x) x0 >=> repoint (Point _y) y0) g0
        let f0 = Proj (Var _q t0_) (Var _z c0_) (Var _x (Var _y g0_)) p0
        t1_ <- repoint (Point _q) q1 t1
        c1_ <- repoint (Point _z) z1 c1
        g1_ <- (repoint (Point _x) x1 >=> repoint (Point _y) y1) g1
        let f1 = Proj (Var _q t1_) (Var _z c1_) (Var _x (Var _y g1_)) p1
        p0 === p1
        unless (f0 == f1) $ throwError (Disequality a b)
    (Coproduct a0 b0, Coproduct a1 b1) -> do
      a0 === a1
      b0 === b1
    (InL _0, InL _1) -> _0 === _1
    (InR _0, InR _1) -> _0 === _1
    ( Match (Var z0 t0) (Var x0 a0) (Var y0 b0) p0
      , Match (Var z1 t1) (Var x1 a1) (Var y1 b1) p1
      ) -> fresh \_z -> fresh \_x -> fresh \_y -> do
        t0_ <- repoint (Point _z) z0 t0
        a0_ <- repoint (Point _x) x0 a0
        b0_ <- repoint (Point _y) y0 b0
        let f0 = Match (Var _z t0_) (Var _x a0_) (Var _y b0_) p0
        t1_ <- repoint (Point _z) z1 t1
        a1_ <- repoint (Point _x) x1 a1
        b1_ <- repoint (Point _y) y1 b1
        let f1 = Match (Var _z t1_) (Var _x a1_) (Var _y b1_) p1
        p0 === p1
        unless (f0 == f1) $ throwError (Disequality a b)
    (Naturals, Naturals) -> pure ()
    (Zero, Zero) -> pure ()
    (Succ m, Succ n) -> m === n
    ( Peano (Var z0 t0) c0 (Var x0 (Var y0 c'0)) m0
      , Peano (Var z1 t1) c1 (Var x1 (Var y1 c'1)) m1
      ) -> fresh \_z -> fresh \_x -> fresh \_y -> do
        t0_ <- repoint (Point _z) z0 t0
        c'0_ <- (repoint (Point _x) x0 >=> repoint (Point _y) y0) c'0
        let f0 = Peano (Var _z t0_) c0 (Var _x (Var _y c'0_)) m0
        t1_ <- repoint (Point _z) z1 t1
        c'1_ <- (repoint (Point _x) x1 >=> repoint (Point _y) y1) c'1
        let f1 = Peano (Var _z t1_) c1 (Var _x (Var _y c'1_)) m1
        c0 === c1
        m0 === m1
        unless (f0 == f1) $ throwError (Disequality a b)
    (Equality t0 a0 b0, Equality t1 a1 b1) -> do
      t0 === t1
      a0 === a1
      b0 === b1
    (Refl _0, Refl _1) -> _0 === _1
    ( Path ta0 (Var x0 (Var y0 (Var p0 t0))) (Var z0 c0) a0 b0 e0
      , Path ta1 (Var x1 (Var y1 (Var p1 t1))) (Var z1 c1) a1 b1 e1
      ) -> fresh \_x -> fresh \_y -> fresh \_p -> fresh \_z -> do
        ta0 === ta1
        t0_ <-
          ( repoint (Point _x) x0
              >=> repoint (Point _y) y0
              >=> repoint (Point _p) p0
          )
            t0
        c0_ <- repoint (Point _z) z0 c0
        let f0 = Path ta0 (Var _x (Var _y (Var _p t0_))) (Var _z c0_) a0 b0 e0
        t1_ <-
          ( repoint (Point _x) x1
              >=> repoint (Point _y) y1
              >=> repoint (Point _p) p1
          )
            t1
        c1_ <- repoint (Point _z) z1 c1
        let f1 = Path ta1 (Var _x (Var _y (Var _p t1_))) (Var _z c1_) a1 b1 e1
        a0 === a1
        b0 === b1
        e0 === e1
        unless (f0 == f1) $ throwError (Disequality a b)
    _ -> throwError (Disequality a b)

  infer :: P -> M P
  infer this = case this of
    U u -> pure (U (succ u))
    --
    Point i -> bind (typeof i) \case
      Just p -> pure p
      Nothing -> throwError (UnknownIdentifier i)
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
    Apply f _ -> throwError (NotAFunction f)
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
    Proj (Var _ Sigma{}) _ _ p -> throwError (NotAPair p)
    Proj (Var _ tp) _ _ _ -> throwError (NotASigmaType tp)
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
      _ -> throwError (NotAnInjection e)
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
        _ -> throwError (NotANatural nat)
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
    FunExt _f _g -> throwError (Crash)
    UA _i _ta _tb -> throwError (Crash)

  compute :: P -> M P
  compute = \case
    Point x -> bind (recall x) \case
      Nothing -> pure (Point x)
      Just p -> compute p
    Apply (Lambda (Var x ta) b) a -> do
      a √ ta
      compute =<< repoint a x b
    Apply f a -> do
      p <- compute f
      compute (Apply p a)
    --
    Proj (Var _ s@(Sigma (Var _ ta) tb)) (Var z tc) (Var x (Var y g)) (Pair a b) -> do
      suppose (Var z s) (typ tc)
      Pair a b √ s
      suppose (Var x ta) $ suppose (Var y tb) do
        c' <- repoint (Pair a b) z tc
        g' <- (repoint a x >=> repoint b y) g
        g' √ c'
        compute g'
    Proj s@(Var _ Sigma{}) z xy p -> bind (compute p) \case
      Pair a b -> compute (Proj s z xy (Pair a b))
      x -> throwError (NotAPair x)
    Proj (Var x tp) z xy p -> bind (compute tp) \case
      Sigma v t -> compute $ Proj (Var x (Sigma v t)) z xy p
      t -> throwError (NotASigmaType t)
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
      e' -> bind (compute e') \case
        InL a -> compute (Match (Var z tc) (Var x c) (Var y d) (InL a))
        InR b -> compute (Match (Var z tc) (Var x c) (Var y d) (InR b))
        p -> throwError (NotAnInjection p)
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
        _ -> throwError (NotANatural nat)
    --
    Path ta (Var x (Var y (Var p tc))) (Var z c) a b (Refl a') -> do
      unless (List.all (a' ==) [a, b]) $ throwError (NonidenticalRefl a' a b)
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
    Path _ _ _ _ _ e -> throwError (NotAReflection e)
    --
    p -> pure p

typ :: P -> M ()
typ = void . universe

(√) :: P -> P -> M ()
a √ t = (t ===) =<< infer a

universe :: P -> M Natural
universe point = bind (infer point) \case
  U u -> pure u
  t -> throwError (NotAType point t)

sameUniverse :: P -> P -> M Natural
sameUniverse p0 p1 = do
  u0 <- universe p0
  u1 <- universe p1
  unless (u0 == u1) $ throwError (UniverseMismatch u0 u1)
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
