module Language.Hott where

import Control.Applicative
import Control.Arrow (Arrow (..))
import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Data.Bool
import Data.Either
import Data.Eq
import Data.Function
import Data.Kind (Constraint, Type)
import Data.Ord
import Data.Semigroup (Semigroup ((<>)))
import Data.Text (Text, pack)
import Data.Tuple
import GHC.Enum
import GHC.Show
import Numeric.Natural (Natural)

newtype Name = Name Text
  deriving (Eq, Ord, Show)

data Var x = Var Name x
  deriving (Eq, Ord, Show)

data C
  = C_
  | (:&) C (Var Point)
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

data TyErr
  = Crash
  | NotInContext Name
  | AlreadyBound Name Point
  | Unequal Point Point
  | UniverseMismatch Point Natural Point Natural
  | NotAType Point Point
  | NotAFunction Point
  | NotAPair Point
  | NotANatural Point

type Infer = StateT (C, Natural) (Except TyErr)

runInfer :: (C, Natural) -> Infer x -> Either TyErr (x, (C, Natural))
runInfer = flip ((runExcept .) . runStateT)

evalInfer :: (C, Natural) -> Infer x -> Either TyErr x
evalInfer = (fmap fst .) . runInfer

eval :: Infer x -> Either TyErr x
eval = evalInfer (C_, 0)

type MonadFresh :: (Type -> Type) -> Constraint
class (Monad m) => MonadFresh m where
  type Fresh m :: Type
  fresh :: m (Fresh m)

type MonadContext :: (Type -> Type) -> Constraint
class (Monad m) => MonadContext m where
  type Context m :: Type
  context :: m (Context m)

instance MonadFresh Infer where
  type Fresh Infer = Text
  fresh = modify (second succ) >> gets (pack . show . snd)
instance MonadContext Infer where
  type Context Infer = C
  context = gets fst

inContext :: C -> Infer x -> Infer x
inContext ctx infer = do
  orig <- get
  withStateT (first $ const ctx) infer <* put orig

append :: Var Point -> Infer ()
append var = modify (first (:& var))

given :: Name -> Infer (Var Point)
given name =
  context >>= \case
    C_ -> throwError (NotInContext name)
    _ :& Var x tx | x == name -> pure (Var x tx)
    ctx :& _ -> inContext ctx (given name)

unbound :: Name -> Infer ()
unbound x =
  context >>= \case
    C_ -> pure ()
    ctx :& Var y ty -> do
      when (x == y) $ throwError (AlreadyBound x ty)
      inContext ctx (unbound x)

withVar :: Var Point -> Infer x -> Infer x
withVar (Var x tx) infer = do
  unbound x
  orig <- get
  modify $ first (:& Var x tx)
  infer <* put orig

universe :: Point -> Infer Natural
universe point = do
  typeOf point >>= \case
    U i -> pure i
    t -> throwError (NotAType point t)

sameUniverse :: Var Point -> Point -> Infer Natural
sameUniverse (Var _ p0) p1 = do
  u0 <- universe p0
  u1 <- universe p1
  unless (u0 == u1) $ throwError (UniverseMismatch p0 u0 p1 u1)
  pure u0

typ :: Point -> Infer ()
typ = void . universe

(===) :: Point -> Infer Point -> Infer ()
p0 === run = do
  p1 <- run
  unless (p0 == p1) $ throwError (Unequal p0 p1)

repoint :: Point -> Point -> Text -> Infer Point
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

typeOf :: Point -> Infer Point
typeOf point = case point of
  U n -> pure (U (succ n))
  Point x -> do
    Var _ tx <- given (Name x)
    pure tx
  Pi (Var x ta) tb -> U <$> sameUniverse (Var x ta) tb
  Lam (Var x ta) b -> do
    typ ta
    tb <- withVar (Var x ta) (typeOf b)
    pure (Pi (Var x ta) tb)
  App (Pi (Var (Name x) ta) tb) a -> do
    ta === typeOf a
    typ tb
    repoint tb a x
  App f _ -> throwError (NotAFunction f)
  Sig (Var x ta) tb -> U <$> sameUniverse (Var x ta) tb
  Pair a b -> do
    ta <- typeOf a
    x <- fresh
    tb <- withVar (Var (Name x) ta) do
      typeOf =<< repoint b a x
    pure (Sig (Var (Name x) ta) tb)
  Proj
    (Var _ tp@(Sig (Var _ ta) tb))
    (Var (Name z) tc)
    (Var (Name x) (Var (Name y) g))
    p@(Pair a b) -> do
      tp === typeOf p
      withVar (Var (Name z) tp) $ typ tc
      withVar (Var (Name x) ta) $ withVar (Var (Name y) tb) do
        c' <- repoint tc p z
        g' <- repoint g a x >>= \g_ -> repoint g_ b y
        c' === typeOf g'
        pure c'
  Proj (Var _ (Sig _ _)) _ _ p -> throwError (NotAPair p)
  Proj (Var _ tp) _ _ _ -> throwError (NotAPair tp)
  Sum ta tb -> U <$> sameUniverse (Var (Name "") ta) tb
  InL a -> do
    ta <- typeOf a
    ui <- typeOf ta
    b <- fresh
    append (Var (Name b) ui)
    pure (Sum ta (Point b))
  InR b -> do
    tb <- typeOf b
    ui <- typeOf tb
    a <- fresh
    append (Var (Name a) ui)
    pure (Sum (Point a) tb)
  Empty -> pure (U 0)
  Singleton -> pure (U 0)
  Single -> pure Singleton
  Naturals -> pure (U 0)
  Zero -> pure Naturals
  Succ n -> do
    Naturals === typeOf n
    pure Naturals
  IndN (Var (Name z) tc) c0 (Var (Name x) (Var (Name y) cs)) m -> case m of
    Zero -> do
      withVar (Var (Name z) Naturals) $ typ tc
      tc' <- repoint tc Zero x
      tc' === typeOf c0
      pure tc'
    Succ n -> do
      withVar (Var (Name z) Naturals) $ typ tc
      tc' <- repoint tc (Succ n) z
      withVar (Var (Name x) Naturals) $ withVar (Var (Name y) tc') do
        cs' <- repoint cs (Succ n) x
        tc' === typeOf cs'
      pure tc'
    _ -> throwError (NotANatural m)
  Equality ta a b -> do
    ta === typeOf a
    ta === typeOf b
    U <$> universe ta
  Refl a -> do
    ta <- typeOf a
    pure (Equality ta a a)
  Path
    ta
    (Var (Name x) (Var (Name y) (Var (Name p) tc)))
    (Var (Name z) c)
    a
    b
    path -> do
      ta === typeOf a
      ta === typeOf b
      Equality ta a b === typeOf path
      tc' <-
        repoint tc (Point z) x
          >>= (\tc_ -> repoint tc_ (Point z) y)
          >>= (\tc__ -> repoint tc__ (Refl (Point z)) p)
      withVar (Var (Name z) ta) $ tc' === typeOf c
      pure tc'
  FunExt _f _g -> throwError Crash
  UA _i _ta _tb -> throwError Crash

(-->) :: Point -> Point -> Infer Point
a --> b = do
  ui <- universe a
  ui' <- universe b
  x <- (<>) "_" <$> fresh
  let fun = Pi (Var (Name x) a) b
  unless (ui == ui') $ throwError (UniverseMismatch a ui b ui')
  pure fun

(**) :: Point -> Point -> Infer Point
a ** b = do
  ui <- universe a
  ui' <- universe b
  x <- (<>) "_" <$> fresh
  let pair = Sig (Var (Name x) a) b
  unless (ui == ui') $ throwError (UniverseMismatch a ui b ui')
  pure pair

negate :: Point -> Infer Point
negate point = do
  typ point
  x <- fresh
  pure (Pi (Var (Name x) point) Empty)
