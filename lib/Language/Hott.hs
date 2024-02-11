{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Language.Hott where

import Control.Arrow (Arrow (..))
import Data.Text (Text, pack)
import Language.Hott.Monad
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
  | UniverseMismatch Point Natural Natural

type Infer = StateT (C, Natural) (Except TyErr)

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
universe = \case
  U i -> pure i
  t -> universe =<< typeOf t

(===) :: Point -> Infer Point -> Infer ()
point0 === run = do
  point1 <- run
  unless (point0 == point1) $ throwError (Unequal point0 point1)

(<==) :: Natural -> Infer Point -> Infer ()
ui <== run = do
  pt <- run
  ui' <- universe pt
  unless (ui <= ui') $ throwError (UniverseMismatch pt ui ui')

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
typeOf = \case
  U n -> pure (U (n + 1))
  Point x -> do
    Var _ tx <- given (Name x)
    pure tx
  Pi (Var x ta) tb -> do
    ui <- universe ta
    withVar (Var x ta) do
      ui <== typeOf tb
    pure (U ui)
  Lam (Var x ta) b -> do
    tb <- withVar (Var x ta) do
      typeOf b
    pure (Pi (Var x ta) tb)
  App (Pi (Var (Name x) ta) tb) a -> do
    ta === typeOf a
    repoint tb a x
  App _ _ -> throwError Crash
  Sig (Var x ta) tb -> do
    ui <- universe ta
    withVar (Var x ta) $ U ui === fmap U (universe tb)
    pure (U ui)
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
      _ui <- withVar (Var (Name z) tp) $ universe tc
      withVar (Var (Name x) ta) $ withVar (Var (Name y) tb) do
        c' <- repoint tc p z
        g' <- repoint g a x >>= \g_ -> repoint g_ b y
        c' === typeOf g'
        pure c'
  Proj _ _ _ _ -> throwError Crash
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
      _ui <- withVar (Var (Name z) Naturals) $ universe tc
      tc' <- repoint tc Zero x
      tc' === typeOf c0
      pure tc'
    Succ n -> withVar (Var (Name z) Naturals) do
      _ui <- universe tc
      tc' <- repoint tc n x
      withVar (Var (Name x) Naturals) $ withVar (Var (Name y) tc') do
        tcs <- repoint tc (Succ n) x
        tcs === typeOf cs
        pure tc'
    _ -> throwError Crash
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
  FunExt f g -> do
    _
  UA i ta tb -> do
    _
