module Language.Hott (Lbl (Lbl), Var (Var), Point (..)) where

import Data.String (IsString)
import Data.Text (Text)
import Numeric.Natural (Natural)
import Prelude (Eq, Ord, Semigroup, Show)

newtype Lbl = Lbl Text deriving (IsString, Eq, Ord, Semigroup, Show)
data Var x = Var Lbl x deriving (Eq, Ord, Show)
data Point
  = U Natural
  | Point Lbl
  | Pi (Var Point) Point
  | Lam (Var Point) Point
  | App Point Point
  | Sig (Var Point) Point
  | Pair Point Point
  | Proj (Var Point) (Var Point) (Var (Var Point)) Point
  | Sum Point Point
  | InL Point
  | InR Point
  | Empty
  | Singleton
  | Single
  | Naturals
  | Zero
  | Succ Point
  | IndN (Var Point) Point (Var (Var Point)) Point
  | Equality Point Point Point
  | Refl Point
  | Path Point (Var (Var (Var Point))) (Var Point) Point Point Point
  | FunExt Point Point
  | UA Natural Point Point
  deriving (Eq, Ord, Show)
