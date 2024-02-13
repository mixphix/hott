module Language.Hott.Structure (Point (..), E (..)) where

import Control.Monad.Interpret (HasParseErrors (..), Var)
import Data.Text (Text)
import Numeric.Natural (Natural)
import Text.Parsec qualified as Parsec
import Prelude (Eq, Ord, Show)

data Point
  = U Natural
  | Point Text
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
data E
  = Crash
  | NotInContext Text
  | AlreadyBound Text Point
  | Unequal Point Point
  | UniverseMismatch Point Natural Point Natural
  | NotAType Point Point
  | NotAFunction Point
  | NotAPair Point
  | NotANatural Point
  | Misparse Parsec.ParseError
instance HasParseErrors E where
  parseFailure = Misparse
