module Language.Hott.Structure (P (..), E (..)) where

import Control.Monad.Interpret (HasParseErrors (..), Var)
import Data.Text (Text)
import Numeric.Natural (Natural)
import Text.Parsec qualified as Parsec
import Prelude (Eq, Ord, Show)

data P
  = U Natural
  | Point Text
  | Pi (Var P) P
  | Lam (Var P) P
  | App P P
  | Sig (Var P) P
  | Pair P P
  | Proj (Var P) (Var P) (Var (Var P)) P
  | Sum P P
  | InL P
  | InR P
  | Empty
  | Singleton
  | Single
  | Naturals
  | Zero
  | Succ P
  | IndN (Var P) P (Var (Var P)) P
  | Equality P P P
  | Refl P
  | Path P (Var (Var (Var P))) (Var P) P P P
  | FunExt P P
  | UA Natural P P
  deriving (Eq, Ord, Show)
data E
  = Crash
  | NotInContext Text
  | AlreadyBound Text P
  | Unequal P P
  | UniverseMismatch P Natural P Natural
  | NotAType P P
  | NotAFunction P
  | NotAPair P
  | NotANatural P
  | Misparse Parsec.ParseError
instance HasParseErrors E where
  parseFailure = Misparse
