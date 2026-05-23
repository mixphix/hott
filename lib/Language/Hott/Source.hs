module Language.Hott.Source where

import Data.Eq (Eq)
import Data.Int (Int)
import Data.Ord (Ord)
import Text.Show (Show)

data Source = Source {line :: !Int, column :: !Int} deriving (Eq, Ord, Show)

class GetSource x where
  getSource :: x -> Source
