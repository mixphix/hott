module Language.Hott.Parse where

import Control.Monad.Interpret
import Language.Hott.Source

import Control.Applicative
import Control.Block
import Data.Bool
import Data.Either
import Data.Enum (Enum (..))
import Data.Function
import Data.List qualified as List
import Data.Text (Text)
import Data.Traversable (mapAccumM)
import Language.Hott.Lex (I (I))
import Language.Hott.Lex qualified as Lex
import Numeric.Natural (Natural)
import Text.Show (Show)

data E
  = Reserved !Source !Text
  | UnexpectedToken !Lex.Lexed
  | MissingClosedParenthesis !Source
  | Indentation !Source
  | WrongDefinitionExitCondition !Source
  | UnexpectedEndOfFile
  deriving (Show)

data Parsed
  = ParsedUniverse !Source !Natural
  | ParsedNatural !Source !Natural
  | ParsedIdentifier !Source !I
  | ParsedSymbol !Source !I
  | ParsedConstructor !Source !I
  | ParsedDoubleColon !Source !Parsed
  | ParsedIsDefinedAs !Source !I !Parsed
  | ParsedLambda !Source ![Parsed] ![Parsed]
  | ParsedRightArrow !Source
  | ParsedLet !Source ![(Var Source I, Var Source Parsed)]
  | ParsedIn !Source !Parsed
  | ParsedWhere !Source ![(Var Source I, Var Source Parsed)]
  | ParsedDo !Source ![Parsed]
  | ParsedCase !Source ![(Parsed, Parsed)]
  | ParsedUnit !Source
  | ParsedDefinition !Source !Parsed ![Parsed]
  | ParsedFunction !Source !Parsed ![Parsed]

instance GetSource Parsed where
  getSource :: Parsed -> Source
  getSource = \case
    ParsedUniverse source _ -> source
    ParsedNatural source _ -> source
    ParsedIdentifier source _ -> source
    ParsedSymbol source _ -> source
    ParsedConstructor source _ -> source
    ParsedDoubleColon source _ -> source
    ParsedIsDefinedAs source _ _ -> source
    ParsedLambda source _ _ -> source
    ParsedRightArrow source -> source
    ParsedLet source _ -> source
    ParsedIn source _ -> source
    ParsedWhere source _ -> source
    ParsedDo source _ -> source
    ParsedCase source _ -> source
    ParsedUnit source -> source
    ParsedDefinition source _ _ -> source
    ParsedFunction source _ _ -> source

data State
  = TopLevel
  | Brackets !Natural
  | Definition !I

parse :: State -> [Lex.Lexed] -> Either E (State, [Parsed])
parse TopLevel = \case
  Lex.LexedIdentifier source identifier : rest0 -> do
    (s, ps) <- parse (Definition identifier) rest0
    case s of
      TopLevel ->
        pure
          (TopLevel, [ParsedDefinition source (ParsedIdentifier source identifier) ps])
      _ -> Left (WrongDefinitionExitCondition source)
  p : _ -> Left (UnexpectedToken p)
  [] -> pure (TopLevel, [])
parse (Brackets n) = \case
  Lex.LexedIdentifier source identifier : rest0 -> do
    fmap (ParsedIdentifier source identifier :) <$> parse (Brackets n) rest0
  Lex.LexedCloseBracket _ : rest0 -> case n of
    0 -> parse TopLevel rest0
    _ -> parse (Brackets (pred n)) rest0
  p : _ -> Left (UnexpectedToken p)
  [] -> Left UnexpectedEndOfFile
parse (Definition i) = \case
  Lex.LexedIdentifier source identifier : rest0 -> _
  p : _ -> Left (UnexpectedToken p)
  [] -> Left UnexpectedEndOfFile
