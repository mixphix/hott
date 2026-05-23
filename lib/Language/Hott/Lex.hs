module Language.Hott.Lex where

import Language.Hott.Source

import Bolt.Math
import Control.Block
import Control.Monad
import Data.Bool
import Data.Char
import Data.Either
import Data.Eq
import Data.Function
import Data.Int
import Data.List qualified as List
import Data.Maybe
import Data.Ord
import Data.Semigroup
import Data.String (IsString)
import Data.Text (Text)
import Data.Text qualified as Text
import Numeric.Natural (Natural)
import Text.Read (Read, readMaybe)
import Text.Show (Show)

-- | Identifier
newtype I = I Text deriving newtype (IsString, Eq, Ord, Semigroup, Show, Read)

data E
  = UnexpectedCharacter !Source Text
  | Panic !Source
  deriving (Show)

instance GetSource E where
  getSource :: E -> Source
  getSource = \case
    UnexpectedCharacter source _ -> source
    Panic source -> source

data Lexed
  = LexedUniverse !Source !Natural
  | LexedNatural !Source !Natural
  | LexedIdentifier !Source I -- lowercase
  | LexedSymbol !Source I
  | LexedConstructor !Source I -- uppercase
  | LexedDoubleColon !Source
  | LexedIsDefinedAs !Source -- :=
  | LexedLambda !Source -- \
  | LexedRightArrow !Source -- ->
  | LexedLet !Source -- let
  | LexedIn !Source -- in
  | LexedWhere !Source -- where
  | LexedDo !Source
  | LexedCase !Source
  | LexedNewline !Source
  | LexedWhitespace !Source {-# UNPACK #-} !Int
  | LexedUnit !Source
  | LexedOpenBracket !Source
  | LexedCloseBracket !Source
  deriving (Show)

instance GetSource Lexed where
  getSource :: Lexed -> Source
  getSource = \case
    LexedUniverse source _ -> source
    LexedNatural source _ -> source
    LexedIdentifier source _ -> source
    LexedSymbol source _ -> source
    LexedConstructor source _ -> source
    LexedDoubleColon source -> source
    LexedIsDefinedAs source -> source
    LexedLambda source -> source
    LexedRightArrow source -> source
    LexedLet source -> source
    LexedIn source -> source
    LexedWhere source -> source
    LexedDo source -> source
    LexedCase source -> source
    LexedNewline source -> source
    LexedWhitespace source _ -> source
    LexedUnit source -> source
    LexedOpenBracket source -> source
    LexedCloseBracket source -> source

lex :: Source -> Text -> Either E [Lexed]
lex _ "" = Right []
lex !source text0
  | Just text1 <- Text.stripPrefix "let" text0 = case Text.span (== ' ') text1 of
      ("", text2) -> case Text.span isLetter text2 of
        ("", text3) -> (LexedLet source :) <$> lex source{column = source.column + 3} text3
        (ters, text3) ->
          (LexedIdentifier source (I $ "let" <> ters) :)
            <$> lex source{column = source.column + 3 + Text.length ters} text3
      (spaces, text2) ->
        (LexedLet source :)
          <$> lex source{column = source.column + 3} (spaces <> text2)
  | Just text1 <- Text.stripPrefix "in" text0 = case Text.span isLetter text1 of
      ("", text2) -> (LexedIn source :) <$> lex source{column = source.column + 2} text2
      (nards, text2) ->
        (LexedIdentifier source (I $ "in" <> nards) :)
          <$> lex source{column = source.column + 2 + Text.length nards} text2
  | Just text1 <- Text.stripPrefix "where" text0 = case Text.span isLetter text1 of
      ("", text2) -> (LexedWhere source :) <$> lex source{column = source.column + 2} text2
      (at, text2) ->
        (LexedIdentifier source (I $ "where" <> at) :)
          <$> lex source{column = source.column + 2 + Text.length at} text2
  | Just text1 <- Text.stripPrefix "do" text0 = case Text.span isLetter text1 of
      ("", text2) -> (LexedDo source :) <$> lex source{column = source.column + 2} text2
      (ts, text2) ->
        (LexedIdentifier source (I $ "do" <> ts) :)
          <$> lex source{column = source.column + 2 + Text.length ts} text2
  | Just ('\n', text1) <- Text.uncons text0 =
      (LexedNewline source :)
        <$> lex source{line = source.line + 1, column = 0} text1
  | Just ('(', text1) <- Text.uncons text0 =
      (LexedOpenBracket source :)
        <$> lex source{column = source.column + 1} text1
  | Just (')', text1) <- Text.uncons text0 =
      (LexedCloseBracket source :)
        <$> lex source{column = source.column + 1} text1
  | Just ('\\', text1) <- Text.uncons text0 = case Text.span isSymbol text1 of
      ("", text2) -> (LexedLambda source :) <$> lex source{column = source.column + 1} text2
      (symbols, text2) ->
        (LexedSymbol source (I $ "\\" <> symbols) :)
          <$> lex source{column = source.column + 1 + Text.length symbols} text2
  | otherwise = case Text.span isSpace text0 of
      ("", text1) -> case Text.span isDigit text1 of
        ("", text2) -> case Text.span (liftM2 (||) isLetter (`List.elem` ['_', '\''])) text2 of
          ("", text3) -> case Text.span symbolic text3 of
            ("", text4) -> Left (UnexpectedCharacter source (Text.takeWhile (/= '\n') text4))
            ("()", text4) ->
              (LexedUnit source :)
                <$> lex source{column = source.column + 2} text4
            (":=", text4) ->
              (LexedIsDefinedAs source :)
                <$> lex source{column = source.column + 2} text4
            (":->", text4) ->
              (LexedRightArrow source :) <$> lex source{column = source.column + 2} text4
            (symbols, text4) ->
              (LexedSymbol source (I symbols) :)
                <$> lex source{column = source.column + Text.length symbols} text4
          (letters, text3) -> case Text.uncons letters of
            Nothing -> Left (Panic source)
            Just (firstLetter, _)
              | isUpperCase firstLetter ->
                  (LexedConstructor source (I letters) :)
                    <$> lex source{column = source.column + Text.length letters} text3
              | otherwise ->
                  (LexedIdentifier source (I letters) :)
                    <$> lex source{column = source.column + Text.length letters} text3
        (numbers, text2) ->
          (LexedNatural source (fromMaybe 0 . readMaybe $ Text.unpack numbers) :)
            <$> lex source{column = source.column + Text.length numbers} text2
      (spaces, text2) ->
        (LexedWhitespace source (Text.length spaces) :)
          <$> lex source{column = source.column + Text.length spaces} text2
 where
  symbolic c = isSymbol c || (not (isLetter c) && not (isSpace c))
