module Language.Hott.Lex where

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
import Text.Read (Read)
import Text.Show (Show)

-- | Identifier
newtype I = I Text deriving newtype (IsString, Eq, Ord, Semigroup, Show, Read)

data Source = Source {line :: Int, column :: Int} deriving (Eq, Ord, Show)

data E
  = UnexpectedCharacter Text
  | Panic
  deriving (Show)

data Lexed
  = LexedIdentifier I -- lowercase
  | LexedSymbol I
  | LexedConstructor I -- uppercase
  | LexedIsDefinedAs -- :=
  | LexedLambda -- \
  | LexedRightArrow -- ->
  | LexedLet -- let
  | LexedIn -- in
  | LexedWhere -- where
  | LexedDo
  | LexedNewline
  | LexedWhitespace {-# UNPACK #-} !Int
  | LexedUnit
  | LexedOpenBracket
  | LexedCloseBracket
  deriving (Show)

lex :: Source -> Text -> (Source, Either E [Lexed])
lex source "" = (source, Right [])
lex source text0
  | Just text1 <- Text.stripPrefix "let" text0 = case Text.span (== ' ') text1 of
      ("", text2) -> case Text.span isLetter text2 of
        ("", text3) -> fmap (LexedLet :) <$> lex source{column = source.column + 3} text3
        (ters, text3) ->
          fmap (LexedIdentifier (I $ "let" <> ters) :)
            <$> lex source{column = source.column + 3 + Text.length ters} text3
      (spaces, text2) ->
        fmap (LexedLet :)
          <$> lex source{column = source.column + 3} (spaces <> text2)
  | Just text1 <- Text.stripPrefix "in" text0 = case Text.span isLetter text1 of
      ("", text2) -> fmap (LexedIn :) <$> lex source{column = source.column + 2} text2
      (nards, text2) ->
        fmap (LexedIdentifier (I $ "in" <> nards) :)
          <$> lex source{column = source.column + 2 + Text.length nards} text2
  | Just text1 <- Text.stripPrefix "where" text0 = case Text.span isLetter text1 of
      ("", text2) -> fmap (LexedIn :) <$> lex source{column = source.column + 2} text2
      (at, text2) ->
        fmap (LexedIdentifier (I $ "where" <> at) :)
          <$> lex source{column = source.column + 2 + Text.length at} text2
  | Just text1 <- Text.stripPrefix "do" text0 = case Text.span isLetter text1 of
      ("", text2) -> fmap (LexedDo :) <$> lex source{column = source.column + 2} text2
      (ts, text2) ->
        fmap (LexedIdentifier (I $ "do" <> ts) :)
          <$> lex source{column = source.column + 2 + Text.length ts} text2
  | Just ('\n', text1) <- Text.uncons text0 =
      fmap (LexedNewline :)
        <$> lex source{line = source.line + 1, column = 0} text1
  | Just ('(', text1) <- Text.uncons text0 =
      fmap (LexedOpenBracket :)
        <$> lex source{line = source.line + 1, column = 0} text1
  | Just (')', text1) <- Text.uncons text0 =
      fmap (LexedCloseBracket :)
        <$> lex source{line = source.line + 1, column = 0} text1
  | Just ('\\', text1) <- Text.uncons text0 = case Text.span isSymbol text1 of
      ("", text2) -> fmap (LexedLambda :) <$> lex source{column = source.column + 1} text2
      (symbols, text2) ->
        fmap (LexedSymbol (I $ "\\" <> symbols) :)
          <$> lex source{column = source.column + 1 + Text.length symbols} text2
  | otherwise = case Text.span isSpace text0 of
      ("", text1) -> case Text.span (liftM2 (||) isLetter (`List.elem` ['_', '\''])) text1 of
        ("", text2) -> case Text.span
          (liftM2 (||) isSymbol (liftM2 (&&) (not . isLetter) (not . isSpace)))
          text2 of
          ("", text3) -> (source, Left (UnexpectedCharacter (Text.takeWhile (/= '\n') text3)))
          (":=", text3) ->
            fmap (LexedIsDefinedAs :) <$> lex source{column = source.column + 2} text3
          (":->", text3) ->
            fmap (LexedRightArrow :) <$> lex source{column = source.column + 2} text3
          (symbols, text3) ->
            fmap (LexedSymbol (I symbols) :)
              <$> lex source{column = source.column + Text.length symbols} text3
        (letters, text2) -> case Text.uncons letters of
          Nothing -> (source, Left Panic)
          Just (firstLetter, _)
            | isUpperCase firstLetter ->
                fmap (LexedConstructor (I letters) :)
                  <$> lex source{column = source.column + Text.length letters} text2
            | otherwise ->
                fmap (LexedIdentifier (I letters) :)
                  <$> lex source{column = source.column + Text.length letters} text2
      (spaces, text1) ->
        fmap (LexedWhitespace (Text.length spaces) :)
          <$> lex source{column = source.column + Text.length spaces} text1
