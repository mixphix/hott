{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Language.Hott.Src
  ( Parser
  , identifier
  , reserved
  , operator
  , reservedOp
  , charLiteral
  , stringLiteral
  , natural
  , integer
  , float
  , naturalOrFloat
  , decimal
  , hexadecimal
  , octal
  , symbol
  , lexeme
  , whiteSpace
  , parens
  , braces
  , angles
  , brackets
  , squares
  , semi
  , comma
  , colon
  , dot
  , semiSep
  , semiSep1
  , commaSep
  , commaSep1
  )
where

import Control.Applicative
import Control.Monad
import Data.Bool
import Data.Char
import Data.Eq
import Data.Foldable
import Data.Kind
import Data.List.NonEmpty
import Data.Map.Strict (Map)
import Data.Maybe
import Data.Ord
import Data.Semigroup
import Data.Text (Text)
import Data.Traversable
import Data.Wedge
import GHC.Show
import Text.Parsec
import Text.Parsec.Text (Parser)
import Text.Parsec.Token qualified as Token

import Language.Hott.Syntax

tk :: (Monad m) => Token.GenTokenParser Text u m
tk@Token.TokenParser
  { identifier
  , reserved
  , operator
  , reservedOp
  , charLiteral
  , stringLiteral
  , natural
  , integer
  , float
  , naturalOrFloat
  , decimal
  , hexadecimal
  , octal
  , symbol
  , lexeme
  , whiteSpace
  , parens
  , braces
  , angles
  , brackets
  , squares
  , semi
  , comma
  , colon
  , dot
  , semiSep
  , semiSep1
  , commaSep
  , commaSep1
  } = Token.makeTokenParser do
    Token.LanguageDef
      { caseSensitive = True
      , commentStart = "{-"
      , commentEnd = "-}"
      , commentLine = "{}"
      , nestedComments = True
      , identStart = satisfy \c -> isLetter c || c == '_'
      , identLetter = satisfy \c -> isAlphaNum c || c == '_'
      , opStart = satisfy \c -> isSymbol c || (c /= ',' && isPunctuation c)
      , opLetter = satisfy \c -> isSymbol c || (c /= ',' && isPunctuation c)
      , reservedNames =
          [ "scope"
          , "using"
          , "by"
          , "let"
          , "where"
          , "_"
          ]
      , reservedOpNames =
          [ ":"
          , "="
          , "->"
          , "<-"
          , "**"
          , "∏" -- shift-option-P
          , "∑" -- option-W
          ]
      }

type Src :: Type -> (Type -> Type) -> Type
data Src l m
  = SrcScope Name [Src l m]
  | SrcData Name (m l) (m [m l])
  | SrcExpression (m l)
  | SrcPattern (m l)

class (MonadInfer l m) => MonadSource l m where
  source :: Src l m -> m ()

instance (MonadInfer Point m) => MonadSource Point m where
  source :: Src Point m -> m ()
  source = \case
    SrcScope scope src -> do
      traverse_ source src
    SrcData name point impl -> do
      _
    SrcExpression expr -> do
      _
    SrcPattern patt -> do
      _
