{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Language.Hott.Source
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

import Control.Monad
import Control.Monad.Interpret
import Data.Bool
import Data.Char
import Data.Eq
import Data.Semigroup
import Data.Text (Text)
import Text.Parsec
import Text.Parsec.Text (Parser)
import Text.Parsec.Token qualified as Token

import Language.Hott.Structure ((===))
import Language.Hott.Structure qualified as Hott

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

data Source p
  = Data Text p p
  | Expression p
  | Pattern p

class (MonadInterpret e n p m) => MonadSource e n p m where
  source :: Text -> Source p -> m ()

instance MonadSource Hott.E Hott.N Hott.P Hott.M where
  source :: Text -> Source Hott.P -> Hott.M ()
  source scope = \case
    Data a ta impl -> do
      ta === infer impl
      acknowledge (Var (scope <> "." <> a) ta)
    Expression x -> do
      tx <- infer x
      l <- fresh
      acknowledge (Var (scope <> "." <> l) tx)
    Pattern p -> do
      tp <- infer p
      l <- fresh
      acknowledge (Var (scope <> "." <> l) tp)
