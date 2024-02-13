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

import Control.Monad
import Data.Bool
import Data.Char
import Data.Eq
import Data.Kind
import Data.List.NonEmpty
import Data.Maybe
import Data.Ord
import Data.Semigroup
import Data.Text (Text)
import Data.These
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

-- |
-- 'Pos' has an 'Eq' instance that ignores the 'SourcePos',
-- but an 'Ord' instance that sorts by 'SourcePos' first. Be careful!
type Pos :: Type -> Type
data Pos x = Pos
  { pos :: SourcePos
  , __ :: x
  }
  deriving (Show, Functor)

instance (Eq x) => Eq (Pos x) where
  x == y = x.__ == y.__
instance (Ord x) => Ord (Pos x) where
  compare p0 p1 = compare p0.pos p1.pos <> compare p0.__ p1.__

type Import :: Type -> (Type -> Type) -> Type
data Import l m = Import
  { scope :: Name
  , qual :: Maybe Name
  , names :: These (NonEmpty Name) (NonEmpty Name)
  }

type Data :: Type -> (Type -> Type) -> Type
data Data l m = Data
  { term :: m l
  , impl :: m [m l]
  }

type Src :: Type -> (Type -> Type) -> Type
data Src l m
  = SrcScope (Pos (Var [Src l m]))
  | SrcImport (Pos (Import l m))
  | SrcData (Pos (Var (Data l m)))
  | SrcExpression (Pos (m l))
  | SrcPattern (Pos (m l))

class (MonadInfer l m) => MonadSource l m where
  source :: Src l m -> m ()
