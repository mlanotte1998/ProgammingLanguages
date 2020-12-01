{-|
Module      : Types
Description : Types for protoScheme
Copyright   : (c) Ferd, 2020
Maintainer  : f.vesely@northeastern

Types used in protoScheme.

This module defines the type language of protoScheme. Types have the following syntax:

> <BaseType> ::= Integer
>              | Real
>              | Boolean
>
> <Type> ::= <BaseType>
>          | (-> <Type>+)
>          | (Pair-of <Type> <Type>)
>          | (All (<TypeVariable>+) <Type>)
>          | <TypeVariable>

-}
module Types 
    ( BaseType (..)
    , Type(..)
    , fromSExpression
    , toSExpression
    , showType
    ) where

import Result

import qualified SExpression as S

-- |Base types
data BaseType = TyInteger
              | TyReal
              | TyBoolean
              deriving (Show, Eq)

-- |protoScheme types
data Type = TyBase BaseType         -- ^Base types
          | TyArrow [Type]          -- ^Function type
          | TyPair Type Type        -- ^Pair type
          deriving (Show, Eq)

-- |Convert an s-expression into a type, if possible.
fromSExpression :: S.Expr -> Result Type
fromSExpression (S.Symbol "Integer") = return $ TyBase TyInteger
fromSExpression (S.Symbol "Real") = return $ TyBase TyReal
fromSExpression (S.Symbol "Boolean") = return $ TyBase TyBoolean
fromSExpression (S.List (S.Symbol "->" : ses )) = TyArrow <$> mapM fromSExpression ses
fromSExpression (S.List [ S.Symbol "Pair-of", se1, se2 ]) = 
    TyPair <$> fromSExpression se1 <*> fromSExpression se2
fromSExpression _ = fail "Given s-expression cannot be parsed as a type"

-- |Convert a type into an s-expression.
toSExpression :: Type -> S.Expr
toSExpression (TyBase b) = S.Symbol $ base b
  where
    base TyInteger = "Integer"
    base TyReal = "Real"
    base TyBoolean = "Boolean"
toSExpression (TyArrow tys) =
    S.List $ S.Symbol "->" : map toSExpression tys
toSExpression (TyPair ty1 ty2) = 
    S.List [ S.Symbol "Pair-of", toSExpression ty1, toSExpression ty2 ]

-- |Pretty print a type as its s-expression representation
showType :: Type -> String
showType = S.toString . toSExpression

