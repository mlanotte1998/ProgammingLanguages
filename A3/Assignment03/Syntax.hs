{-|
Module      : Syntax
Description : Abstract syntax of protoScheme
Copyright   : (c) Ferd, 2020
                  <add your name(s)>, 2020
Maintainer  : f.vesely@northeastern
              <email1>
              <email2>

This module defines the abstract syntax of protoScheme and related functions.
-}
module Syntax where

{- TODO:
 -   * Redesign the abstract syntax to accommodate floats
 -   * Complete the missing clauses in 'fromSExpression'
 -   * Implement 'toSExpression'
 -   * Fix the type and implementation of 'valueToSExpression'
 -   * Write tests & examples
 -   * Write more test
 -}

import qualified SExpression as S

import SimpleTests (test)

-- |Variables are just strings
type Variable = String

-- |protoScheme expressions
data Expr = Integer Integer
          | Var Variable
          | Add Expr Expr
          | Sub Expr Expr
          | Mul Expr Expr
          | Div Expr Expr
          | Let Variable Expr Expr
          deriving (Eq, Show)

-- |Parse an s-expression and convert it into a protoScheme expression.
fromSExpression :: S.Expr -> Expr
fromSExpression (S.Integer i) = Integer i
fromSExpression (S.List [S.Symbol "+", e1, e2]) =
    Add (fromSExpression e1) (fromSExpression e2)
fromSExpression (S.List [S.Symbol "-", e1, e2]) =
    Sub (fromSExpression e1) (fromSExpression e2)
fromSExpression (S.List [S.Symbol "*", e1, e2]) =
    Mul (fromSExpression e1) (fromSExpression e2)
fromSExpression (S.List [S.Symbol "/", e1, e2]) =
    Div (fromSExpression e1) (fromSExpression e2)
fromSExpression (S.List [S.Symbol x, e1, e2]) =
    Let x (fromSExpression e1) (fromSExpression e2)
fromSExpression (S.Symbol s) =
    Var s

test_fromSExpression = do
    test "fromSExpression 42" (fromSExpression $ S.Integer 42) (Integer 42)

    test "fromSExpression Test Variable" (fromSExpression $ S.Symbol "v") (Var "v")

    test "fromSExpression Test Add" (fromSExpression $ S.List [S.Symbol "+",
     S.Integer 4, S.Integer 10]) (Add (Integer 4) (Integer 10))

    test "fromSExpression Test Sub" (fromSExpression $ S.List [S.Symbol "-",
     S.Integer 4, S.Integer 10]) (Sub (Integer 4) (Integer 10))

    test "fromSExpression Test Mul" (fromSExpression $ S.List [S.Symbol "*",
     S.Integer 4, S.Integer 10]) (Mul (Integer 4) (Integer 10))

    test "fromSExpression Test Div" (fromSExpression $ S.List [S.Symbol "/",
     S.Integer 4, S.Integer 10]) (Div (Integer 4) (Integer 10))

    test "fromSExpression Test Nested Operations" (fromSExpression $ S.List [S.Symbol "/",
     S.List [S.Symbol "+", S.Integer 4, S.Integer 10], S.List [S.Symbol "-",
      S.Integer 4, S.Integer 10]]) (Div (Add (Integer 4) (Integer 10))
       (Sub (Integer 4) (Integer 10)))

    test "fromSExpression Test Let  Simple" (fromSExpression $ S.List [S.Symbol "x",
     S.List [S.Symbol "+", S.Integer 10, S.Integer 4], S.List [S.Symbol "+", S.Symbol "x", S.Integer 1]])
     (Let "x" (Add (Integer 10) (Integer 4)) (Add (Var "x") (Integer 1)))

    test "fromSExpression Test Let Complex" (fromSExpression $ S.List [S.Symbol "y",
     S.List [S.Symbol "-", S.Integer 20, S.Integer 8], S.List [S.Symbol "x",
      S.List [S.Symbol "+", S.Symbol "y", S.Integer 4], S.List [S.Symbol "+",
       S.Symbol "x", S.Integer 1]]]) (Let "y" (Sub (Integer 20) (Integer 8))
       (Let "x" (Add (Var "y") (Integer 4)) (Add (Var "x") (Integer 1))))



-- |Convert a protoScheme expression into its s-expression representation
toSExpression :: Expr -> S.Expr
toSExpression _ = undefined

test_toSExpression = do
    test "toSExpression (+ 32 14)"
        (toSExpression $ Add (Integer 32) (Integer 14))
        (S.List [S.Symbol "+", S.Integer 32, S.Integer 14])

-- |Convert an evaluation result into s-expression
valueToSExpression :: Integer -> S.Expr
valueToSExpression i = S.Integer i

test_valueToSExpression = do
    test "toSExpression 42"
        (valueToSExpression 42)
        (S.Integer 42)
