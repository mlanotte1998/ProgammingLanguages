{-|
Module      : Syntax
Description : Abstract syntax of protoScheme
Copyright   : (c) Ferd, 2020
                  Michael Lanotte, 2020
                  Rachel Johanek, 2020
Maintainer  : f.vesely@northeastern
              lanotte.m@northeastern.edu
              johanek.r@northeastern.edu

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
{- 
 Only need to add a Float pattern of type double into the protoScheme syntax. 
 But to make eval work, need eval to return either an Integer or a Double now. 
 To do this, need to use the Either term with Maybe Double and Maybe Integer
 And for that to work, subst needs to take in a Integer or Double now as well. 
 To do this, need to use the Either term with Double and Integer. 
 Considered making our own datatype to act as either a Integer or a Double but
 after researching more on Haskell and how Either worked, it made more sense
 to go with the data type that is already available. 
-}
data Expr = Integer Integer
          | Float Double
          | Var Variable
          | Add Expr Expr
          | Sub Expr Expr
          | Mul Expr Expr
          | Div Expr Expr
          | Let Variable Expr Expr
          deriving (Eq, Show)

-- |Parse an s-expression and convert it into a protoScheme expression.
-- Need to have the S.Symbol x last to account for where there should be let because
-- pattern matching tells us that that symbol is not one of the four operation symbols. 
fromSExpression :: S.Expr -> Expr
fromSExpression (S.Integer i) = Integer i
fromSExpression (S.Real r) = Float r
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
    test "fromSExpression Test Variable" (fromSExpression $ S.Symbol "v") (Var "v")

    test "Integer fromSExpression 42" (fromSExpression $ S.Integer 42) (Integer 42)

    test "Integer fromSExpression Test Add" (fromSExpression $ S.List [S.Symbol "+",
     S.Integer 4, S.Integer 10]) (Add (Integer 4) (Integer 10))

    test "Integer fromSExpression Test Sub" (fromSExpression $ S.List [S.Symbol "-",
     S.Integer 4, S.Integer 10]) (Sub (Integer 4) (Integer 10))

    test "Integer fromSExpression Test Mul" (fromSExpression $ S.List [S.Symbol "*",
     S.Integer 4, S.Integer 10]) (Mul (Integer 4) (Integer 10))

    test "Integer fromSExpression Test Div" (fromSExpression $ S.List [S.Symbol "/",
     S.Integer 4, S.Integer 10]) (Div (Integer 4) (Integer 10))

    test "Integer fromSExpression Test Nested Operations" (fromSExpression $ S.List [S.Symbol "/",
     S.List [S.Symbol "+", S.Integer 4, S.Integer 10], S.List [S.Symbol "-",
      S.Integer 4, S.Integer 10]]) (Div (Add (Integer 4) (Integer 10))
       (Sub (Integer 4) (Integer 10)))

    test "Integer fromSExpression Test Let  Simple" (fromSExpression $ S.List [S.Symbol "x",
     S.List [S.Symbol "+", S.Integer 10, S.Integer 4], S.List [S.Symbol "+", S.Symbol "x", S.Integer 1]])
     (Let "x" (Add (Integer 10) (Integer 4)) (Add (Var "x") (Integer 1)))

    test "Integer fromSExpression Test Let Complex" (fromSExpression $ S.List [S.Symbol "y",
     S.List [S.Symbol "-", S.Integer 20, S.Integer 8], S.List [S.Symbol "x",
      S.List [S.Symbol "+", S.Symbol "y", S.Integer 4], S.List [S.Symbol "+",
       S.Symbol "x", S.Integer 1]]]) (Let "y" (Sub (Integer 20) (Integer 8))
       (Let "x" (Add (Var "y") (Integer 4)) (Add (Var "x") (Integer 1))))

    test "Real fromSExpression 42" (fromSExpression $ S.Real 42.0) (Float 42.0)

    test "Real fromSExpression Test Add" (fromSExpression $ S.List [S.Symbol "+",
     S.Real 4.1, S.Real 10.1]) (Add (Float 4.1) (Float 10.1))

    test "Real fromSExpression Test Sub" (fromSExpression $ S.List [S.Symbol "-",
     S.Real 4.1, S.Real 10.1]) (Sub (Float 4.1) (Float 10.1))

    test "Real fromSExpression Test Mul" (fromSExpression $ S.List [S.Symbol "*",
     S.Real 4.1, S.Real 10.1]) (Mul (Float 4.1) (Float 10.1))

    test "Real fromSExpression Test Div" (fromSExpression $ S.List [S.Symbol "/",
     S.Real 4.1, S.Real 10.1]) (Div (Float 4.1) (Float 10.1))

    test "Real fromSExpression Test Nested Operations" (fromSExpression $ S.List [S.Symbol "/",
     S.List [S.Symbol "+", S.Real 4.1, S.Real 10.1], S.List [S.Symbol "-",
      S.Real 4.1, S.Real 10.1]]) (Div (Add (Float 4.1) (Float 10.1))
       (Sub (Float 4.1) (Float 10.1)))

    test "Real fromSExpression Test Let  Simple" (fromSExpression $ S.List [S.Symbol "x",
     S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]])
     (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1)))

    test "Real fromSExpression Test Let Complex" (fromSExpression $ S.List [S.Symbol "y",
     S.List [S.Symbol "-", S.Real 20.1, S.Real 8.1], S.List [S.Symbol "x",
      S.List [S.Symbol "+", S.Symbol "y", S.Real 4.1], S.List [S.Symbol "+",
       S.Symbol "x", S.Real 1.1]]]) (Let "y" (Sub (Float 20.1) (Float 8.1))
       (Let "x" (Add (Var "y") (Float 4.1)) (Add (Var "x") (Float 1.1))))

    test "Mixed fromSExpression 42" (fromSExpression $ S.Real 42.0) (Float 42.0)

    test "Mixed fromSExpression Test Add" (fromSExpression $ S.List [S.Symbol "+",
     S.Real 4.1, S.Real 10.1]) (Add (Float 4.1) (Float 10.1))

    test "Mixed fromSExpression Test Sub" (fromSExpression $ S.List [S.Symbol "-",
     S.Real 4.1, S.Real 10.1]) (Sub (Float 4.1) (Float 10.1))

    test "Mixed fromSExpression Test Mul" (fromSExpression $ S.List [S.Symbol "*",
     S.Real 4.1, S.Real 10.1]) (Mul (Float 4.1) (Float 10.1))

    test "Mixed fromSExpression Test Div" (fromSExpression $ S.List [S.Symbol "/",
     S.Real 4.1, S.Real 10.1]) (Div (Float 4.1) (Float 10.1))

    test "Mixed fromSExpression Test Nested Operations" (fromSExpression $ S.List [S.Symbol "/",
     S.List [S.Symbol "+", S.Real 4.1, S.Real 10.1], S.List [S.Symbol "-",
      S.Real 4.1, S.Real 10.1]]) (Div (Add (Float 4.1) (Float 10.1))
       (Sub (Float 4.1) (Float 10.1)))

    test "Mixed fromSExpression Test Let  Simple" (fromSExpression $ S.List [S.Symbol "x",
     S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]])
     (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1)))

    test "Mixed fromSExpression Test Let Complex" (fromSExpression $ S.List [S.Symbol "y",
     S.List [S.Symbol "-", S.Real 20.1, S.Real 8.1], S.List [S.Symbol "x",
      S.List [S.Symbol "+", S.Symbol "y", S.Real 4.1], S.List [S.Symbol "+",
       S.Symbol "x", S.Real 1.1]]]) (Let "y" (Sub (Float 20.1) (Float 8.1))
       (Let "x" (Add (Var "y") (Float 4.1)) (Add (Var "x") (Float 1.1))))   


-- |Convert a protoScheme expression into its s-expression representation
toSExpression :: Expr -> S.Expr
toSExpression (Integer i) = S.Integer i 
toSExpression (Float f) = S.Real f 
toSExpression (Var v) = S.Symbol v 
toSExpression (Add x y) = S.List [S.Symbol "+", toSExpression x, toSExpression y]
toSExpression (Sub x y) = S.List [S.Symbol "-", toSExpression x, toSExpression y]
toSExpression (Mul x y) = S.List [S.Symbol "*", toSExpression x, toSExpression y]
toSExpression (Div x y) = S.List [S.Symbol "/", toSExpression x, toSExpression y]
toSExpression (Let v x y) = S.List [S.Symbol v, toSExpression x, toSExpression y]

test_toSExpression = do
    --Base cases
    test "toSExpression (10)" (toSExpression (Integer 10)) (S.Integer 10)
    test "toSExpression (10.1)" (toSExpression (Float 10.1)) (S.Real 10.1)
    test "toSExpression (Var x)" (toSExpression (Var "x")) (S.Symbol "x")

    --Addition with Integers and Reals
    test "toSExpression (+ 32 14)"
        (toSExpression $ Add (Integer 32) (Integer 14))
        (S.List [S.Symbol "+", S.Integer 32, S.Integer 14])
    test "toSExpression (+ 32.1 14)"
        (toSExpression $ Add (Float 32.1) (Integer 14))
        (S.List [S.Symbol "+", S.Real 32.1, S.Integer 14])
    test "toSExpression (+ 32.1 14.5)"
        (toSExpression $ Add (Float 32.1) (Float 14.5))
        (S.List [S.Symbol "+", S.Real 32.1, S.Real 14.5])

    --Subtraction with Integers and Reals
    test "toSExpression (- 32 14)"
        (toSExpression $ Sub (Integer 32) (Integer 14))
        (S.List [S.Symbol "-", S.Integer 32, S.Integer 14])
    test "toSExpression (- 32.1 14)"
        (toSExpression $ Sub (Float 32.1) (Integer 14))
        (S.List [S.Symbol "-", S.Real 32.1, S.Integer 14])
    test "toSExpression (- 32.1 14.5)"
        (toSExpression $ Sub (Float 32.1) (Float 14.5))
        (S.List [S.Symbol "-", S.Real 32.1, S.Real 14.5])
    
    --Multiplication with Integers and Reals
    test "toSExpression (* 10 5)"
        (toSExpression $ Mul (Integer 10) (Integer 5))
        (S.List [S.Symbol "*", S.Integer 10, S.Integer 5])
    test "toSExpression (* 10.2 5)"
        (toSExpression $ Mul (Float 10.2) (Integer 5))
        (S.List [S.Symbol "*", S.Real 10.2, S.Integer 5])
    test "toSExpression (* 10.2 5.6)"
        (toSExpression $ Mul (Float 10.2) (Float 5.6))
        (S.List [S.Symbol "*", S.Real 10.2, S.Real 5.6])

    --Division with Integers and Reals
    test "toSExpression (/ 10 5)"
        (toSExpression $ Div (Integer 10) (Integer 5))
        (S.List [S.Symbol "/", S.Integer 10, S.Integer 5])
    test "toSExpression (/ 10.2 5)"
        (toSExpression $ Div (Float 10.2) (Integer 5))
        (S.List [S.Symbol "/", S.Real 10.2, S.Integer 5])
    test "toSExpression (/ 10.2 5.6)"
        (toSExpression $ Div (Float 10.2) (Float 5.6))
        (S.List [S.Symbol "/", S.Real 10.2, S.Real 5.6])

    --Nested functions with Integers and Reals
    test "toSExpression (/ (+ 10 10) (* 5 2)"
        (toSExpression (Div (Add (Integer 10) (Integer 10)) (Mul (Integer 5) (Integer 2))))
        (S.List [S.Symbol "/", (S.List [S.Symbol "+", S.Integer 10, S.Integer 10]),
          (S.List [S.Symbol "*", S.Integer 5, S.Integer 2])])
    test "toSExpression (/ (+ 10.2 10) (- 5 2.1)"
        (toSExpression $ Div (Add (Float 10.2) (Integer 10)) (Sub (Integer 5) (Float 2.1)))
        (S.List [S.Symbol "/", (S.List [S.Symbol "+", S.Real 10.2, S.Integer 10]),
          (S.List [S.Symbol "-", S.Integer 5, S.Real 2.1])])
    test "toSExpression (+ (* 10.2 10.8) (- 5.7 2.1)"
        (toSExpression $ Add (Mul (Float 10.2) (Float 10.8)) (Sub (Float 5.7) (Float 2.1)))
        (S.List [S.Symbol "+", (S.List [S.Symbol "*", S.Real 10.2, S.Real 10.8]),
          (S.List [S.Symbol "-", S.Real 5.7, S.Real 2.1])])


-- |Convert an evaluation result into s-expression
valueToSExpression :: Either Double Integer -> S.Expr
valueToSExpression (Left i) = S.Real i
valueToSExpression (Right i) = S.Integer i

test_valueToSExpression = do
    test "toSExpression 42"
        (valueToSExpression (Right 42))
        (S.Integer 42)
    test "toSExpression 42.3"
        (valueToSExpression (Left 42.3))
        (S.Real 42.3)
    test "toSExpression 20"
        (valueToSExpression (Right 20))
        (S.Integer 20)
    test "toSExpression 51.9"
        (valueToSExpression (Left 51.9))
        (S.Real 51.9)
