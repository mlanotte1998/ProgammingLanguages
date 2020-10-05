{-|
Module      : SExpression
Description : Syntax of s-expressions
Copyright   : (c) Ferd, 2020
Maintainer  : f.vesely@northeastern

This module provides the abstract syntax and functions for manipulating 
s-expressions.

-}
module SExpression 
    ( Expr (..)
    , toString
    ) where

import SimpleTests (test)

-- |Abstract syntax of s-expressions
data Expr = Integer Integer
          | Real Double
          | Boolean Bool
          | Symbol String
          | List [Expr]
          deriving (Eq, Show)

ex_expr1 = Integer 42
ex_expr2 = Real (-3.14)
ex_expr3 = List [Integer 1, Symbol "foo"]
ex_expr4 = List [Integer 1, List [Symbol "a", Symbol "b"], Symbol "foo"]
ex_expr5 = List [ Symbol "+"
                , List [ Symbol "-"
                       , Symbol "x"
                       , Integer 4
                       ]
                , List [ Symbol "*"
                       , Real 5.32517
                       , Symbol "y"
                       ]
                ]
ex_expr6 = Boolean False

-- |Pretty-print the given s-expression.
toString :: Expr -> String
toString (Integer i) = show i
toString (Real d) = show d
toString (Boolean b) | b = "#t"
                     | not b = "#f"
toString (Symbol sym) = sym
toString (List es) = "(" ++ listToString es ++ ")"
  where
    listToString :: [Expr] -> String
    listToString [] = ""
    listToString [e] = toString e
    listToString (e : es) = toString e ++ " " ++ listToString es

test_toString :: IO ()
test_toString = do 
    test "toString: integer" (toString $ Integer 42) "42"
    test "toString: real" (toString $ Real (-3.14)) "-3.14"
    test "toString: symbol foo" (toString $ Symbol "foo") "foo"
    test "toString: symbol +" (toString $ Symbol "+") "+"
    test "toString: ()" (toString $ List []) "()"
    test "toString: (1)" (toString $ List [Integer 1]) "(1)"
    test "toString: (1 foo)" (toString $ List [Integer 1, Symbol "foo"]) "(1 foo)"
    test "toString: (1 (a b) foo)" (toString ex_expr4) "(1 (a b) foo)"
    test "toString: (+ (- x 4) (* 5.32517 y))" 
        (toString ex_expr5) 
        "(+ (- x 4) (* 5.32517 y))"
    test "toString (Boolean True)" (toString $ Boolean True) "#t"
    test "toString (Boolean False)" (toString $ Boolean False) "#f"

