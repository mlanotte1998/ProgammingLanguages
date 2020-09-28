{-|
Module      : Eval
Description : Semantics of protoScheme
Copyright   : (c) Ferd, 2020
                  <add your name(s)>, 2020
Maintainer  : f.vesely@northeastern
              <email1>
              <email2>

This module provides the evaluator of the protoScheme language.

-}
module Eval where

{- TODO:
 -   * Fix the type signatures and modify 'eval' and 'subst' to accommodate a
 -     new type of values
 -   * Write tests
 -   * Write more tests
 -}

import Syntax

import qualified SExpression as S

import SimpleTests (test)


-- |Evaluates the given expression to a value.
eval :: Expr -> Maybe Integer
eval (Integer i) = Just i
eval (Var _) = Nothing
eval (Add e1 e2) =
    case eval e1 of
         Just v1 ->
            case eval e2 of
                 Just v2 -> Just (v1 + v2)
                 Nothing -> Nothing
         Nothing -> Nothing
eval (Sub e1 e2) =
    case eval e1 of
         Just v1 ->
            case eval e2 of
                 Just v2 -> Just (v1 - v2)
                 Nothing -> Nothing
         Nothing -> Nothing
eval (Mul e1 e2) =
    case eval e1 of
         Just v1 ->
            case eval e2 of
                 Just v2 -> Just (v1 * v2)
                 Nothing -> Nothing
         Nothing -> Nothing
eval (Div e1 e2) =
    case eval e1 of
         Just v1 ->
            case eval e2 of
                 Just 0 -> Nothing
                 Just v2 -> Just (v1 `div` v2)
                 Nothing -> Nothing
         Nothing -> Nothing
eval (Let x e1 e2) =
    case eval e1 of
         Just v1 -> eval (subst x v1 e2)
         Nothing -> Nothing

test_eval = do
    test "eval: (+ 12 30)" (eval (Add (Integer 12) (Integer 30))) (Just 42)

    test "eval: (let (x (+1 2)) (* 4 x))"
       (eval $ Let "x" (Add (Integer 1) (Integer 2)) (Mul (Integer 4) (Var "x")))
       (Just 12)

    test "eval not assigned Var Test 1" (eval $ Var "x") Nothing

    test "eval not assigned Var Test 2" (eval $ Add (Integer 2) (Var "x")) Nothing

    test "eval: simple Integer test" (eval $ Integer 11) (Just 11)

    test "eval: (- 30 12)" (eval $ Sub (Integer 30) (Integer 12)) (Just 18)

    test "eval: (* 30 12)" (eval $ Mul (Integer 30) (Integer 12)) (Just 360)

    test "eval: (/ 30 12)" (eval $ Div (Integer 30) (Integer 12)) (Just 2)

    test "eval: (* (+ 5 10) (- 5 4))" (eval $ Mul (Add (Integer 5) (Integer 10))
     (Sub (Integer 5) (Integer 4))) (Just 15)

    test "eval: nested let" (eval $ Let "y" (Sub (Integer 20) (Integer 8))
     (Let "y" (Add (Var "x") (Integer 4)) (Add (Var "x") (Integer 1)))) (Just 17)



-- |Substitutes the given value for the given variable in the given expression.
subst :: Variable -> Integer -> Expr -> Expr
subst _ _ (Integer n) = Integer n
subst x v (Var y) | x == y = Integer v
                  | otherwise = Var y
subst x v (Add e1 e2) = Add (subst x v e1) (subst x v e2)
subst x v (Sub e1 e2) = Sub (subst x v e1) (subst x v e2)
subst x v (Mul e1 e2) = Mul (subst x v e1) (subst x v e2)
subst x v (Div e1 e2) = Div (subst x v e1) (subst x v e2)
subst x v (Let y e1 e2) | x == y = Let y (subst x v e1) e2
                        | otherwise = Let y (subst x v e1) (subst x v e2)


test_subst = do
    test "subst x 42 x" (subst "x" 42 (Var "x")) (Integer 42)

    test "subst x 42 y" (subst "x" 42 (Var "y")) (Var "y")

    test "subst Add Test Simple" (subst "x" 10 (Add (Integer 20) (Integer 4)))
     (Add (Integer 20) (Integer 4))

    test "subst Add Test Complex" (subst "x" 10 (Add (Var "x") (Integer 4)))
     (Add (Integer 10) (Integer 4))

    test "subst Sub Test Simple" (subst "x" 10 (Sub (Integer 20) (Integer 4)))
     (Sub (Integer 20) (Integer 4))

    test "subst Sub Test Complex" (subst "x" 10 (Sub (Var "x") (Integer 4)))
     (Sub (Integer 10) (Integer 4))

    test "subst Mul Test Simple" (subst "x" 10 (Mul (Integer 20) (Integer 4)))
     (Mul (Integer 20) (Integer 4))

    test "subst Mul Test Complex" (subst "x" 10 (Mul (Var "x") (Integer 4)))
     (Mul (Integer 10) (Integer 4))

    test "subst Div Test Simple" (subst "x" 10 (Div (Integer 20) (Integer 4)))
     (Div (Integer 20) (Integer 4))

    test "subst Div Test Complex" (subst "x" 10 (Div (Var "x") (Integer 4)))
     (Div (Integer 10) (Integer 4))

    test "subst nested variable Test" (subst "x" 10 (Div
     (Sub (Integer 10) (Var "x")) (Add (Var "y") (Integer 15))))
      (Div (Sub (Integer 10) (Integer 10)) (Add (Var "y") (Integer 15)))

    test "subst let Test 1" (subst "x" 10
     (Let "x" (Add (Var "x") (Integer 6)) (Sub (Var "x") (Integer 16))))
      (Let "x" (Add (Integer 10) (Integer 6)) (Sub (Var "x") (Integer 16)))

    test "subst let Test 2" (subst "x" 10
     (Let "y" (Add (Var "y") (Integer 6)) (Sub (Var "x") (Integer 16))))
      (Let "y" (Add (Var "y") (Integer 6)) (Sub (Integer 10) (Integer 16)))

    test "subst let Test 3" (subst "x" 10
     (Let "y" (Add (Var "x") (Integer 6)) (Sub (Var "x") (Integer 16))))
      (Let "y" (Add (Integer 10) (Integer 6)) (Sub (Integer 10) (Integer 16)))



-- |Run the given protoScheme s-expression, returning an s-expression
-- representation of the result.
runSExpression :: S.Expr -> Maybe S.Expr
runSExpression se =
    case eval (fromSExpression se) of
         Just v -> Just (valueToSExpression v)
         Nothing -> Nothing

test_runSExpression = do
    test "run: (+ 1 2)"
        (runSExpression $ S.List [S.Symbol "+", S.Integer 1, S.Integer 2])
        (Just $ S.Integer 3)
