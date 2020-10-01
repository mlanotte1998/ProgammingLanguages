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


type MaybeInt = Maybe Integer 
type MaybeFloat = Maybe Double

-- |Evaluates the given expression to a value.
{- Changed type signuture to handle either an Integer or a Double
   Decided to use Either to return both. 
   For consistency, made both the left and right of the either be a "Maybe" type 
   even though we only return Left Nothings. Could potentially update further
   to have Right Nothing if all of the parts were integers and then if there is a Nothing
   along with at least one double then it would be a Left Nothing. But for now we did not
   deem that necessary.      
-}
eval :: Expr -> Either (Maybe Double) (Maybe Integer)
eval (Integer i) = Right (Just i)
eval (Float d) = Left (Just d)
eval (Var _) = Left Nothing
eval (Add e1 e2) =
    case eval e1 of
         Left (Just v1) ->
            case eval e2 of
                 Left (Just v2) -> Left (Just (v1 + v2))
                 Right (Just v2) -> Left (Just (v1 + (fromInteger v2)))
                 Left Nothing -> Left Nothing
         Right (Just v1) -> 
            case eval e2 of 
                 Left (Just v2) -> Left (Just ((fromInteger v1) + v2))
                 Right (Just v2) -> Right (Just (v1 + v2))
                 Left Nothing -> Left Nothing
         Left Nothing -> Left Nothing        
eval (Sub e1 e2) =
    case eval e1 of
         Left (Just v1) ->
            case eval e2 of
                 Left (Just v2) -> Left (Just (v1 - v2))
                 Right (Just v2) -> Left (Just (v1 - (fromInteger v2)))
                 Left Nothing -> Left Nothing
         Right (Just v1) -> 
            case eval e2 of 
                 Left (Just v2) -> Left (Just ((fromInteger v1) - v2))
                 Right (Just v2) -> Right (Just (v1 - v2))
                 Left Nothing -> Left Nothing
         Left Nothing -> Left Nothing        
eval (Mul e1 e2) =
    case eval e1 of
         Left (Just v1) ->
            case eval e2 of
                 Left (Just v2) -> Left (Just (v1 * v2))
                 Right (Just v2) -> Left (Just (v1 * (fromInteger v2)))
                 Left Nothing -> Left Nothing
         Right (Just v1) -> 
            case eval e2 of 
                 Left (Just v2) -> Left (Just ((fromInteger v1) * v2))
                 Right (Just v2) -> Right (Just (v1 * v2))
                 Left Nothing -> Left Nothing
         Left Nothing -> Left Nothing        
eval (Div e1 e2) =
    case eval e1 of
         Left (Just v1) ->
            case eval e2 of
                 Left (Just v2) -> Left (Just (v1 / v2))
                 Right (Just v2) -> Left (Just (v1 / (fromInteger v2)))
                 Left Nothing -> Left Nothing
         Right (Just v1) -> 
            case eval e2 of 
                 Left (Just v2) -> Left (Just ((fromInteger v1) / v2))
                 Right (Just v2) -> Right (Just (v1 `div` v2))
                 Left Nothing -> Left Nothing
         Left Nothing -> Left Nothing        
eval (Let x e1 e2) =
    case eval e1 of
         Left (Just v1) -> eval (subst x (Left v1) e2)
         Right (Just v1) -> eval (subst x (Right v1) e2)
         Left Nothing -> Left Nothing

test_eval = do
    test "Integer eval: (+ 12 30)" (eval (Add (Integer 12) (Integer 30))) (Right (Just 42))

    test "Integer eval: (let (x (+1 2)) (* 4 x))"
       (eval $ Let "x" (Add (Integer 1) (Integer 2)) (Mul (Integer 4) (Var "x")))
       (Right (Just 12))

    test "Integer eval not assigned Var Test 1" (eval $ Var "x") (Left Nothing)

    test "Integer eval not assigned Var Test 2" (eval $ Add (Integer 2) (Var "x")) (Left Nothing)

    test "Integer eval: simple Integer test" (eval $ Integer 11) (Right (Just 11))

    test "Integer eval: (- 30 12)" (eval $ Sub (Integer 30) (Integer 12)) (Right (Just 18))

    test "Integer eval: (* 30 12)" (eval $ Mul (Integer 30) (Integer 12)) (Right (Just 360))
  
    test "Integer eval: (/ 30 12)" (eval $ Div (Integer 30) (Integer 12)) (Right (Just 2))

    test "Integer eval: (* (+ 5 10) (- 5 4))" (eval $ Mul (Add (Integer 5) (Integer 10))
     (Sub (Integer 5) (Integer 4))) (Right (Just 15))

    test "Integer eval: nested let" (eval $ Let "y" (Sub (Integer 20) (Integer 8))
     (Let "x" (Add (Var "y") (Integer 4)) (Add (Var "x") (Integer 1)))) (Right (Just 17))

    -- // Float tests 

    test "Float eval: (+ 12.2 30.5)" (eval (Add (Float 12.2) (Float 30.5))) (Left (Just 42.7))

    test "Float eval: (let (x (+1.1 2.2)) (* 4.5 x))"
       (eval $ Let "x" (Add (Float 1.1) (Float 2.2)) (Mul (Float 4.5) (Var "x")))
       (Left (Just 14.850000000000001))

    test "Float eval not assigned Var Test" (eval $ Add (Float 2.5) (Var "x")) (Left Nothing)

    test "Float eval: simple Integer test" (eval $ Float 11.1) (Left (Just 11.1))

    test "Float eval: (- 30.5 12.5)" (eval $ Sub (Float 30.5) (Float 12.5)) (Left (Just 18.0))

    test "Float eval: (* 30.5 12.1)" (eval $ Mul (Float 30.5) (Float 12.1)) (Left (Just 369.05))

    test "Float eval: (/ 30.0 12.0)" (eval $ Div (Float 30.0) (Float 12.0)) (Left (Just 2.5))

    test "Float eval: (* (+ 5.5 10.5) (- 5.4 4.4))" (eval $ Mul (Add (Float 5.5) (Float 10.5))
     (Sub (Float 5.4) (Float 4.4))) (Left (Just 16.0))

    test "Float eval: nested let" (eval $ Let "y" (Sub (Float 20.2) (Float 8.4))
     (Let "x" (Add (Var "y") (Float 4.4)) (Add (Var "x") (Float 1.1)))) (Left (Just 17.3))

    -- // Mixed tests 

    test "Mixed eval: (+ 12.2 30)" (eval (Add (Float 12.2) (Integer 30))) (Left (Just 42.2))

    test "Mixed eval: (let (x (+1.1 20)) (* 4.5 x))"
       (eval $ Let "x" (Add (Float 1.1) (Integer 20)) (Mul (Integer 4) (Var "x")))
       (Left (Just 84.4))

    test "Mixed eval: (- 30.5 12)" (eval $ Sub (Float 30.5) (Integer 12)) (Left (Just 18.5))

    test "Mixed eval: (* 30.5 12)" (eval $ Mul (Float 30.5) (Integer 12)) (Left (Just 366.0))

    test "Mixed eval: (/ 32.5 10)" (eval $ Div (Float 32.5) (Float 10)) (Left (Just 3.25))

    test "Mixed eval: (* (+ 5.5 10) (- 5.4 4))" (eval $ Mul (Add (Float 5.5) (Integer 10))
     (Sub (Integer 5) (Float 4.4))) (Left (Just 9.299999999999994))

    test "Mixed eval: nested let" (eval $ Let "y" (Sub (Float 20.2) (Integer 8))
     (Let "x" (Add (Var "y") (Integer 4)) (Add (Var "x") (Float 1.1)))) (Left (Just 17.3))





-- |Substitutes the given value for the given variable in the given expression.
-- Given value can now be either a double or an integer 
subst :: Variable -> (Either Double Integer) -> Expr -> Expr
subst _ _ (Integer n) = Integer n
subst _ _ (Float n) = Float n
subst x v (Var y) | x == y = 
                      case v of 
                           Left num -> Float num 
                           Right num -> Integer num 
                  | otherwise = Var y
subst x v (Add e1 e2) = Add (subst x v e1) (subst x v e2)
subst x v (Sub e1 e2) = Sub (subst x v e1) (subst x v e2)
subst x v (Mul e1 e2) = Mul (subst x v e1) (subst x v e2)
subst x v (Div e1 e2) = Div (subst x v e1) (subst x v e2)
subst x v (Let y e1 e2) | x == y = Let y (subst x v e1) e2
                        | otherwise = Let y (subst x v e1) (subst x v e2)


test_subst = do
   -- // Integer tests
    test "subst x 42 x" (subst "x" (Right 42) (Var "x")) (Integer 42)

    test "subst x 42 y" (subst "x" (Right 42) (Var "y")) (Var "y")

    test "subst Add Test Simple" (subst "x" (Right 10) (Add (Integer 20) (Integer 4)))
     (Add (Integer 20) (Integer 4))

    test "subst Add Test Complex" (subst "x" (Right 10) (Add (Var "x") (Integer 4)))
     (Add (Integer 10) (Integer 4))

    test "subst Sub Test Simple" (subst "x" (Right 10) (Sub (Integer 20) (Integer 4)))
     (Sub (Integer 20) (Integer 4))

    test "subst Sub Test Complex" (subst "x" (Right 10) (Sub (Var "x") (Integer 4)))
     (Sub (Integer 10) (Integer 4))

    test "subst Mul Test Simple" (subst "x" (Right 10) (Mul (Integer 20) (Integer 4)))
     (Mul (Integer 20) (Integer 4))

    test "subst Mul Test Complex" (subst "x" (Right 10) (Mul (Var "x") (Integer 4)))
     (Mul (Integer 10) (Integer 4))

    test "subst Div Test Simple" (subst "x" (Right 10) (Div (Integer 20) (Integer 4)))
     (Div (Integer 20) (Integer 4))

    test "subst Div Test Complex" (subst "x" (Right 10) (Div (Var "x") (Integer 4)))
     (Div (Integer 10) (Integer 4))

    test "subst nested variable Test" (subst "x" (Right 10) (Div
     (Sub (Integer 10) (Var "x")) (Add (Var "y") (Integer 15))))
      (Div (Sub (Integer 10) (Integer 10)) (Add (Var "y") (Integer 15)))

    test "subst let Test 1" (subst "x" (Right 10)
     (Let "x" (Add (Var "x") (Integer 6)) (Sub (Var "x") (Integer 16))))
      (Let "x" (Add (Integer 10) (Integer 6)) (Sub (Var "x") (Integer 16)))

    test "subst let Test 2" (subst "x" (Right 10)
     (Let "y" (Add (Var "y") (Integer 6)) (Sub (Var "x") (Integer 16))))
      (Let "y" (Add (Var "y") (Integer 6)) (Sub (Integer 10) (Integer 16)))

    test "subst let Test 3" (subst "x" (Right 10)
     (Let "y" (Add (Var "x") (Integer 6)) (Sub (Var "x") (Integer 16))))
      (Let "y" (Add (Integer 10) (Integer 6)) (Sub (Integer 10) (Integer 16)))

    -- // Float Tests

    test "subst x 42.5 x" (subst "x" (Left 42.5) (Var "x")) (Float 42.5)

    test "subst x 42.5 y" (subst "x" (Left 42.5) (Var "y")) (Var "y")

    test "subst Add Test Simple Float" (subst "x" (Left 10.5) (Add (Integer 20) (Integer 4)))
     (Add (Integer 20) (Integer 4))

    test "subst Add Test Complex Float" (subst "x" (Left 10.5) (Add (Var "x") (Integer 4)))
     (Add (Float 10.5) (Integer 4))

    test "subst Sub Test Simple Float" (subst "x" (Left 10.5) (Sub (Integer 20) (Integer 4)))
     (Sub (Integer 20) (Integer 4))

    test "subst Sub Test Complex Float" (subst "x" (Left 10.5) (Sub (Var "x") (Integer 4)))
     (Sub (Float 10.5) (Integer 4))

    test "subst Mul Test Simple Float" (subst "x" (Left 10.5) (Mul (Integer 20) (Integer 4)))
     (Mul (Integer 20) (Integer 4))

    test "subst Mul Test Complex Float" (subst "x" (Left 10.5) (Mul (Var "x") (Integer 4)))
     (Mul (Float 10.5) (Integer 4))

    test "subst Div Test Simple Float" (subst "x" (Left 10.5) (Div (Integer 20) (Integer 4)))
     (Div (Integer 20) (Integer 4))

    test "subst Div Test Complex Float" (subst "x" (Left 10.5) (Div (Var "x") (Integer 4)))
     (Div (Float 10.5) (Integer 4))

    test "subst nested variable Test Float" (subst "x" (Left 10.5) (Div
     (Sub (Integer 10) (Var "x")) (Add (Var "y") (Integer 15))))
      (Div (Sub (Integer 10) (Float 10.5)) (Add (Var "y") (Integer 15)))

    test "subst let Test 1 Float" (subst "x" (Left 10.5)
     (Let "x" (Add (Var "x") (Integer 6)) (Sub (Var "x") (Integer 16))))
      (Let "x" (Add (Float 10.5) (Integer 6)) (Sub (Var "x") (Integer 16)))

    test "subst let Test 2" (subst "x" (Left 10.5)
     (Let "y" (Add (Var "y") (Integer 6)) (Sub (Var "x") (Integer 16))))
      (Let "y" (Add (Var "y") (Integer 6)) (Sub (Float 10.5) (Integer 16)))

    test "subst let Test 3" (subst "x" (Left 10.5)
     (Let "y" (Add (Var "x") (Integer 6)) (Sub (Var "x") (Integer 16))))
      (Let "y" (Add (Float 10.5) (Integer 6)) (Sub (Float 10.5) (Integer 16)))



-- |Run the given protoScheme s-expression, returning an s-expression
-- representation of the result.
runSExpression :: S.Expr -> Maybe S.Expr
runSExpression se =
    case eval (fromSExpression se) of
         Left (Just v)-> Just (valueToSExpression (Left v))
         Right (Just v)-> Just (valueToSExpression (Right v))
         Right Nothing -> Nothing
         Left Nothing -> Nothing

test_runSExpression = do

    test "run: (+ 1 2)"
        (runSExpression $ S.List [S.Symbol "+", S.Integer 1, S.Integer 2])
        (Just $ S.Integer 3)

    test "runSExpression Test Variable" (runSExpression $ S.Symbol "v") (Nothing)

    test "Integer runSExpression 42" (runSExpression $ S.Integer 42) (Just (S.Integer 42))

    test "Integer runSExpression Test Add" (runSExpression $ S.List [S.Symbol "+",
     S.Integer 4, S.Integer 10]) (Just $ S.Integer 14)

    test "Integer runSExpression Test Sub" (runSExpression $ S.List [S.Symbol "-",
     S.Integer 4, S.Integer 10]) (Just $ S.Integer (-6))

    test "Integer runSExpression Test Mul" (runSExpression $ S.List [S.Symbol "*",
     S.Integer 4, S.Integer 10]) (Just $ S.Integer 40)

    test "Integer runSExpression Test Div" (runSExpression $ S.List [S.Symbol "/",
     S.Integer 4, S.Integer 10]) (Just $ S.Integer 0)

    test "Integer runSExpression Test Nested Operations" (runSExpression $ S.List [S.Symbol "/",
     S.List [S.Symbol "+", S.Integer 4, S.Integer 10], S.List [S.Symbol "-",
      S.Integer 10, S.Integer 6]]) 
     (Just $ S.Integer 3)

    test "Integer runSExpression Test Let  Simple" (runSExpression $ S.List [S.Symbol "x",
     S.List [S.Symbol "+", S.Integer 10, S.Integer 4], S.List [S.Symbol "+", S.Symbol "x", S.Integer 1]])
     (Just $ S.Integer 15)

    test "Integer runExpression Test Let Complex" (runSExpression $ S.List [S.Symbol "y",
     S.List [S.Symbol "-", S.Integer 20, S.Integer 8], S.List [S.Symbol "x",
      S.List [S.Symbol "+", S.Symbol "y", S.Integer 4], S.List [S.Symbol "+",
       S.Symbol "x", S.Integer 1]]])
       (Just $ S.Integer 17)

    test "Real runSExpression 42" (runSExpression $ S.Real 42.0) (Just $ S.Real 42.0)

    test "Real runSExpression Test Add" (runSExpression $ S.List [S.Symbol "+",
     S.Real 4.1, S.Real 10.1]) (Just $ S.Real 14.2)

    test "Real runSExpression Test Sub" (runSExpression $ S.List [S.Symbol "-",
     S.Real 4.1, S.Real 10.1]) (Just $ S.Real (-6.0))

    test "Real runSExpression Test Mul" (runSExpression $ S.List [S.Symbol "*",
     S.Real 4.1, S.Real 10.1]) (Just $ S.Real 41.41)

    test "Real runSExpression Test Div" (runSExpression $ S.List [S.Symbol "/",
     S.Real 4.1, S.Real 10.1]) (Just $ S.Real 0.4059405940594059)

    test "Real runSExpression Test Nested Operations" (runSExpression $ S.List [S.Symbol "/",
     S.List [S.Symbol "+", S.Real 4.1, S.Real 10.1], S.List [S.Symbol "-",
      S.Real 4.1, S.Real 10.1]]) (Just $ S.Real (-2.3666666666666667))

    test "Real runSExpression Test Let  Simple" (runSExpression $ S.List [S.Symbol "x",
     S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]])
     (Just $ S.Real 15.299999999999999)

    test "Real runSExpression Test Let Complex" (runSExpression $ S.List [S.Symbol "y",
     S.List [S.Symbol "-", S.Real 20.1, S.Real 8.1], S.List [S.Symbol "x",
      S.List [S.Symbol "+", S.Symbol "y", S.Real 4.1], S.List [S.Symbol "+",
       S.Symbol "x", S.Real 1.1]]])
     (Just $ S.Real 17.200000000000003) 

    test "Mixed runSExpression 42" (runSExpression $ S.Real 42.0) (Just $ S.Real 42.0)

    test "Mixed runSExpression Test Add" (runSExpression $ S.List [S.Symbol "+",
     S.Real 4.1, S.Real 10.1]) (Just $ S.Real 14.2)

    test "Mixed runSExpression Test Sub" (runSExpression $ S.List [S.Symbol "-",
     S.Real 4.1, S.Real 10.1]) (Just $ S.Real (-6))

    test "Mixed runSExpression Test Mul" (runSExpression $ S.List [S.Symbol "*",
     S.Real 4.1, S.Real 10.1]) (Just $ S.Real 41.41)

    test "Mixed runSExpression Test Div" (runSExpression $ S.List [S.Symbol "/",
     S.Real 4.1, S.Real 10.1]) (Just $ S.Real 0.4059405940594059)

    test "Mixed runSExpression Test Nested Operations" (runSExpression $ S.List [S.Symbol "/",
     S.List [S.Symbol "+", S.Real 4.1, S.Real 10.1], S.List [S.Symbol "-",
      S.Real 4.1, S.Real 10.1]]) (Just $ S.Real (-2.3666666666666667))

    test "Mixed runSExpression Test Let  Simple" (runSExpression $ S.List [S.Symbol "x",
     S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]])
     (Just $ S.Real 15.299999999999999)

    test "Mixed runSExpression Test Let Complex" (runSExpression $ S.List [S.Symbol "y",
     S.List [S.Symbol "-", S.Real 20.1, S.Real 8.1], S.List [S.Symbol "x",
      S.List [S.Symbol "+", S.Symbol "y", S.Real 4.1], S.List [S.Symbol "+",
       S.Symbol "x", S.Real 1.1]]])
     (Just $ S.Real 17.200000000000003)   

        
