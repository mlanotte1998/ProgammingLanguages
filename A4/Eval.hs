{-|
Module      : Eval
Description : Semantics of protoScheme
Copyright   : (c) Ferd, 2020
                  Michael Lanotte, 2020
                  Rachel Johanek, 2020
Maintainer  : f.vesely@northeastern
              lanotte.m@northeastern.edu
              johanek.r@northeastern.edu

This module provides the evaluator of the protoScheme language.

-}
module Eval where

import Syntax

import qualified SExpression as S

import SimpleTests (test)

-- ======================================================================================================

-- Function for testing doubles that takes go to the thousandths place. 
-- Without this, some results were for example 14.850000000000001
checkFloatEquality :: Maybe ExprEval -> Maybe ExprEval -> Bool 
checkFloatEquality (Just (Eval_Float x)) (Just (Eval_Float y)) = if (abs (x - y) < 0.001) 
                                                             then True 
                                                             else False
checkFloatEquality x y = False             

-- Tests for the checkFloatEquality function
test_checkFloatEquality = do 
    test "checkFloatEquality nothing with nothing" False (checkFloatEquality Nothing Nothing)
    test "checkFloatEquality int with nothing" False (checkFloatEquality (Just (Eval_Integer 1)) Nothing)
    test "checkFloatEquality nothing with int" False (checkFloatEquality Nothing (Just (Eval_Integer 1)))
    test "checkFloatEquality int with int" False (checkFloatEquality (Just (Eval_Integer 1)) (Just (Eval_Integer 1)))
    test "checkFloatEquality float with nothing" False (checkFloatEquality (Just (Eval_Float 1.1)) Nothing)
    test "checkFloatEquality nothing with float" False (checkFloatEquality Nothing (Just (Eval_Float 1.1)))
    test "checkFloatEquality float with int" False (checkFloatEquality (Just (Eval_Float 1.1)) (Just (Eval_Integer 1)))
    test "checkFloatEquality int with float" False (checkFloatEquality (Just (Eval_Integer 1)) (Just (Eval_Float 1.1)))
    test "checkFloatEquality float with float should not be equal 1" False (checkFloatEquality (Just (Eval_Float 12.1)) 
     (Just (Eval_Float 12.101000001)))
    test "checkFloatEquality float with float should not be equal 2" False (checkFloatEquality (Just (Eval_Float 12.1)) 
     (Just (Eval_Float 8.0)))
    test "checkFloatEquality float with float should be equal 1" True (checkFloatEquality (Just (Eval_Float 12.1)) 
     (Just (Eval_Float 12.100000001)))
    test "checkFloatEquality float with float should be equal 2" True (checkFloatEquality (Just (Eval_Float 12.1)) 
     (Just (Eval_Float 12.1)))
 
 -- ===============================================================================================

-- |Evaluates the given expression to a value.
{- 
  For Assignment 4:  
     Added Boolean line to function definition. 
     Changed the function signature to show that it needs to take in our new datatype
        for Integers and Floats and Booleans 
     Changed the Var case to handle the new ExprEval types    
     Added If line to function definition for part 2
     Added And, Or, and Not lines to function definition for part 3
-}
eval :: Expr -> Maybe ExprEval 
eval (Integer i) = Just (Eval_Integer i)
eval (Float d) = Just (Eval_Float d)
eval (Boolean b) = Just (Eval_Boolean b)
eval (Var _) = Nothing
eval (Add e1 e2) =
    case eval e1 of
         Just (Eval_Integer v1) ->
            case eval e2 of
                 Just (Eval_Integer v2) -> Just (Eval_Integer (v1 + v2))
                 Just (Eval_Float v2) -> Just (Eval_Float ((fromInteger v1) + v2))
                 Just (Eval_Boolean _) -> Nothing
                 Nothing -> Nothing
         Just (Eval_Float v1) -> 
            case eval e2 of 
                 Just (Eval_Integer v2) -> Just (Eval_Float(v1 + (fromInteger v2)))
                 Just (Eval_Float v2) -> Just (Eval_Float (v1 + v2))
                 Just (Eval_Boolean _) -> Nothing
                 Nothing -> Nothing
         Just (Eval_Boolean _) -> Nothing 
         Nothing -> Nothing        
eval (Sub e1 e2) =
    case eval e1 of
         Just (Eval_Integer v1) ->
            case eval e2 of
                 Just (Eval_Integer v2) -> Just (Eval_Integer (v1 - v2))
                 Just (Eval_Float v2) -> Just (Eval_Float ((fromInteger v1) - v2))
                 Just (Eval_Boolean _) -> Nothing
                 Nothing -> Nothing
         Just (Eval_Float v1) -> 
            case eval e2 of 
                 Just (Eval_Integer v2) -> Just (Eval_Float(v1 - (fromInteger v2)))
                 Just (Eval_Float v2) -> Just (Eval_Float (v1 - v2))
                 Just (Eval_Boolean _) -> Nothing
                 Nothing -> Nothing
         Just (Eval_Boolean _) -> Nothing 
         Nothing -> Nothing        
eval (Mul e1 e2) =
    case eval e1 of
         Just (Eval_Integer v1) ->
            case eval e2 of
                 Just (Eval_Integer v2) -> Just (Eval_Integer (v1 * v2))
                 Just (Eval_Float v2) -> Just (Eval_Float ((fromInteger v1) * v2))
                 Just (Eval_Boolean _) -> Nothing
                 Nothing -> Nothing
         Just (Eval_Float v1) -> 
            case eval e2 of 
                 Just (Eval_Integer v2) -> Just (Eval_Float(v1 * (fromInteger v2)))
                 Just (Eval_Float v2) -> Just (Eval_Float (v1 * v2))
                 Just (Eval_Boolean _) -> Nothing
                 Nothing -> Nothing
         Just (Eval_Boolean _) -> Nothing 
         Nothing -> Nothing           
eval (Div e1 e2) =
    case eval e1 of
         Just (Eval_Integer v1) ->
            case eval e2 of
                 Just (Eval_Integer v2) -> Just (Eval_Integer (v1 `div` v2))
                 Just (Eval_Float v2) -> Just (Eval_Float ((fromInteger v1) / v2))
                 Just (Eval_Boolean _) -> Nothing
                 Nothing -> Nothing
         Just (Eval_Float v1) -> 
            case eval e2 of 
                 Just (Eval_Integer v2) -> Just (Eval_Float(v1 / (fromInteger v2)))
                 Just (Eval_Float v2) -> Just (Eval_Float (v1 / v2))
                 Just (Eval_Boolean _) -> Nothing
                 Nothing -> Nothing
         Just (Eval_Boolean _) -> Nothing 
         Nothing -> Nothing        
eval (Let x e1 e2) =
    case eval e1 of
         Just (Eval_Integer v1) -> eval (subst x (Eval_Integer v1) e2)
         Just (Eval_Float v1) -> eval (subst x (Eval_Float v1) e2)
         Just (Eval_Boolean v1) -> eval (subst x (Eval_Boolean v1) e2)
         Nothing -> Nothing
-- If eval e1 is true then return e2, if false return e3, else return Nothing because 
-- did not receive boolean for e1.          
eval (If e1 e2 e3) = 
     case eval e1 of 
          Just (Eval_Boolean True) -> eval e2 
          Just (Eval_Boolean False) -> eval e3 
          _ -> Nothing 
-- If eval e1 is True then check e2 for either being a boolean to return or anything else returns nothing
-- because and needs booleans. If eval e1 is False then short circuit and return false. Otherwise
-- that means e1 was not a boolean so return Nothing.          
eval (And e1 e2) = 
     case eval e1 of 
          Just (Eval_Boolean True) -> 
            case eval e2 of 
              Just (Eval_Boolean b) -> Just (Eval_Boolean b)
              _ -> Nothing 
          Just (Eval_Boolean False) -> Just (Eval_Boolean False)
          _ -> Nothing     
-- Or is almost the same as And, except now short circuit on True, check eval e2 on false,
-- and still return Nothing when e1 is not a boolean.           
eval (Or e1 e2) = 
     case eval e1 of 
          Just (Eval_Boolean False) -> 
            case eval e2 of 
              Just (Eval_Boolean b) -> Just (Eval_Boolean b)
              _ -> Nothing 
          Just (Eval_Boolean True) -> Just (Eval_Boolean True)
          _ -> Nothing 

-- Not changes eval of e1 true to false, false to true and anything else to Nothing.         
eval (Not e) = 
     case eval e of
          Just (Eval_Boolean True) -> Just (Eval_Boolean False)
          Just (Eval_Boolean False) -> Just (Eval_Boolean True)      
          _ -> Nothing                   

test_eval = do
    -- // Boolean Tests
    test "Boolean True" (eval $ Boolean True) (Just (Eval_Boolean True))

    test "Boolean False" (eval $ Boolean False) (Just (Eval_Boolean False))
    
    test "Boolean eval: (+ True 30)" (eval (Add (Boolean True) (Integer 30))) (Nothing)

    test "Boolean eval: (let (x (+ 1 False)) (* 4 x))"
       (eval $ Let "x" (Add (Integer 1) (Boolean False)) (Mul (Integer 4) (Var "x")))
       (Nothing)

    test "Boolean eval: (- 30 False)" (eval $ Sub (Integer 30) (Boolean False)) (Nothing)

    test "Boolean eval: (* True 12)" (eval $ Mul (Boolean True) (Integer 12)) (Nothing)
  
    test "Boolean eval: (/ False 12)" (eval $ Div (Boolean False) (Integer 12)) (Nothing)

    test "Boolean eval: (* (+ 5 10) (- 5 True))" (eval $ Mul (Add (Integer 5) (Integer 10))
     (Sub (Integer 5) (Boolean True))) (Nothing)

    test "Boolean eval: nested let" (eval $ Let "y" (Sub (Integer 20) (Integer 8))
     (Let "x" (Add (Var "y") (Integer 4)) (Add (Var "x") (Boolean False)))) (Nothing)


    -- // Integer tests
    test "Integer eval: (+ 12 30)" (eval (Add (Integer 12) (Integer 30))) (Just (Eval_Integer 42))

    test "Integer eval: (let (x (+1 2)) (* 4 x))"
       (eval $ Let "x" (Add (Integer 1) (Integer 2)) (Mul (Integer 4) (Var "x")))
       (Just (Eval_Integer 12))

    test "Integer eval not assigned Var Test 1" (eval $ Var "x") (Nothing)

    test "Integer eval not assigned Var Test 2" (eval $ Add (Integer 2) (Var "x")) (Nothing)

    test "Integer eval: simple Integer test" (eval $ Integer 11) (Just (Eval_Integer 11))

    test "Integer eval: (- 30 12)" (eval $ Sub (Integer 30) (Integer 12)) (Just (Eval_Integer 18))

    test "Integer eval: (* 30 12)" (eval $ Mul (Integer 30) (Integer 12)) (Just (Eval_Integer 360))
  
    test "Integer eval: (/ 30 12)" (eval $ Div (Integer 30) (Integer 12)) (Just (Eval_Integer 2))

    test "Integer eval: (* (+ 5 10) (- 5 4))" (eval $ Mul (Add (Integer 5) (Integer 10))
     (Sub (Integer 5) (Integer 4))) (Just (Eval_Integer 15))

    test "Integer eval: nested let" (eval $ Let "y" (Sub (Integer 20) (Integer 8))
     (Let "x" (Add (Var "y") (Integer 4)) (Add (Var "x") (Integer 1)))) (Just (Eval_Integer 17))

    -- // Float tests 

    test "Float eval: (+ 12.2 30.5)" True (checkFloatEquality (eval (Add (Float 12.2) (Float 30.5))) (Just (Eval_Float 42.7)))

    test "Float eval: (let (x (+1.1 2.2)) (* 4.5 x))"
       True 
       (checkFloatEquality(eval $ Let "x" (Add (Float 1.1) (Float 2.2)) (Mul (Float 4.5) (Var "x"))) (Just (Eval_Float 14.85)))

    test "Float eval not assigned Var Test" (eval $ Add (Float 2.5) (Var "x")) (Nothing)
   
    test "Float eval: simple Integer test" True (checkFloatEquality (eval $ Float 11.1) (Just (Eval_Float 11.1)))

    test "Float eval: (- 30.5 12.5)" True (checkFloatEquality (eval $ Sub (Float 30.5) (Float 12.5)) (Just (Eval_Float 18.0)))

    test "Float eval: (* 30.5 12.1)" True (checkFloatEquality (eval $ Mul (Float 30.5) (Float 12.1)) (Just (Eval_Float 369.05)))

    test "Float eval: (/ 30.0 12.0)" True (checkFloatEquality (eval $ Div (Float 30.0) (Float 12.0)) (Just (Eval_Float 2.5)))

    test "Float eval: (* (+ 5.5 10.5) (- 5.4 4.4))" True (checkFloatEquality (eval $ Mul (Add (Float 5.5) (Float 10.5))
     (Sub (Float 5.4) (Float 4.4))) (Just (Eval_Float 16.0)))

    test "Float eval: nested let" True (checkFloatEquality (eval $ Let "y" (Sub (Float 20.2) (Float 8.4))
     (Let "x" (Add (Var "y") (Float 4.4)) (Add (Var "x") (Float 1.1)))) (Just (Eval_Float 17.3)))

    -- // Mixed tests 

    test "Mixed eval: (+ 12.2 30)" True (checkFloatEquality (eval (Add (Float 12.2) (Integer 30))) (Just (Eval_Float 42.2)))

    test "Mixed eval: (let (x (+1.1 20)) (* 4.5 x))" True
       (checkFloatEquality (eval $ Let "x" (Add (Float 1.1) (Integer 20)) (Mul (Integer 4) (Var "x")))
       (Just (Eval_Float 84.4)))

    test "Mixed eval: (- 30.5 12)" True (checkFloatEquality (eval $ Sub (Float 30.5) (Integer 12)) (Just (Eval_Float 18.5)))

    test "Mixed eval: (* 30.5 12)" True (checkFloatEquality (eval $ Mul (Float 30.5) (Integer 12)) (Just (Eval_Float 366.0)))

    test "Mixed eval: (/ 32.5 10)" True (checkFloatEquality (eval $ Div (Float 32.5) (Float 10)) (Just (Eval_Float 3.25)))

    test "Mixed eval: (* (+ 5.5 10) (- 5.4 4))" True (checkFloatEquality (eval $ Mul (Add (Float 5.5) (Integer 10))
     (Sub (Integer 5) (Float 4.4))) (Just (Eval_Float 9.299999999999994)))

    test "Mixed eval: nested let" True (checkFloatEquality (eval $ Let "y" (Sub (Float 20.2) (Integer 8))
     (Let "x" (Add (Var "y") (Integer 4)) (Add (Var "x") (Float 1.1)))) (Just (Eval_Float 17.3)))


    -- // If tests 

    test "If eval: e1 is True Simple" (eval $ If (Boolean True) (Integer 10) (Float 15.1))  
      (Just $ Eval_Integer 10)  

    test "If eval: e1 is False Simple" True (checkFloatEquality (eval $ If (Boolean False) (Integer 10) (Float 15.1))  
      (Just $ Eval_Float 15.1))

    test "If eval: e1 is True Complex" True (checkFloatEquality (eval $ If (Boolean True) (Add (Integer 10) (Float 9.5)) (Float 15.1))
      (Just $ Eval_Float 19.5))

    test "If eval: e1 is False Complex" True (checkFloatEquality (eval $ If (Boolean False) (Float 15.1) (Sub (Integer 10) (Float 9.5)))
      (Just $ Eval_Float 0.5))

    test "If eval: e1 is not a boolean" (eval $ If (Div (Integer 5) (Float 5.1)) (Boolean False) (Boolean True))
        (Nothing)       

   -- // And tests 

    test "And eval: e1 not a boolean simple" (eval $ And (Integer 10) (Boolean False)) (Nothing)    

    test "And eval: e1 not a boolean complex" (eval $ And (If (Boolean False) (Float 5.5) 
      (Add (Boolean True) (Integer 10))) (Boolean True)) (Nothing)  

    test "And eval: e1 is False simple" (eval $ And (Boolean False) (Integer 3)) (Just (Eval_Boolean False))  

    test "And eval: e1 is False complex" (eval $ And (If (Boolean False) (Float 5.5) (Boolean False)) 
      (Float 3.5)) (Just (Eval_Boolean False))






-- |Substitutes the given value for the given variable in the given expression.
-- Given value can now be either a double or an integer 
{-
 For Assignment 4:
 Added Boolean line to function definition. 
 Changed the function signature to show that it needs to take in our new datatype
    for Integers and Floats and Booleans 
 Changed the Var case to handle the new ExprEval types    
 Added If line to function definition for part 2
 Added And, Or, and Not lines to function definition for part 3
-}
subst :: Variable -> ExprEval -> Expr -> Expr
subst _ _ (Integer n) = Integer n
subst _ _ (Float f) = Float f
subst _ _ (Boolean b) = Boolean b
subst x v (Var y) | x == y = 
                      case v of 
                           Eval_Integer num -> Integer num 
                           Eval_Float num -> Float num 
                           Eval_Boolean b-> Boolean b
                  | otherwise = Var y
subst x v (Add e1 e2) = Add (subst x v e1) (subst x v e2)
subst x v (Sub e1 e2) = Sub (subst x v e1) (subst x v e2)
subst x v (Mul e1 e2) = Mul (subst x v e1) (subst x v e2)
subst x v (Div e1 e2) = Div (subst x v e1) (subst x v e2)
subst x v (Let y e1 e2) | x == y = Let y (subst x v e1) e2
                        | otherwise = Let y (subst x v e1) (subst x v e2)
subst x v (If e1 e2 e3) = If (subst x v e1) (subst x v e2) (subst x v e3)     
subst x v (And e1 e2) = And (subst x v e1) (subst x v e2)
subst x v (Or e1 e2) = Or (subst x v e1) (subst x v e2)
subst x v (Not e1) = Not (subst x v e1)                     



test_subst = do
   -- // Integer tests
    test "subst x 42 x" (subst "x" (Eval_Integer 42) (Var "x")) (Integer 42)

    test "subst x 42 y" (subst "x" (Eval_Integer 42) (Var "y")) (Var "y")

    test "subst Add Test Simple Integer" (subst "x" (Eval_Integer 10) (Add (Integer 20) (Integer 4)))
     (Add (Integer 20) (Integer 4))

    test "subst Add Test Complex Integer" (subst "x" (Eval_Integer 10) (Add (Var "x") (Integer 4)))
     (Add (Integer 10) (Integer 4))

    test "subst Sub Test Simple Integer" (subst "x" (Eval_Integer 10) (Sub (Integer 20) (Integer 4)))
     (Sub (Integer 20) (Integer 4))

    test "subst Sub Test Complex Integer" (subst "x" (Eval_Integer 10) (Sub (Var "x") (Integer 4)))
     (Sub (Integer 10) (Integer 4))

    test "subst Mul Test Simple Integer" (subst "x" (Eval_Integer 10) (Mul (Integer 20) (Integer 4)))
     (Mul (Integer 20) (Integer 4))

    test "subst Mul Test Complex Integer" (subst "x" (Eval_Integer 10) (Mul (Var "x") (Integer 4)))
     (Mul (Integer 10) (Integer 4))

    test "subst Div Test Simple Integer" (subst "x" (Eval_Integer 10) (Div (Integer 20) (Integer 4)))
     (Div (Integer 20) (Integer 4))

    test "subst Div Test Complex Integer" (subst "x" (Eval_Integer 10) (Div (Var "x") (Integer 4)))
     (Div (Integer 10) (Integer 4))

    test "subst nested variable Test Integer" (subst "x" (Eval_Integer 10) (Div
     (Sub (Integer 10) (Var "x")) (Add (Var "y") (Integer 15))))
      (Div (Sub (Integer 10) (Integer 10)) (Add (Var "y") (Integer 15)))

    test "subst let Test 1 Integer" (subst "x" (Eval_Integer 10)
     (Let "x" (Add (Var "x") (Integer 6)) (Sub (Var "x") (Integer 16))))
      (Let "x" (Add (Integer 10) (Integer 6)) (Sub (Var "x") (Integer 16)))

    test "subst let Test 2 Integer" (subst "x" (Eval_Integer 10)
     (Let "y" (Add (Var "y") (Integer 6)) (Sub (Var "x") (Integer 16))))
      (Let "y" (Add (Var "y") (Integer 6)) (Sub (Integer 10) (Integer 16)))

    test "subst let Test 3 Integer" (subst "x" (Eval_Integer 10)
     (Let "y" (Add (Var "x") (Integer 6)) (Sub (Var "x") (Integer 16))))
      (Let "y" (Add (Integer 10) (Integer 6)) (Sub (Integer 10) (Integer 16)))

    -- // Float Tests

    test "subst x 42.5 x" (subst "x" (Eval_Float 42.5) (Var "x")) (Float 42.5)

    test "subst x 42.5 y" (subst "x" (Eval_Float 42.5) (Var "y")) (Var "y")

    test "subst Add Test Simple Float" (subst "x" (Eval_Float 10.5) (Add (Integer 20) (Integer 4)))
     (Add (Integer 20) (Integer 4))

    test "subst Add Test Complex Float" (subst "x" (Eval_Float 10.5) (Add (Var "x") (Integer 4)))
     (Add (Float 10.5) (Integer 4))

    test "subst Sub Test Simple Float" (subst "x" (Eval_Float 10.5) (Sub (Integer 20) (Integer 4)))
     (Sub (Integer 20) (Integer 4))

    test "subst Sub Test Complex Float" (subst "x" (Eval_Float 10.5) (Sub (Var "x") (Integer 4)))
     (Sub (Float 10.5) (Integer 4))

    test "subst Mul Test Simple Float" (subst "x" (Eval_Float 10.5) (Mul (Integer 20) (Integer 4)))
     (Mul (Integer 20) (Integer 4))

    test "subst Mul Test Complex Float" (subst "x" (Eval_Float 10.5) (Mul (Var "x") (Integer 4)))
     (Mul (Float 10.5) (Integer 4))

    test "subst Div Test Simple Float" (subst "x" (Eval_Float 10.5) (Div (Integer 20) (Integer 4)))
     (Div (Integer 20) (Integer 4))

    test "subst Div Test Complex Float" (subst "x" (Eval_Float 10.5) (Div (Var "x") (Integer 4)))
     (Div (Float 10.5) (Integer 4))

    test "subst nested variable Test Float" (subst "x" (Eval_Float 10.5) (Div
     (Sub (Integer 10) (Var "x")) (Add (Var "y") (Integer 15))))
      (Div (Sub (Integer 10) (Float 10.5)) (Add (Var "y") (Integer 15)))

    test "subst let Test 1 Float" (subst "x" (Eval_Float 10.5)
     (Let "x" (Add (Var "x") (Integer 6)) (Sub (Var "x") (Integer 16))))
      (Let "x" (Add (Float 10.5) (Integer 6)) (Sub (Var "x") (Integer 16)))

    test "subst let Test 2 Float" (subst "x" (Eval_Float 10.5)
     (Let "y" (Add (Var "y") (Integer 6)) (Sub (Var "x") (Integer 16))))
      (Let "y" (Add (Var "y") (Integer 6)) (Sub (Float 10.5) (Integer 16)))

    test "subst let Test 3 Float" (subst "x" (Eval_Float 10.5)
     (Let "y" (Add (Var "x") (Integer 6)) (Sub (Var "x") (Integer 16))))
      (Let "y" (Add (Float 10.5) (Integer 6)) (Sub (Float 10.5) (Integer 16)))

    -- // Boolean Tests  
    test "subst x 42.5 x" (subst "x" (Eval_Boolean False) (Var "x")) (Boolean False)

    test "subst x 42.5 y" (subst "x" (Eval_Boolean True) (Var "y")) (Var "y")

    test "subst Add Test Simple Boolean" (subst "x" (Eval_Boolean True) (Add (Integer 20) (Integer 4)))
     (Add (Integer 20) (Integer 4))

    test "subst Add Test Complex Boolean" (subst "x" (Eval_Boolean True) (Add (Var "x") (Integer 4)))
     (Add (Boolean True) (Integer 4))

    test "subst Sub Test Simple Boolean" (subst "x" (Eval_Boolean True) (Sub (Integer 20) (Integer 4)))
     (Sub (Integer 20) (Integer 4))

    test "subst Sub Test Complex Boolean" (subst "x" (Eval_Boolean False) (Sub (Var "x") (Integer 4)))
     (Sub (Boolean False) (Integer 4))

    test "subst Mul Test Simple Boolean" (subst "x" (Eval_Boolean False) (Mul (Integer 20) (Integer 4)))
     (Mul (Integer 20) (Integer 4))

    test "subst Mul Test Complex Boolean" (subst "x" (Eval_Boolean False) (Mul (Var "x") (Integer 4)))
     (Mul (Boolean False) (Integer 4))

    test "subst Div Test Simple Boolean" (subst "x" (Eval_Boolean True) (Div (Integer 20) (Integer 4)))
     (Div (Integer 20) (Integer 4))

    test "subst Div Test Complex Boolean" (subst "x" (Eval_Boolean True) (Div (Var "x") (Integer 4)))
     (Div (Boolean True) (Integer 4))

    test "subst nested variable Test Boolean" (subst "x" (Eval_Boolean True) (Div
     (Sub (Integer 10) (Var "x")) (Add (Var "y") (Integer 15))))
      (Div (Sub (Integer 10) (Boolean True)) (Add (Var "y") (Integer 15)))

    test "subst let Test 1 Boolean" (subst "x" (Eval_Boolean False)
     (Let "x" (Add (Var "x") (Integer 6)) (Sub (Var "x") (Integer 16))))
      (Let "x" (Add (Boolean False) (Integer 6)) (Sub (Var "x") (Integer 16)))

    test "subst let Test 2 Boolean" (subst "x" (Eval_Boolean True)
     (Let "y" (Add (Var "y") (Integer 6)) (Sub (Var "x") (Integer 16))))
      (Let "y" (Add (Var "y") (Integer 6)) (Sub (Boolean True) (Integer 16)))

    test "subst let Test 3 Boolean" (subst "x" (Eval_Boolean False)
     (Let "y" (Add (Var "x") (Integer 6)) (Sub (Var "x") (Integer 16))))
      (Let "y" (Add (Boolean False) (Integer 6)) (Sub (Boolean False) (Integer 16)))


    -- If tests 

    test "subst if test No subst" (subst "x" (Eval_Integer 5) (If (Boolean True) (Integer 1) (Float 5.1))) 
      (If (Boolean True) (Integer 1) (Float 5.1))  

    test "subst if test Subst into e1" (subst "x" (Eval_Integer 5) (If (Var "x") (Integer 1) (Float 5.1))) 
      (If (Integer 5) (Integer 1) (Float 5.1))    

    test "subst if test Subst into e2" (subst "x" (Eval_Integer 5) (If (Boolean True) (Var "x") (Float 5.1))) 
      (If (Boolean True) (Integer 5) (Float 5.1))   

    test "subst if test Subst into e3 with other variable present" (subst "x" (Eval_Integer 5) (If (Boolean True) (Var "y") (Var "x"))) 
      (If (Boolean True) (Var "y") (Integer 5))   

    test "subst if test Subst into a let" (subst "x" (Eval_Integer 5) (If (Boolean True) 
      (Let "y" (Add (Var "y") (Integer 6)) (Sub (Var "x") (Integer 16))) (Integer 10)))
        (If (Boolean True) (Let "y" (Add (Var "y") (Integer 6)) 
          (Sub (Integer 5) (Integer 16))) (Integer 10))    

    -- And tests 

    test "subst and test No subst" (subst "x" (Eval_Integer 5) (And (Boolean True) (Float 5.1))) 
      (And (Boolean True) (Float 5.1))  

    test "subst and test Subst into e1" (subst "x" (Eval_Integer 5) (And (Var "x") (Float 5.1))) 
      (And (Integer 5) (Float 5.1))    

    test "subst and test Subst into e2" (subst "x" (Eval_Integer 5) (And (Boolean True) (Var "x"))) 
      (And (Boolean True) (Integer 5))   

    test "subst and test Subst into e2 with other variable present" (subst "x" (Eval_Integer 5) (And (Var "y") (Var "x"))) 
      (And (Var "y") (Integer 5))   

    test "subst and test Subst into a let" (subst "x" (Eval_Integer 5) (And (Boolean True) 
      (Let "y" (Add (Var "y") (Integer 6)) (Sub (Var "x") (Integer 16)))))
        (And (Boolean True) (Let "y" (Add (Var "y") (Integer 6)) 
          (Sub (Integer 5) (Integer 16))))   

    -- Or tests 

    test "subst or test No subst" (subst "x" (Eval_Integer 5) (Or (Boolean True) (Float 5.1))) 
      (Or (Boolean True) (Float 5.1))  

    test "subst or test Subst into e1" (subst "x" (Eval_Integer 5) (Or (Var "x") (Float 5.1))) 
      (Or (Integer 5) (Float 5.1))    

    test "subst or test Subst into e2" (subst "x" (Eval_Integer 5) (Or (Boolean True) (Var "x"))) 
      (Or (Boolean True) (Integer 5))   

    test "subst or test Subst into e2 with other variable present" (subst "x" (Eval_Integer 5) (Or (Var "y") (Var "x"))) 
      (Or (Var "y") (Integer 5))   

    test "subst or test Subst into a let" (subst "x" (Eval_Integer 5) (Or (Boolean True) 
      (Let "y" (Add (Var "y") (Integer 6)) (Sub (Var "x") (Integer 16)))))
        (Or (Boolean True) (Let "y" (Add (Var "y") (Integer 6)) 
          (Sub (Integer 5) (Integer 16))))   

    -- Not tests 

    test "subst not test No subst" (subst "x" (Eval_Integer 5) (Not (Boolean True))) 
      (Not (Boolean True))  

    test "subst not test Subst into e" (subst "x" (Eval_Integer 5) (Not (Var "x"))) 
      (Not (Integer 5))    
  
    test "subst not test Subst into e with other variable present" (subst "x" (Eval_Integer 5) (Not (Var "y"))) 
      (Not (Var "y"))   

    test "subst not test Subst into a let" (subst "x" (Eval_Integer 5) (Not 
      (Let "y" (Add (Var "y") (Integer 6)) (Sub (Var "x") (Integer 16)))))
        (Not (Let "y" (Add (Var "y") (Integer 6)) 
          (Sub (Integer 5) (Integer 16))))              


-- |Run the given protoScheme s-expression, returning an s-expression
-- representation of the result.
runSExpression :: S.Expr -> Maybe S.Expr
runSExpression se =
    case eval (fromSExpression se) of
         (Just (Eval_Integer v)) -> Just (valueToSExpression (Eval_Integer v))
         (Just (Eval_Float v)) -> Just (valueToSExpression (Eval_Float v))
         (Just (Eval_Boolean v)) -> Just (valueToSExpression (Eval_Boolean v))
         Nothing -> Nothing

test_runSExpression = do

    test "run: (+ 1 2)"
        (runSExpression $ S.List [S.Symbol "+", S.Integer 1, S.Integer 2])
        (Just $ S.Integer 3)

    test "runSExpression Test Variable" (runSExpression $ S.Symbol "v") (Nothing)

    -- Integer Tests

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

    test "Integer runSExpression Test Let  Simple" (runSExpression $ S.List [S.Symbol "Let", S.Symbol "x",
     S.List [S.Symbol "+", S.Integer 10, S.Integer 4], S.List [S.Symbol "+", S.Symbol "x", S.Integer 1]])
     (Just $ S.Integer 15)

    test "Integer runExpression Test Let Complex" (runSExpression $ S.List [S.Symbol "Let", S.Symbol "y",
     S.List [S.Symbol "-", S.Integer 20, S.Integer 8], S.List [S.Symbol "Let", S.Symbol "x",
      S.List [S.Symbol "+", S.Symbol "y", S.Integer 4], S.List [S.Symbol "+",
       S.Symbol "x", S.Integer 1]]])
       (Just $ S.Integer 17)

    -- Real Tests 

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

    test "Real runSExpression Test Let  Simple" (runSExpression $ S.List [S.Symbol "Let", S.Symbol "x",
     S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]])
     (Just $ S.Real 15.299999999999999)

    test "Real runSExpression Test Let Complex" (runSExpression $ S.List [S.Symbol "Let", S.Symbol "y",
     S.List [S.Symbol "-", S.Real 20.1, S.Real 8.1], S.List [S.Symbol "Let", S.Symbol "x",
      S.List [S.Symbol "+", S.Symbol "y", S.Real 4.1], S.List [S.Symbol "+",
       S.Symbol "x", S.Real 1.1]]])
     (Just $ S.Real 17.200000000000003) 

    -- Mixed Tests 

    test "Mixed runSExpression Test Add" (runSExpression $ S.List [S.Symbol "+",
     S.Real 4.1, S.Integer 10]) (Just $ S.Real 14.1)

    test "Mixed runSExpression Test Sub" (runSExpression $ S.List [S.Symbol "-",
     S.Real 4.1, S.Integer 10]) (Just $ S.Real (-5.9))

    test "Mixed runSExpression Test Mul" (runSExpression $ S.List [S.Symbol "*",
     S.Real 4.1, S.Integer 10]) (Just $ S.Real 41)

    test "Mixed runSExpression Test Div" (runSExpression $ S.List [S.Symbol "/",
     S.Real 4.1, S.Integer 10]) (Just $ S.Real 0.41)

    test "Mixed runSExpression Test Nested Operations" (runSExpression $ S.List [S.Symbol "/",
     S.List [S.Symbol "+", S.Real 4.1, S.Integer 10], S.List [S.Symbol "-",
      S.Real 4.1, S.Real 10.1]]) (Just $ S.Real (-2.35))

    test "Mixed runSExpression Test Let  Simple" (runSExpression $ S.List [S.Symbol "Let", S.Symbol "x",
     S.List [S.Symbol "+", S.Integer 10, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]])
     (Just $ S.Real 15.2)

    test "Mixed runSExpression Test Let Complex" (runSExpression $ S.List [S.Symbol "Let", S.Symbol "y",
     S.List [S.Symbol "-", S.Integer 20, S.Real 8.1], S.List [S.Symbol "Let", S.Symbol "x",
      S.List [S.Symbol "+", S.Symbol "y", S.Real 4.1], S.List [S.Symbol "+",
       S.Symbol "x", S.Real 1.1]]])
     (Just $ S.Real 17.1)   


    -- Boolean tests

    test "Boolean runSExpression Test 1" (runSExpression $ S.Boolean False) 
      (Just $ S.Boolean False)

    test "Boolean runSExpression Test 2" (runSExpression $ S.Boolean True) 
      (Just $ S.Boolean True)  

    -- If tests 

    test "If runSExpression Test e1 is True Simple" (runSExpression $ S.List 
      [S.Symbol "If", S.Boolean True, S.Integer 10, S.Real 15])
        (Just $ S.Integer 10)  

    test "If runSExpression Test e1 is False Simple" (runSExpression $ S.List 
      [S.Symbol "If", S.Boolean False, S.Integer 10, S.Real 15])
        (Just $ S.Real 15)      

    test "If runSExpression Test e1 is True Complex" (runSExpression $ S.List 
      [S.Symbol "If", S.Boolean True, S.List [S.Symbol "+", S.Integer 10, S.Integer 15] , S.Real 15])
        (Just $ S.Integer 25)  

    test "If runSExpression Test e1 is False Complex" (runSExpression $ S.List 
      [S.Symbol "If", S.Boolean False, S.Integer 10, S.List [S.Symbol "+", S.Real 10.1, S.Real 15.1]])
        (Just $ S.Real 25.2)     

    test "If runSExpression Test e1 is not a boolean" (runSExpression $ S.List 
      [S.Symbol "If", S.List [S.Symbol "+", S.Integer 10, S.Integer 15], S.Integer 10, S.Real 15])
        (Nothing)       

    -- TODODODODODODODOODDO 

    -- And tests
    test "And runSExpression Test 1" (fromSExpression $ S.List [
        S.Symbol "And" , S.Boolean True, S.Integer 10]) 
          (And (Boolean True) (Integer 10))   

    test "And runSExpression Test 2" (fromSExpression $ S.List [
        S.Symbol "And" , S.Boolean False, S.List [S.Symbol "Let", S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
            (And (Boolean False) (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1))))       

    test "And runSExpression Test 3" (fromSExpression $ S.List [
        S.Symbol "And" , S.List [S.Symbol "And" , S.Integer 10, S.Real 15.1], 
         S.List [S.Symbol "Let", S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
            (And (And (Integer 10) (Float 15.1))
             (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1))))    

    -- Or tests
    test "Or fromSExpression Test 1" (fromSExpression $ S.List [
        S.Symbol "Or" , S.Boolean True, S.Integer 10]) 
          (Or (Boolean True) (Integer 10))   

    test "Or fromSExpression Test 2" (fromSExpression $ S.List [
        S.Symbol "Or" , S.Boolean False, S.List [S.Symbol "Let", S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
            (Or (Boolean False) (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1))))       

    test "Or fromSExpression Test 3" (fromSExpression $ S.List [
        S.Symbol "Or" , S.List [S.Symbol "Or" , S.Integer 10, S.Real 15.1], 
         S.List [S.Symbol "Let", S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
            (Or (Or (Integer 10) (Float 15.1))
             (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1))))    

    -- Not tests
    test "Not fromSExpression Test 1" (fromSExpression $ S.List [
        S.Symbol "Not" , S.Boolean True]) 
          (Not (Boolean True))   

    test "Not fromSExpression Test 2" (fromSExpression $ S.List [
        S.Symbol "Not" , S.List [S.Symbol "Let", S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
            (Not (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1))))       

    test "Not fromSExpression Test 3" (fromSExpression $ S.List [
        S.Symbol "Not" , S.List [S.Symbol "Or" , S.Integer 10, 
         S.List [S.Symbol "Let", S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]]) 
            (Not (Or (Integer 10)
             (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1)))))   
        
