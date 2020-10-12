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
     Added Less_Than, Greater_Than, and Equal for part 4
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
-- For or, if e1 is True then return True. If e1 is false then evaluate e2, so then
-- if e2 is a boolean return that, otherwise return False or Nothing is still False.
-- If e1 is not a boolean than evaluate e2, and if boolean return that or if not return nothing 
-- because once again Nothing | Boolean should be that Boolean.       
eval (Or e1 e2) = 
     case eval e1 of 
          Just (Eval_Boolean True) -> Just (Eval_Boolean True)
          Just (Eval_Boolean False) -> 
            case eval e2 of 
              Just (Eval_Boolean b) -> Just (Eval_Boolean b)
              _ -> Just (Eval_Boolean False)
          _ -> 
            case eval e2 of 
              Just (Eval_Boolean b) -> Just (Eval_Boolean b)
              _ -> Nothing 

-- Not changes eval of e1 true to false, false to true and anything else to Nothing.         
eval (Not e) = 
     case eval e of
          Just (Eval_Boolean True) -> Just (Eval_Boolean False)
          Just (Eval_Boolean False) -> Just (Eval_Boolean True)      
          _ -> Nothing                   

-- Less than checks what eval e1 is and then compares it with eval e2. 
-- If eval e1 is a integer, and eval e2 is an integer or float then compare with the < 
-- otherwise return nothing. If eval e1 is a float then do the same thing. Just need 
-- to convert ints to floats when the other element is a float. 
-- Lastly, if eval e1 is not an integer or float (Nothing or Boolean) then return Nothing. 
eval (Less_Than e1 e2) =
    case eval e1 of
         Just (Eval_Integer v1) ->
            case eval e2 of
                 Just (Eval_Integer v2) -> Just (Eval_Boolean (v1 < v2))
                 Just (Eval_Float v2) -> Just (Eval_Boolean ((fromInteger v1) < v2))
                 _ -> Nothing
         Just (Eval_Float v1) -> 
            case eval e2 of 
                 Just (Eval_Integer v2) -> Just (Eval_Boolean(v1 < (fromInteger v2)))
                 Just (Eval_Float v2) -> Just (Eval_Boolean (v1 < v2))
                 _ -> Nothing
         _ -> Nothing  

-- Greater than checks what eval e1 is and then compares it with eval e2. 
-- If eval e1 is a integer, and eval e2 is an integer or float then compare with the >
-- otherwise return nothing. If eval e1 is a float then do the same thing. Just need 
-- to convert ints to floats when the other element is a float. 
-- Lastly, if eval e1 is not an integer or float (Nothing or Boolean) then return Nothing. 
eval (Greater_Than e1 e2) =
    case eval e1 of
         Just (Eval_Integer v1) ->
            case eval e2 of
                 Just (Eval_Integer v2) -> Just (Eval_Boolean (v1 > v2))
                 Just (Eval_Float v2) -> Just (Eval_Boolean ((fromInteger v1) > v2))
                 _ -> Nothing
         Just (Eval_Float v1) -> 
            case eval e2 of 
                 Just (Eval_Integer v2) -> Just (Eval_Boolean (v1 > (fromInteger v2)))
                 Just (Eval_Float v2) -> Just (Eval_Boolean (v1 > v2))
                 _ -> Nothing
         _ -> Nothing 

-- Equals works similarly to less than and greater than for eval e1 being an Integer or Float. 
-- But now can check booleans and also if both eval e1 and eval e2 are nothing then return true. 
eval (Equal_To e1 e2) =
    case eval e1 of
         Just (Eval_Integer v1) ->
            case eval e2 of
                 Just (Eval_Integer v2) -> Just (Eval_Boolean (v1 == v2))
                 Just (Eval_Float v2) -> Just (Eval_Boolean ((fromInteger v1) == v2))
                 _ -> Nothing
         Just (Eval_Float v1) -> 
            case eval e2 of 
                 Just (Eval_Integer v2) -> Just (Eval_Boolean (v1 == (fromInteger v2)))
                 Just (Eval_Float v2) -> Just (Eval_Boolean (v1 == v2))
                 _ -> Nothing
         Just (Eval_Boolean v1) -> 
            case eval e2 of 
                Just (Eval_Boolean v2) -> Just (Eval_Boolean (v1 == v2))
                _ -> Nothing 
         Nothing -> 
             case eval e2 of 
                 Nothing -> Just (Eval_Boolean (True))
                 _ -> Nothing     

eval (Cond x) = (evalTupleListHelper x)         

evalTupleListHelper :: [(Expr, Expr)] -> Maybe ExprEval
evalTupleListHelper [] = Nothing 
evalTupleListHelper [(Else, t2)] = eval t2
evalTupleListHelper ((t1, t2):xs) = case eval t1 of 
                                         (Just (Eval_Boolean True)) -> eval t2 
                                         (Just (Eval_Boolean False)) -> evalTupleListHelper xs
                                         _ -> Nothing 


test_evalTupleListHelper = do 
    test "evalTupleListHelper basic test" (evalTupleListHelper []) Nothing 

    test "evalTupleListHelper else case basic " (evalTupleListHelper [(Else, Integer 5)]) (Just (Eval_Integer 5))

    test "evalTupleListHelper else case complex 1" (evalTupleListHelper [(Boolean False, Float 5.5), (Else, (Integer 5))]) (Just (Eval_Integer 5))

    test "evalTupleListHelper else case complex 2" (evalTupleListHelper [(Boolean True, Float 5.5), (Else, (Integer 5))]) (Just (Eval_Float 5.5))

    test "evalTupleListHelper no else complex 1" (evalTupleListHelper [(Boolean False, Float 5.5), (Boolean False, (Integer 5))]) (Nothing)

    test "evalTupleListHelper no else complex 2" (evalTupleListHelper [(Boolean True, Float 5.5), (Boolean False, (Integer 5))]) (Just (Eval_Float 5.5))

    test "evalTupleListHelper no else complex 3" (evalTupleListHelper [(Boolean False, Float 5.5), (And (Boolean True) (Less_Than (Integer 1) (Integer 2)), 
     (Integer 5))]) (Just (Eval_Integer 5)) 

    test "evalTupleListHelper no else complex 4" (evalTupleListHelper [(Equal_To (Integer 10) (Float 10.0), Boolean True), (And (Boolean True) (Less_Than (Integer 1) (Integer 2)), 
     (Integer 5))]) (Just (Eval_Boolean True))  

    test "evalTupleListHelper no else complex 5" (evalTupleListHelper [(Add (Integer 10) (Float 10.0) ,Boolean False), (And (Boolean True) (Less_Than (Integer 1) (Integer 2)), 
     (Integer 5))]) (Nothing)   

                         
test_eval = do
    -- // Boolean Tests
    test "Boolean eval True" (eval $ Boolean True) (Just (Eval_Boolean True))

    test "Boolean eval False" (eval $ Boolean False) (Just (Eval_Boolean False))
    
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

    test "And eval: e1 is True, e2 is True simple" (eval $ And (Boolean True) (Boolean True)) (Just (Eval_Boolean True))

    test "And eval: e1 is True, e2 is True complex"  (eval $ And (If (And (Boolean True) (Boolean True)) (Boolean True) (Boolean False)) 
      (If (And (Boolean True) (Boolean False)) (Boolean False) (Boolean True))) (Just (Eval_Boolean True))

    test "And eval: e1 is True, e2 is False simple"  (eval $ And (Boolean True) (Boolean False)) (Just (Eval_Boolean False)) 

    test "And eval: e1 is True, e2 is False complex"  (eval $ And (If (And (Boolean True) (Boolean True)) (Boolean True) (Boolean False)) 
      (If (And (Boolean True) (Boolean False)) (Boolean True) (Boolean False))) (Just (Eval_Boolean False))

    test "And eval: e1 is True, e2 is not a boolean simple" (eval $ And (Boolean True) (Integer 10)) (Nothing)  

    test "And eval: e1 is True, e2 is not a boolean complex" (eval $ And (If (And (Boolean True) (Boolean True)) (Boolean True) (Boolean False)) 
      (If (And (Boolean True) (Boolean True)) (Mul (Float 5.5) (Integer 10)) (Boolean False))) (Nothing)

    -- // Or tests 

    test "Or eval: e1 not a boolean, e2 is True simple" (eval $ Or (Integer 10) (Boolean True)) (Just (Eval_Boolean True))    

    test "Or eval: e1 not a boolean, e2 is False simple" (eval $ Or (Integer 10) (Boolean False)) (Just (Eval_Boolean False)) 
    
    test "Or eval: e1 not a boolean, e2 is not a boolean simple" (eval $ Or (Integer 10) (Float 15.2)) (Nothing)

    test "Or eval: e1 not a boolean, e2 is True complex" (eval $ Or (Let "x" (Float 5.5) (Add (Var "x") (Integer 5))) 
      (If (And (Boolean True) (Boolean True)) (Boolean True) (Boolean False))) (Just (Eval_Boolean True))

    test "Or eval: e1 not a boolean, e2 is False complex" (eval $ Or (Let "x" (Float 5.5) (Add (Var "x") (Integer 5)))
      (If (And (Boolean True) (Boolean False)) (Boolean True) (Boolean False))) (Just (Eval_Boolean False))

    test "Or eval: e1 not a boolean, e2 is not a boolean complex" (eval $ Or (Let "x" (Float 5.5) (Add (Var "x") (Integer 5))) 
      (If (And (Boolean True) (Boolean False)) (Boolean True) (Float 5.5))) (Nothing)  

    test "Or eval: e1 is True, e2 is True simple" (eval $ Or (Boolean True) (Boolean True)) (Just (Eval_Boolean True))
    
    test "Or eval: e1 is True, e2 is False simple" (eval $ Or (Boolean True) (Boolean False)) (Just (Eval_Boolean True))

    test "Or eval: e1 is True, e2 is not a boolean simple" (eval $ Or (Boolean True) (Integer 15)) (Just (Eval_Boolean True))
      
    test "Or eval: e1 is True, e2 is True complex" (eval $ (Or (Let "x" (Boolean True) (Var "x")) 
      (And (Boolean True) (Boolean True)))) (Just (Eval_Boolean True))
      
    test "Or eval: e1 is True, e2 is False complex" (eval $ (Or (Let "x" (Boolean True) (Var "x")) 
      (And (Boolean True) (Boolean False)))) (Just (Eval_Boolean True))  

    test "Or eval: e1 is True, e2 is not a boolean complex" (eval $ (Or (Let "x" (Boolean True) (Var "x")) 
      (Div (Float 5.5) (Integer 22)))) (Just (Eval_Boolean True))  

    test "Or eval: e1 is False, e2 is True simple" (eval $ Or (Boolean False) (Boolean True)) (Just (Eval_Boolean True))
    
    test "Or eval: e1 is False, e2 is False simple" (eval $ Or (Boolean False) (Boolean False)) (Just (Eval_Boolean False))

    test "Or eval: e1 is False, e2 is not a boolean simple" (eval $ Or (Boolean False) (Integer 15)) (Just (Eval_Boolean False))
      
    test "Or eval: e1 is False, e2 is True complex" (eval $ (Or (Let "x" (Boolean False) (Var "x")) 
      (And (Boolean True) (Boolean True)))) (Just (Eval_Boolean True))
      
    test "Or eval: e1 is False, e2 is False complex" (eval $ (Or (Let "x" (Boolean False) (Var "x")) 
      (And (Boolean True) (Boolean False)))) (Just (Eval_Boolean False))  

    test "Or eval: e1 is False, e2 is not a boolean complex" (eval $ (Or (Let "x" (Boolean False) (Var "x")) 
      (Div (Float 5.5) (Integer 22)))) (Just (Eval_Boolean False))   
      
-- // Not tests 
    
    test "Not eval: e1 True" (eval $ Not (Boolean True)) (Just (Eval_Boolean False)) 

    test "Not eval: e1 False" (eval $ Not (Boolean False)) (Just (Eval_Boolean True)) 
    
    test "Not eval: e1 boolean complex" (eval $ Not (Or (Boolean False) (Boolean True)))
      (Just (Eval_Boolean False)) 

    test "Not eval: e1 boolean if complex" (eval $ Not (If (Boolean False)(Boolean True)(Boolean False)))
      (Just (Eval_Boolean True)) 

    test "Not eval: e1 not boolean" (eval $ Not (Integer 10)) (Nothing) 
    
    test "Not eval: e1 not boolean complex" (eval $ Not (Add (Integer 5) (Integer 10)))
      (Nothing)  

    -- // And, Or, Not complex tests 

    test "Complex boolean operator test 1" (eval $ If (Not (Let "x" (And (Boolean True) (Not (Boolean True))) (Or (Var "x") (Boolean True))))
      (Add (Integer 10) (Integer 15)) (Div (Integer 50) (Integer 25))) (Just (Eval_Integer 2)) 

    test "Complex boolean operator test 2" (eval $ If (Not (Let "x" (Or (Boolean False) (Not (Boolean True))) (And (Var "x") (Boolean True))))
      (Add (Integer 10) (Integer 15)) (Div (Integer 50) (Integer 25))) (Just (Eval_Integer 25))      

    -- // Cond Tests
    test "Cond eval: first true" (eval $ Cond [(Boolean True, (Add (Integer 5) (Integer 2)))])
       (Just (Eval_Integer 7))

    test "Cond eval: next true" (eval $ Cond [(Boolean False, (Add (Integer 5) (Integer 2))), 
        (Boolean True, (Div (Integer 4) (Integer 2)))])
       (Just (Eval_Integer 2))

    test "Cond eval: no true" (eval $ Cond [(Boolean False, (Add (Integer 5) (Integer 2))), 
        (Boolean False, (Div (Integer 4) (Integer 2)))])
       (Nothing)

    test "Cond eval: not boolean values" (eval $ Cond [(Float 5.1, (Add (Integer 5) (Integer 2))), 
        (Boolean False, (Div (Integer 4) (Integer 2)))])
       (Nothing)
       
    test "Cond Else eval: first true" (eval $ Cond [(Boolean True, (Add (Integer 5) (Integer 2))),
        (Else, (Sub (Integer 5) (Integer 2)))])
       (Just (Eval_Integer 7))

    test "Cond Else eval: next true" (eval $ Cond [(Boolean False, (Add (Integer 5) (Integer 2))), 
        (Boolean True, (Div (Integer 4) (Integer 2))), (Else, (Mul (Float 5.1) (Float 2.0)))])
       (Just (Eval_Integer 2))

    test "Cond Else eval: no true" (eval $ Cond [(Boolean False, (Add (Integer 5) (Integer 2))), 
        (Boolean False, (Div (Integer 4) (Integer 2))), (Else, Float 2.2)])
       (Just (Eval_Float 2.2))

    test "Cond Else eval: not boolean values" (eval $ Cond [(Float 5.1, (Add (Integer 5) (Integer 2))), 
        (Boolean False, (Div (Integer 4) (Integer 2))), (Else, Float 2.1)])
       (Nothing)

   -- // Less_Than Tests 
   
    test "Less_Than eval: eval e1 is Integer and eval e2 is Integer greater than e1 simple" 
     (eval $ Less_Than (Integer 5) (Integer 10)) (Just (Eval_Boolean True))  
     
    test "Less_Than eval: eval e1 is Integer and eval e2 is Integer less than e1 simple" 
     (eval $ Less_Than (Integer 10) (Integer 5)) (Just (Eval_Boolean False))    
     
    test "Less_Than eval: eval e1 is Integer and eval e2 is Float greater than e1 simple" 
     (eval $ Less_Than (Integer 5) (Float 10)) (Just (Eval_Boolean True))  
     
    test "Less_Than eval: eval e1 is Integer and eval e2 is Float less than e1 simple" 
     (eval $ Less_Than (Integer 10) (Float 5)) (Just (Eval_Boolean False))     

    test "Less_Than eval: eval e1 is Integer and eval e2 not a numeric type simple" 
     (eval $ Less_Than (Integer 5) (Boolean True)) (Nothing)   

    test "Less_Than eval: eval e1 is Integer and eval e2 is Integer greater than e1 complex" 
     (eval $ Less_Than (Sub (Integer 5) (Integer  7)) (Add (Integer 10) (Integer 20))) (Just (Eval_Boolean True))  
     
    test "Less_Than eval: eval e1 is Integer and eval e2 is Integer less than e1 complex" 
     (eval $ Less_Than (Add (Integer 10) (Integer 20)) (Sub (Integer 5) (Integer  7))) (Just (Eval_Boolean False))    
     
    test "Less_Than eval: eval e1 is Integer and eval e2 is Float greater than e1 complex" 
     (eval $ Less_Than (Sub (Integer 5) (Integer  7)) (Add (Integer 5) (Float 10))) (Just (Eval_Boolean True))  
     
    test "Less_Than eval: eval e1 is Integer and eval e2 is Float less than e1 complex" 
     (eval $ Less_Than (Mul (Integer 5) (Integer  7)) (Add (Integer 5) (Float 10))) (Just (Eval_Boolean False))     

    test "Less_Than eval: eval e1 is Integer and eval e2 not a numeric type complex" 
     (eval $ Less_Than (Integer 5) (And (Boolean True) (Boolean True))) (Nothing) 

    test "Less_Than eval: eval e1 is Float and eval e2 is Integer greater than e1 simple" 
     (eval $ Less_Than (Float 5) (Integer 10)) (Just (Eval_Boolean True))  
     
    test "Less_Than eval: eval e1 is Float and eval e2 is Integer less than e1 simple" 
     (eval $ Less_Than (Float 10) (Integer 5)) (Just (Eval_Boolean False))    
     
    test "Less_Than eval: eval e1 is Float and eval e2 is Float greater than e1 simple" 
     (eval $ Less_Than (Float 5) (Float 10)) (Just (Eval_Boolean True))  
     
    test "Less_Than eval: eval e1 is Float and eval e2 is Float less than e1 simple" 
     (eval $ Less_Than (Float 10) (Float 5)) (Just (Eval_Boolean False))     

    test "Less_Than eval: eval e1 is Float and eval e2 not a numeric type simple" 
     (eval $ Less_Than (Float 5) (Boolean True)) (Nothing)   

    test "Less_Than eval: eval e1 is Float and eval e2 is Integer greater than e1 complex" 
     (eval $ Less_Than (Sub (Float 5) (Integer  7)) (Add (Integer 10) (Integer 20))) (Just (Eval_Boolean True))  
     
    test "Less_Than eval: eval e1 is Float and eval e2 is Integer less than e1 complex" 
     (eval $ Less_Than (Add (Float 10) (Float 20)) (Sub (Integer 5) (Integer  7))) (Just (Eval_Boolean False))    
     
    test "Less_Than eval: eval e1 is Float and eval e2 is Float greater than e1 complex" 
     (eval $ Less_Than (Sub (Float 5) (Float  7)) (Add (Integer 5) (Float 10))) (Just (Eval_Boolean True))  
     
    test "Less_Than eval: eval e1 is Float and eval e2 is Float less than e1 complex" 
     (eval $ Less_Than (Mul (Float 5) (Float  7)) (Add (Integer 5) (Float 10))) (Just (Eval_Boolean False))     

    test "Less_Than eval: eval e1 is Float and eval e2 not a numeric type complex" 
     (eval $ Less_Than (Float 5) (And (Boolean True) (Boolean True))) (Nothing)     

    test "Less_Than eval: eval e1 is not numeric" 
     (eval $ Less_Than (Boolean True)(Integer 10)) (Nothing) 

    test "Less_Than eval: eval e1 and eval e2 equal ints should be false" 
     (eval $ Less_Than (Integer 10) (Integer 10)) (Just (Eval_Boolean False))

    test "Less_Than eval: eval e1 and eval e2 equal floats should be false" 
     (eval $ Less_Than (Float 10) (Float 10)) (Just (Eval_Boolean False))  


    -- // Greater_Than Tests 
   
    test "Greater_Than eval: eval e1 is Integer and eval e2 is Integer greater than e1 simple" 
     (eval $ Greater_Than (Integer 5) (Integer 10)) (Just (Eval_Boolean False))  
     
    test "Greater_Than eval: eval e1 is Integer and eval e2 is Integer less than e1 simple" 
     (eval $ Greater_Than (Integer 10) (Integer 5)) (Just (Eval_Boolean True))    
     
    test "Greater_Than eval: eval e1 is Integer and eval e2 is Float greater than e1 simple" 
     (eval $ Greater_Than (Integer 5) (Float 10)) (Just (Eval_Boolean False))  
     
    test "Greater_Than eval: eval e1 is Integer and eval e2 is Float less than e1 simple" 
     (eval $ Greater_Than (Integer 10) (Float 5)) (Just (Eval_Boolean True))     

    test "Greater_Than eval: eval e1 is Integer and eval e2 not a numeric type simple" 
     (eval $ Greater_Than (Integer 5) (Boolean True)) (Nothing)   

    test "Greater_Than eval: eval e1 is Integer and eval e2 is Integer greater than e1 complex" 
     (eval $ Greater_Than (Sub (Integer 5) (Integer  7)) (Add (Integer 10) (Integer 20))) (Just (Eval_Boolean False))  
     
    test "Greater_Than eval: eval e1 is Integer and eval e2 is Integer less than e1 complex" 
     (eval $ Greater_Than (Add (Integer 10) (Integer 20)) (Sub (Integer 5) (Integer  7))) (Just (Eval_Boolean True))    
     
    test "Greater_Than eval: eval e1 is Integer and eval e2 is Float greater than e1 complex" 
     (eval $ Greater_Than (Sub (Integer 5) (Integer  7)) (Add (Integer 5) (Float 10))) (Just (Eval_Boolean False))  
     
    test "Greater_Than eval: eval e1 is Integer and eval e2 is Float less than e1 complex" 
     (eval $ Greater_Than (Mul (Integer 5) (Integer  7)) (Add (Integer 5) (Float 10))) (Just (Eval_Boolean True))     

    test "Greater_Than eval: eval e1 is Integer and eval e2 not a numeric type complex" 
     (eval $ Greater_Than (Integer 5) (And (Boolean True) (Boolean True))) (Nothing) 

    test "Greater_Than eval: eval e1 is Float and eval e2 is Integer greater than e1 simple" 
     (eval $ Greater_Than (Float 5) (Integer 10)) (Just (Eval_Boolean False))  
     
    test "Greater_Than eval: eval e1 is Float and eval e2 is Integer less than e1 simple" 
     (eval $ Greater_Than (Float 10) (Integer 5)) (Just (Eval_Boolean True))    
     
    test "Greater_Than eval: eval e1 is Float and eval e2 is Float greater than e1 simple" 
     (eval $ Greater_Than (Float 5) (Float 10)) (Just (Eval_Boolean False))  
     
    test "Greater_Than eval: eval e1 is Float and eval e2 is Float less than e1 simple" 
     (eval $ Greater_Than (Float 10) (Float 5)) (Just (Eval_Boolean True))     

    test "Greater_Than eval: eval e1 is Float and eval e2 not a numeric type simple" 
     (eval $ Greater_Than (Float 5) (Boolean True)) (Nothing)   

    test "Greater_Than eval: eval e1 is Float and eval e2 is Integer greater than e1 complex" 
     (eval $ Greater_Than (Sub (Float 5) (Integer  7)) (Add (Integer 10) (Integer 20))) (Just (Eval_Boolean False))  
     
    test "Greater_Than eval: eval e1 is Float and eval e2 is Integer less than e1 complex" 
     (eval $ Greater_Than (Add (Float 10) (Float 20)) (Sub (Integer 5) (Integer  7))) (Just (Eval_Boolean True))    
     
    test "Greater_Than eval: eval e1 is Float and eval e2 is Float greater than e1 complex" 
     (eval $ Greater_Than (Sub (Float 5) (Float  7)) (Add (Integer 5) (Float 10))) (Just (Eval_Boolean False))  
     
    test "Greater_Than eval: eval e1 is Float and eval e2 is Float less than e1 complex" 
     (eval $ Greater_Than (Mul (Float 5) (Float  7)) (Add (Integer 5) (Float 10))) (Just (Eval_Boolean True))     

    test "Greater_Than eval: eval e1 is Float and eval e2 not a numeric type complex" 
     (eval $ Greater_Than (Float 5) (And (Boolean True) (Boolean True))) (Nothing)     

    test "Greater_Than eval: eval e1 is not numeric" 
     (eval $ Greater_Than (Boolean True)(Integer 10)) (Nothing) 

    test "Greater_Than eval: eval e1 and eval e2 equal ints should be false" 
     (eval $ Greater_Than (Integer 10) (Integer 10)) (Just (Eval_Boolean False))

    test "Greater_Than eval: eval e1 and eval e2 equal floats should be false" 
     (eval $ Greater_Than (Float 10) (Float 10)) (Just (Eval_Boolean False)) 


    -- // Equal_To Tests 
   
    test "Equal_To eval: eval e1 is Integer and eval e2 is Integer not equal to e1 simple" 
     (eval $ Equal_To (Integer 5) (Integer 10)) (Just (Eval_Boolean False))  
     
    test "Equal_To eval: eval e1 is Integer and eval e2 is Integer equal to e1 simple" 
     (eval $ Equal_To (Integer 5) (Integer 5)) (Just (Eval_Boolean True))    
     
    test "Equal_To eval: eval e1 is Integer and eval e2 is Float not equal to e1 simple" 
     (eval $ Equal_To (Integer 5) (Float 10)) (Just (Eval_Boolean False))  
     
    test "Equal_To eval: eval e1 is Integer and eval e2 is Float equal to e1 simple" 
     (eval $ Equal_To (Integer 5) (Float 5)) (Just (Eval_Boolean True))     

    test "Equal_To eval: eval e1 is Integer and eval e2 not a numeric type simple" 
     (eval $ Equal_To (Integer 5) (Boolean True)) (Nothing)   

    test "Equal_To eval: eval e1 is Integer and eval e2 is Integer not equal e1 complex" 
     (eval $ Equal_To (Sub (Integer 5) (Integer  7)) (Add (Integer 10) (Integer 20))) (Just (Eval_Boolean False))  
     
    test "Equal_To eval: eval e1 is Integer and eval e2 is Integer equal to e1 complex" 
     (eval $ Equal_To (Add (Integer 10) (Integer 20)) (Sub (Integer 35) (Integer  5))) (Just (Eval_Boolean True))    
     
    test "Equal_To eval: eval e1 is Integer and eval e2 is Float not equal to e1 complex" 
     (eval $ Equal_To (Sub (Integer 5) (Integer  7)) (Add (Integer 5) (Float 10))) (Just (Eval_Boolean False))  
     
    test "Equal_To eval: eval e1 is Integer and eval e2 is Float equal to e1 complex" 
     (eval $ Equal_To (Mul (Integer 5) (Integer  7)) (Add (Integer 25) (Float 10))) (Just (Eval_Boolean True))     

    test "Equal_To eval: eval e1 is Integer and eval e2 not a numeric type complex" 
     (eval $ Equal_To (Integer 5) (And (Boolean True) (Boolean True))) (Nothing) 

    test "Equal_To eval: eval e1 is Float and eval e2 is Integer not equal to e1 simple" 
     (eval $ Equal_To (Float 5) (Integer 10)) (Just (Eval_Boolean False))  
     
    test "Equal_To eval: eval e1 is Float and eval e2 is Integer equal to e1 simple" 
     (eval $ Equal_To (Float 10) (Integer 10)) (Just (Eval_Boolean True))    
     
    test "Equal_To eval: eval e1 is Float and eval e2 is Float not equal to e1 simple" 
     (eval $ Equal_To (Float 5) (Float 10)) (Just (Eval_Boolean False))  
     
    test "Equal_To eval: eval e1 is Float and eval e2 is Float equal to e1 simple" 
     (eval $ Equal_To (Float 10) (Float 10)) (Just (Eval_Boolean True))     

    test "Equal_To eval: eval e1 is Float and eval e2 not a numeric type simple" 
     (eval $ Equal_To (Float 5) (Boolean True)) (Nothing)   

    test "Equal_To eval: eval e1 is Float and eval e2 is Integer not equal to e1 complex" 
     (eval $ Equal_To (Sub (Float 5) (Integer  7)) (Add (Integer 10) (Integer 20))) (Just (Eval_Boolean False))  
     
    test "Equal_To eval: eval e1 is Float and eval e2 is Integer equal to e1 complex" 
     (eval $ Equal_To (Add (Float 10) (Float 20)) (Sub (Integer 35) (Integer  5))) (Just (Eval_Boolean True))    
     
    test "Equal_To eval: eval e1 is Float and eval e2 is Float not equal to e1 complex" 
     (eval $ Equal_To (Sub (Float 5) (Float  7)) (Add (Integer 5) (Float 10))) (Just (Eval_Boolean False))  
     
    test "Equal_To eval: eval e1 is Float and eval e2 is Float equal to e1 complex" 
     (eval $ Equal_To (Mul (Float 5) (Float  7)) (Add (Integer 25) (Float 10))) (Just (Eval_Boolean True))     

    test "Equal_To eval: eval e1 is Float and eval e2 not a numeric type complex" 
     (eval $ Equal_To (Float 5) (And (Boolean True) (Boolean True))) (Nothing)     

    test "Equal_To eval: eval e1 is a boolean equal to eval e2 also boolean" 
     (eval $ Equal_To (Boolean True)(Boolean True)) (Just (Eval_Boolean True)) 

    test "Equal_To eval: eval e1 is a boolean not equal to eval e2 also boolean" 
     (eval $ Equal_To (Boolean True)(Boolean False)) (Just (Eval_Boolean False))  

    test "Equal_To eval: eval e1 is a Nothing and eval e2 also Nothing" 
     (eval $ Equal_To (Sub (Integer 5) (Boolean True))(Add (Integer 5) (Boolean False))) (Just (Eval_Boolean True)) 

    test "Equal_To eval: eval e1 is a Nothing  not equal to eval e2 also boolean" 
     (eval $ Equal_To (Sub (Integer 5) (Boolean True))(Boolean False)) (Nothing)  


    -- Cond If equality tests 

    test "Cond and If are same test 1" (eval $ If (Boolean True) (Add (Integer 5) (Integer 2)) (Sub (Integer 5) (Integer 2)))
     (eval $ Cond [(Boolean True, (Add (Integer 5) (Integer 2))), (Else, (Sub (Integer 5) (Integer 2)))])  

    test "Cond and If are same test 2" (eval $ If (Boolean False) (Add (Integer 5) (Integer 2)) 
     (If (Boolean True) (Sub (Integer 5) (Integer 2)) (Mul (Integer 5) (Integer 2)))) 
       (eval $ Cond [(Boolean False, (Add (Integer 5) (Integer 2))), (Boolean True, (Sub (Integer 5) (Integer 2))), 
         (Else, (Mul (Integer 5) (Integer 2)))])
 
      
     


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
 Added Less_Than, Greater_Than, and Equal for part 4
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
subst x v (Less_Than e1 e2) = Less_Than (subst x v e1) (subst x v e2)
subst x v (Greater_Than e1 e2) = Greater_Than (subst x v e1) (subst x v e2)  
subst x v (Equal_To e1 e2) = Equal_To (subst x v e1) (subst x v e2) 
subst x v (Cond l) = Cond (substTupleListHelper x v l)    
subst _ _ (Else) = Else       

-- Function that is a helper for subst that handles the Cond case by 
-- using recursion to call subst on every element in the Cond tuple list.
substTupleListHelper :: Variable -> ExprEval -> [(Expr, Expr)] -> [(Expr, Expr)]
substTupleListHelper _ _ [] = []
substTupleListHelper x v ((t1, t2):ts) = ((subst x v t1), (subst x v t2)) : substTupleListHelper x v ts

test_substTupleListHelper = do 

    test "substTupleListHelper basic test" (substTupleListHelper "x" (Eval_Integer 10) []) [] 

    test "substTupleListHelper complex test 1" (substTupleListHelper "x" (Eval_Integer 15) 
     [(Var "x", Integer 10)]) [(Integer 15, Integer 10)]

    test "substTupleListHelper complex test 2" (substTupleListHelper "x" (Eval_Integer 15) 
     [(Var "x", Integer 10), (Float 5.5, Var "x")]) [(Integer 15, Integer 10), (Float 5.5, Integer 15)] 

    test "substTupleListHelper complex test 3" (substTupleListHelper "x" (Eval_Integer 15) 
     [(Var "y", Integer 10), (Float 5.5, Var "y")]) [(Var "y", Integer 10), (Float 5.5,  Var "y")]  

    test "substTupleListHelper complex test with Else" (substTupleListHelper "x" (Eval_Integer 15) 
     [(Var "x", Integer 10), (Else, Var "x")]) [(Integer 15, Integer 10), (Else, Integer 15)]  

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

    -- Less_Than tests 

    test "subst Less_Than test No subst" (subst "x" (Eval_Integer 5) (Less_Than (Boolean True) (Float 5.1))) 
      (Less_Than (Boolean True) (Float 5.1))  

    test "subst Less_Than test Subst into e1" (subst "x" (Eval_Integer 5) (Less_Than (Var "x") (Float 5.1))) 
      (Less_Than (Integer 5) (Float 5.1))    

    test "subst Less_Than test Subst into e2" (subst "x" (Eval_Integer 5) (Less_Than (Boolean True) (Var "x"))) 
      (Less_Than (Boolean True) (Integer 5))   

    test "subst Less_Than test Subst into e2 with other variable present" (subst "x" (Eval_Integer 5) (Less_Than (Var "y") (Var "x"))) 
      (Less_Than (Var "y") (Integer 5))   

    test "subst Less_Than test Subst into a let" (subst "x" (Eval_Integer 5) (Less_Than (Boolean True) 
      (Let "y" (Add (Var "y") (Integer 6)) (Sub (Var "x") (Integer 16)))))
        (Less_Than (Boolean True) (Let "y" (Add (Var "y") (Integer 6)) 
          (Sub (Integer 5) (Integer 16))))   

    -- Greater_Than tests 

    test "subst Greater_Than test No subst" (subst "x" (Eval_Integer 5) (Greater_Than (Boolean True) (Float 5.1))) 
      (Greater_Than (Boolean True) (Float 5.1))  

    test "subst Greater_Than test Subst into e1" (subst "x" (Eval_Integer 5) (Greater_Than (Var "x") (Float 5.1))) 
      (Greater_Than (Integer 5) (Float 5.1))    

    test "subst Greater_Than test Subst into e2" (subst "x" (Eval_Integer 5) (Greater_Than (Boolean True) (Var "x"))) 
      (Greater_Than (Boolean True) (Integer 5))   

    test "subst Greater_Than test Subst into e2 with other variable present" (subst "x" (Eval_Integer 5) (Greater_Than (Var "y") (Var "x"))) 
      (Greater_Than (Var "y") (Integer 5))   

    test "subst Greater_Than test Subst into a let" (subst "x" (Eval_Integer 5) (Greater_Than (Boolean True) 
      (Let "y" (Add (Var "y") (Integer 6)) (Sub (Var "x") (Integer 16)))))
        (Greater_Than (Boolean True) (Let "y" (Add (Var "y") (Integer 6)) 
          (Sub (Integer 5) (Integer 16))))    

    -- Equal_To tests 

    test "subst Equal test No subst" (subst "x" (Eval_Integer 5) (Equal_To (Boolean True) (Float 5.1))) 
      (Equal_To (Boolean True) (Float 5.1))  

    test "subst Equal test Subst into e1" (subst "x" (Eval_Integer 5) (Equal_To (Var "x") (Float 5.1))) 
      (Equal_To (Integer 5) (Float 5.1))    

    test "subst Equal test Subst into e2" (subst "x" (Eval_Integer 5) (Equal_To (Boolean True) (Var "x"))) 
      (Equal_To (Boolean True) (Integer 5))   

    test "subst Equal test Subst into e2 with other variable present" (subst "x" (Eval_Integer 5) (Equal_To (Var "y") (Var "x"))) 
      (Equal_To (Var "y") (Integer 5))   

    test "subst Equal test Subst into a let" (subst "x" (Eval_Integer 5) (Equal_To (Boolean True) 
      (Let "y" (Add (Var "y") (Integer 6)) (Sub (Var "x") (Integer 16)))))
        (Equal_To (Boolean True) (Let "y" (Add (Var "y") (Integer 6)) 
          (Sub (Integer 5) (Integer 16))))        


    -- Cond tests 

    test "subst Cond basic test" (subst "x" (Eval_Integer 10) (Cond [])) (Cond []) 

    test "subst Cond complex test 1" (subst"x" (Eval_Integer 15) 
     (Cond [(Var "x", Integer 10)])) (Cond [(Integer 15, Integer 10)])

    test "subst Cond complex test 2" (subst "x" (Eval_Integer 15) 
     (Cond [(Var "x", Integer 10), (Float 5.5, Var "x")])) (Cond [(Integer 15, Integer 10), (Float 5.5, Integer 15)])

    test "subst Cond complex test 3" (subst "x" (Eval_Integer 15) 
     (Cond [(Var "y", Integer 10), (Float 5.5, Var "y")])) (Cond [(Var "y", Integer 10), (Float 5.5,  Var "y")])  

    test "subst Cond complex test with Else" (subst "x" (Eval_Integer 15) 
     (Cond [(Var "x", Integer 10), (Else, Var "x")])) (Cond [(Integer 15, Integer 10), (Else, Integer 15)])                        
                           


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

    -- And tests
    test "And runSExpression Test 1" (runSExpression $ S.List [S.Symbol "And" , S.Boolean True, S.Integer 10]) 
        (Nothing)   

    test "And runSExpression Test 2" (runSExpression $ S.List [
        S.Symbol "And" , S.Boolean False, S.List [S.Symbol "Let", S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
        (Just $ S.Boolean False)       

    test "And runSExpression Test 3" (runSExpression $ S.List [
        S.Symbol "And" , S.List [S.Symbol "And" , S.Integer 10, S.Real 15.1], 
         S.List [S.Symbol "Let", S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
        (Nothing)    

    test "And runSExpression Test 4" (runSExpression $ S.List [S.Symbol "And" , S.Boolean True, S.Boolean False]) 
        (Just $ S.Boolean False)
      
    test "And runSExpression Test 5" (runSExpression $ S.List [S.Symbol "And" , S.Boolean True, S.Boolean True]) 
        (Just $ S.Boolean True)

    -- Or tests
    test "Or runSExpression Test 1" (runSExpression $ S.List [
        S.Symbol "Or" , S.Boolean True, S.Integer 10]) 
        (Just $ S.Boolean True)

    test "Or runSExpression Test 2" (runSExpression $ S.List [
        S.Symbol "Or" , S.Boolean False, S.List [S.Symbol "Let", S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
        (Just $ S.Boolean False)    

    test "Or runSExpression Test 3" (runSExpression $ S.List [
        S.Symbol "Or" , S.List [S.Symbol "Or" , S.Integer 10, S.Real 15.1], 
         S.List [S.Symbol "Let", S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
        (Nothing)    

    test "Or runSExpression Test 4" (runSExpression $ S.List [
        S.Symbol "Or" , S.Boolean True, S.Boolean False]) 
        (Just $ S.Boolean True)

    test "Or runSExpression Test 5" (runSExpression $ S.List [
        S.Symbol "Or" , S.Boolean False, S.Boolean False]) 
        (Just $ S.Boolean False)

    -- Not tests
    test "Not runSExpression Test 1" (runSExpression $ S.List [
        S.Symbol "Not" , S.Boolean True]) 
        (Just $ S.Boolean False)

    test "Not fromSExpression Test 2" (runSExpression $ S.List [
        S.Symbol "Not" , S.List [S.Symbol "Let", S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
        (Nothing)      

    test "Not fromSExpression Test 3" (runSExpression $ S.List [
        S.Symbol "Not" , S.List [S.Symbol "Or" , S.Integer 10, 
         S.List [S.Symbol "Let", S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]]) 
        (Nothing)  

    test "Not runSExpression Test 4" (runSExpression $ S.List [
        S.Symbol "Not" , S.Boolean False]) 
        (Just $ S.Boolean True)     

    -- //Less_Than tests 
    test "Less_Than runSExpression Test 1" (runSExpression $ S.List [
        S.Symbol "Less_Than", S.Boolean True, S.Integer 10]) 
        (Nothing)

    test "Less_Than runSExpression Test 2" (runSExpression $ S.List [
        S.Symbol "Less_Than", S.Integer 30, S.List [S.Symbol "Let", S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
        (Just $ S.Boolean False)    

    test "Less_Than runSExpression Test 3" (runSExpression $ S.List [
         S.Symbol "Less_Than", S.List [S.Symbol "Let", S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]], S.Integer 30]) 
        (Just $ S.Boolean True)      

    test "Less_Than runSExpression Test 4" (runSExpression $ S.List [
        S.Symbol "Less_Than", S.Real 15.1, S.Real 13.2]) 
        (Just $ S.Boolean False)

    test "Less_Than runSExpression Test 5" (runSExpression $ S.List [
        S.Symbol "Less_Than", S.Integer 5, S.Integer 6]) 
        (Just $ S.Boolean True)

    -- //Greater_Than tests 
    test "Greater_Than runSExpression Test 1" (runSExpression $ S.List [
        S.Symbol "Greater_Than" , S.Boolean True, S.Integer 10]) 
        (Nothing)

    test "Greater_Than runSExpression Test 2" (runSExpression $ S.List [
        S.Symbol "Greater_Than" , S.Integer 30, S.List [S.Symbol "Let", S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
        (Just $ S.Boolean True)    

    test "Greater_Than runSExpression Test 3" (runSExpression $ S.List [
         S.Symbol "Greater_Than" , S.List [S.Symbol "Let", S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]], S.Integer 30]) 
        (Just $ S.Boolean False)      

    test "Greater_Than runSExpression Test 4" (runSExpression $ S.List [
        S.Symbol "Greater_Than" , S.Real 15.1, S.Real 13.2]) 
        (Just $ S.Boolean True)

    test "Greater_Than runSExpression Test 5" (runSExpression $ S.List [
        S.Symbol "Greater_Than" , S.Integer 5, S.Integer 6]) 
        (Just $ S.Boolean False)

     -- //Equal_To tests 
    test "Equal_To runSExpression Test 1" (runSExpression $ S.List [
        S.Symbol "Equal_To" , S.Boolean True, S.Integer 10]) 
        (Nothing)

    test "Equal_To runSExpression Test 2" (runSExpression $ S.List [
        S.Symbol "Equal_To" , S.Real 15.4, S.List [S.Symbol "Let", S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.2], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
        (Just $ S.Boolean True)    

    test "Equal_To runSExpression Test 3" (runSExpression $ S.List [
         S.Symbol "Equal_To" , S.List [S.Symbol "Let", S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.0, S.Real 4.0], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.0]], S.Integer 15]) 
        (Just $ S.Boolean True)      

    test "Equal_To runSExpression Test 4" (runSExpression $ S.List [
        S.Symbol "Equal_To" , S.Integer 15, S.Integer 13]) 
        (Just $ S.Boolean False)

    test "Equal_To runSExpression Test 5" (runSExpression $ S.List [
        S.Symbol "Equal_To" , S.Integer 5, S.Integer 5]) 
        (Just $ S.Boolean True) 
    
    test "Equal_To runSExpression Test 6" (runSExpression $ S.List [
        S.Symbol "Equal_To" , S.Real 5.0, S.Integer 5]) 
        (Just $ S.Boolean True) 

    -- // Cond and Else tests
    test "Cond runSExpression Test 1" (runSExpression $ S.List[S.Symbol "Cond", S.List[S.List[S.Boolean True, 
        S.List[S.Symbol "+", S.Integer 3, S.Integer 2]]]])
        (Just $ S.Integer 5)

    test "Cond runSExpression Test 2" (runSExpression $ S.List[S.Symbol "Cond", S.List[S.List[S.Boolean False, 
        S.List[S.Symbol "-", S.Integer 3, S.Integer 2]], S.List[S.Boolean True, 
          S.List[S.Symbol "+", S.Integer 3, S.Integer 1]]]])
        (Just $ S.Integer 4)
        
    test "Cond runSExpression Test 3" (runSExpression $ S.List[S.Symbol "Cond", S.List[S.List[S.Boolean False, 
        S.List[S.Symbol "-", S.Integer 3, S.Integer 2]], S.List[S.Boolean False, 
          S.List[S.Symbol "+", S.Integer 3, S.Integer 1]], S.List[S.Symbol "Else", S.List[S.Symbol "/", S.Integer 3, S.Integer 1]]]])
        (Just $ S.Integer 3)

    test "Cond runSExpression Test 4" (runSExpression $ S.List[S.Symbol "Cond", S.List[S.List[S.Boolean False, 
        S.List[S.Symbol "-", S.Integer 3, S.Integer 2]], S.List[S.Boolean True, 
          S.List[S.Symbol "+", S.Integer 3, S.Integer 1]], S.List[S.Symbol "Else", S.List[S.Symbol "/", S.Integer 3, S.Integer 1]]]])
        (Just $ S.Integer 4)

    test "Cond runSExpression Test 5" (runSExpression $ S.List[S.Symbol "Cond", S.List[S.List[S.Real 5.3, 
        S.List[S.Symbol "+", S.Integer 3, S.Integer 2]]]])
        (Nothing)

    test "Cond runSExpression Test 6" (runSExpression $ S.List[S.Symbol "Cond", S.List[S.List[S.Integer 1, 
        S.List[S.Symbol "-", S.Integer 3, S.Integer 2]], S.List[S.Boolean False, 
          S.List[S.Symbol "+", S.Integer 3, S.Integer 1]], S.List[S.Symbol "Else", S.List[S.Symbol "/", S.Integer 3, S.Integer 1]]]])
        (Nothing)
    
    -- // Complex Boolean tests
    test "Not runSExpression complex Test 1" (runSExpression $ S.List [
        S.Symbol "Not" , S.List [S.Symbol "Or", S.Boolean True, S.Boolean True]]) 
        (Just $ S.Boolean False)

    test "Not runSExpression complex Test 2" (runSExpression $ S.List [
        S.Symbol "Not" , S.List [S.Symbol "And", S.Boolean True, S.Boolean True]]) 
        (Just $ S.Boolean False)

    test "Not runSExpression complex Test 3" (runSExpression $ S.List [
        S.Symbol "And" , S.List [S.Symbol "Not", S.Boolean True], 
          S.List [S.Symbol "Or", S.Boolean False, S.Boolean True]]) 
        (Just $ S.Boolean False)    