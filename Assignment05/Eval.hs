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

import Prelude hiding (Left, Right)

import qualified SExpression as S

import Maps (Map, get, set, empty)

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
 

-- ================================================================================================


ex_program1 = Program [Defun "incr" "x" (Add (Var "x") (Integer 1))] 
                 (Call "incr" (Call "incr" (Call "incr" (Integer 1))))
ex_program2 = Program [Defun "f" "x" (Add (Var "x") (Var "y"))]
                 (Let "y" (Integer 10) (Call "f" (Integer 10)))
ex_program3 = Program [Defun "incr" "x" (Add (Var "x") (Integer 1))] 
                 (Let "z" (Integer 20) (Call "incr" (Var "z")))

ex_program4 = Program 
                [ Defun "fact" "n" 
                    (If  
                      (Equal_To (Integer 0) (Var "n"))
                      (Integer 1) 
                      (Mul (Var "n") (Call "fact" (Sub (Var "n") (Integer 1)))))]
                (Call "fact" (Integer 5))  

ex_program5 = Program 
                [ Defun "fact" "n" 
                    (If  
                      (Equal_To (Integer 0) (Var "n"))
                      (Integer 1) 
                      (Mul (Var "n") (Call "fact" (Sub (Var "n") (Integer 1))))), 
                      Defun "incr" "x" (Add (Var "x") (Integer 1))]
                (Call "incr" (Call "fact" (Integer 5)))        

ex_program6 = Program 
                [ Defun "fact" "n" 
                    (If  
                      (Equal_To (Integer 0) (Var "n"))
                      (Integer 1) 
                      (Mul (Var "n") (Call "fact" (Sub (Var "n") (Integer 1))))), 
                      Defun "incr" "x" (Add (Var "x") (Integer 1)),
                      Define "z" (Integer 10)]
                (Add (Var "z") (Call "incr" (Call "fact" (Integer 5))))   

ex_program7 = Program 
                [ Defun "fact" "n" 
                    (If  
                      (Equal_To (Integer 0) (Var "n"))
                      (Integer 1) 
                      (Mul (Var "n") (Call "fact" (Sub (Var "n") (Integer 1))))), 
                      Defun "incr" "x" (Add (Var "x") (Integer 1)),
                      Define "z" (Integer 10),
                      Define "a" (Boolean False)]
                (If (Var "a") (Boolean True) (Add (Var "z") (Call "incr" (Call "fact" (Integer 5)))))              

ex_program8 = Program [Defun "incr" "x" (Add (Var "x") (Integer 1))] 
                 (Call "incr" (Call "incr" (Let "incr" (Integer 5) (Var "incr"))))    

ex_program9 = Program [Define "x" (Integer 2)] 
                 (Add (Var "x") (Let "x" (Integer 1) (Var "x")))    

ex_program10 = Program [Define "x" (Integer 2)] 
                 (Call "x" (Integer 1))                                                                       


evalProgram :: Program -> Maybe ExprEval
evalProgram (Program globalDefs e) = eval globals empty e
  where 
    globals = collectDefs (reverse globalDefs)
    collectDefs [] = empty
    collectDefs (Defun f x body : globalDefs) = 
        set (collectDefs globalDefs) f (Defun f x body)
    collectDefs (Define v e : globalDefs) = 
        set (collectDefs globalDefs) v (Define v e)    


test_evalProgram = do 
    test "evalProgram empty globalDefs and simple expression" (evalProgram $ Program [] (Integer 10))
     (Just (Eval_Integer 10))    

    test "evalProgram single variable globalDefs and simple expression" (evalProgram $ Program 
     [Define "x" (Integer 10)] (Var "x"))
     (Just (Eval_Integer 10))  

    test "evalProgram multiple variable globalDefs and simple expression" (evalProgram $ Program 
     [Define "x" (Integer 10), Define "y" (Integer 20)] (Add (Var "y") (Var "x")))
     (Just (Eval_Integer 30))  

    test "evalProgram multiple of same variable globalDefs and simple expression" (evalProgram $ Program 
     [Define "x" (Integer 10), Define "x" (Integer 20)] (Add (Var "x") (Var "x")))
     (Just (Eval_Integer 40))       

    test "evalProgram single function and simple expression 1" (evalProgram ex_program1)  
     (Just (Eval_Integer 4))  

    test "evalProgram single function and simple expression 2" (evalProgram ex_program2)  
     (Nothing)  

    test "evalProgram single function and simple expression 3" (evalProgram ex_program3)  
     (Just (Eval_Integer 21))  

    test "evalProgram single function and simple expression 4" (evalProgram ex_program4)  
     (Just (Eval_Integer 120))     

    test "evalProgram multiple functions" (evalProgram ex_program5)  
     (Just (Eval_Integer 121))  

    test "evalProgram multiple functions and a variable" (evalProgram ex_program6)  
     (Just (Eval_Integer 131)) 

    test "evalProgram multiple functions and multiple variables" (evalProgram ex_program7)  
     (Just (Eval_Integer 131))  

    test "evalProgram function with same name as let variable" (evalProgram ex_program8)  
     (Just (Eval_Integer 7))

    test "evalProgram variable with same name as let variable" (evalProgram ex_program9)    
     (Just (Eval_Integer 3)) 

    test "evalProgram global variable called like a function" (evalProgram ex_program10)
     (Nothing) 

    

 -- ===============================================================================================

-- |Evaluates the given expression to a value.
{-
 For Assignment 5: 
 Added Pair, Left, and Right cases for Question 1.
 Added the five predicate cases for Question 2.  
 Also fixed up add, sub, mul, div, and let to now account 
 for the Eval_Pair possibility. For the math operations, code got 
 simpler since eval boolean, eval pair, and nothing go to nothing,
 but for let needed to add an actual case. 
 Also fixed Cond/Else stuff now that we use a Maybe Expr for the else case
 Rather than having an Else Expr type. 
-}
eval :: GlobalEnv -> Env -> Expr -> Maybe ExprEval 
eval g m (Integer i) = Just (Eval_Integer i)
eval g m (Float d) = Just (Eval_Float d)
eval g m (Boolean b) = Just (Eval_Boolean b)
eval g m (Var x) =
    case get m x of
         Just v -> Just v
         _ -> case get g x of 
                   Just (Define _ v) -> eval g m v
                   _ -> Nothing
eval g m (Add e1 e2) =
    case eval g m e1 of
         Just (Eval_Integer v1) ->
            case eval g m e2 of
                 Just (Eval_Integer v2) -> Just (Eval_Integer (v1 + v2))
                 Just (Eval_Float v2) -> Just (Eval_Float ((fromInteger v1) + v2))
                 _ -> Nothing
         Just (Eval_Float v1) -> 
            case eval g m e2 of 
                 Just (Eval_Integer v2) -> Just (Eval_Float(v1 + (fromInteger v2)))
                 Just (Eval_Float v2) -> Just (Eval_Float (v1 + v2))
                 _ -> Nothing
         _ -> Nothing    
eval g m (Sub e1 e2) =
    case eval g m e1 of
         Just (Eval_Integer v1) ->
            case eval g m e2 of
                 Just (Eval_Integer v2) -> Just (Eval_Integer (v1 - v2))
                 Just (Eval_Float v2) -> Just (Eval_Float ((fromInteger v1) - v2))
                 _ -> Nothing
         Just (Eval_Float v1) -> 
            case eval g m e2 of 
                 Just (Eval_Integer v2) -> Just (Eval_Float(v1 - (fromInteger v2)))
                 Just (Eval_Float v2) -> Just (Eval_Float (v1 - v2))
                 _ -> Nothing
         _ -> Nothing    
eval g m (Mul e1 e2) =
    case eval g m e1 of
         Just (Eval_Integer v1) ->
            case eval g m e2 of
                 Just (Eval_Integer v2) -> Just (Eval_Integer (v1 * v2))
                 Just (Eval_Float v2) -> Just (Eval_Float ((fromInteger v1) * v2))
                 _ -> Nothing
         Just (Eval_Float v1) -> 
            case eval g m e2 of 
                 Just (Eval_Integer v2) -> Just (Eval_Float(v1 * (fromInteger v2)))
                 Just (Eval_Float v2) -> Just (Eval_Float (v1 * v2))
                 _ -> Nothing
         _ -> Nothing         
eval g m (Div e1 e2) =
    case eval g m e1 of
         Just (Eval_Integer v1) ->
            case eval g m e2 of
                 Just (Eval_Integer v2) -> Just (Eval_Integer (v1 `div` v2))
                 Just (Eval_Float v2) -> Just (Eval_Float ((fromInteger v1) / v2))
                 _ -> Nothing
         Just (Eval_Float v1) -> 
            case eval g m e2 of 
                 Just (Eval_Integer v2) -> Just (Eval_Float(v1 / (fromInteger v2)))
                 Just (Eval_Float v2) -> Just (Eval_Float (v1 / v2))
                 _ -> Nothing
         _ -> Nothing      
eval g m (Let x e1 e2) =
    case eval g m e1 of
         Just v -> eval g (set m x v) e2
         Nothing -> (Nothing)
eval g m (Call f e) =
    case get g f of
         Just (Defun _ x body) ->
             case eval g m e of 
                  Just v -> eval g (set empty x v) body                       
-- If eval e1 is true then return e2, if false return e3, else return Nothing because 
-- did not receive boolean for e1.          
eval g m (If e1 e2 e3) = 
     case eval g m e1 of 
          Just (Eval_Boolean True) -> eval g m e2 
          Just (Eval_Boolean False) -> eval g m e3 
          _ -> Nothing 
-- If eval e1 is True then check e2 for either being a boolean to return or anything else returns nothing
-- because and needs booleans. If eval e1 is False then short circuit and return false. Otherwise
-- that means e1 was not a boolean so return Nothing.          
eval g m (And e1 e2) = 
     case eval g m e1 of 
          Just (Eval_Boolean True) -> 
            case eval g m e2 of 
              Just (Eval_Boolean b) -> Just (Eval_Boolean b)
              _ -> Nothing 
          Just (Eval_Boolean False) -> Just (Eval_Boolean False)
          _ -> Nothing     
-- For or, if e1 is True then return True. If e1 is false then evaluate e2, so then
-- if e2 is a boolean return that, otherwise return False or Nothing is still False.
-- If e1 is not a boolean than evaluate e2, and if boolean return that or if not return nothing 
-- because once again Nothing | Boolean should be that Boolean.       
eval g m (Or e1 e2) = 
     case eval g m e1 of 
          Just (Eval_Boolean True) -> Just (Eval_Boolean True)
          Just (Eval_Boolean False) -> 
            case eval g m e2 of 
              Just (Eval_Boolean b) -> Just (Eval_Boolean b)
              _ -> Just (Eval_Boolean False)
          _ -> 
            case eval g m e2 of 
              Just (Eval_Boolean b) -> Just (Eval_Boolean b)
              _ -> Nothing 

-- Not changes eval of e1 true to false, false to true and anything else to Nothing.         
eval g m (Not e) = 
     case eval g m e of
          Just (Eval_Boolean True) -> Just (Eval_Boolean False)
          Just (Eval_Boolean False) -> Just (Eval_Boolean True)      
          _ -> Nothing                   

-- Less than checks what eval e1 is and then compares it with eval e2. 
-- If eval e1 is a integer, and eval e2 is an integer or float then compare with the < 
-- otherwise return nothing. If eval e1 is a float then do the same thing. Just need 
-- to convert ints to floats when the other element is a float. 
-- Lastly, if eval e1 is not an integer or float (Nothing or Boolean) then return Nothing. 
eval g m (Less_Than e1 e2) =
    case eval g m e1 of
         Just (Eval_Integer v1) ->
            case eval g m e2 of
                 Just (Eval_Integer v2) -> Just (Eval_Boolean (v1 < v2))
                 Just (Eval_Float v2) -> Just (Eval_Boolean ((fromInteger v1) < v2))
                 _ -> Nothing
         Just (Eval_Float v1) -> 
            case eval g m e2 of 
                 Just (Eval_Integer v2) -> Just (Eval_Boolean(v1 < (fromInteger v2)))
                 Just (Eval_Float v2) -> Just (Eval_Boolean (v1 < v2))
                 _ -> Nothing
         _ -> Nothing  

-- Greater than checks what eval e1 is and then compares it with eval e2. 
-- If eval e1 is a integer, and eval e2 is an integer or float then compare with the >
-- otherwise return nothing. If eval e1 is a float then do the same thing. Just need 
-- to convert ints to floats when the other element is a float. 
-- Lastly, if eval e1 is not an integer or float (Nothing or Boolean) then return Nothing. 
eval g m (Greater_Than e1 e2) =
    case eval g m e1 of
         Just (Eval_Integer v1) ->
            case eval g m e2 of
                 Just (Eval_Integer v2) -> Just (Eval_Boolean (v1 > v2))
                 Just (Eval_Float v2) -> Just (Eval_Boolean ((fromInteger v1) > v2))
                 _ -> Nothing
         Just (Eval_Float v1) -> 
            case eval g m e2 of 
                 Just (Eval_Integer v2) -> Just (Eval_Boolean (v1 > (fromInteger v2)))
                 Just (Eval_Float v2) -> Just (Eval_Boolean (v1 > v2))
                 _ -> Nothing
         _ -> Nothing 

-- Equals works similarly to less than and greater than for eval e1 being an Integer or Float. 
-- But now can check booleans and also if both eval e1 and eval e2 are nothing then return true. 
eval g m (Equal_To e1 e2) =
    case eval g m e1 of
         Just (Eval_Integer v1) ->
            case eval g m e2 of
                 Just (Eval_Integer v2) -> Just (Eval_Boolean (v1 == v2))
                 Just (Eval_Float v2) -> Just (Eval_Boolean ((fromInteger v1) == v2))
                 _ -> Nothing
         Just (Eval_Float v1) -> 
            case eval g m e2 of 
                 Just (Eval_Integer v2) -> Just (Eval_Boolean (v1 == (fromInteger v2)))
                 Just (Eval_Float v2) -> Just (Eval_Boolean (v1 == v2))
                 _ -> Nothing
         Just (Eval_Boolean v1) -> 
            case eval g m e2 of 
                Just (Eval_Boolean v2) -> Just (Eval_Boolean (v1 == v2))
                _ -> Nothing 
         Nothing -> 
             case eval g m e2 of 
                 Nothing -> Just (Eval_Boolean (True))
                 _ -> Nothing     
eval g m (Cond x y) = (evalTupleListHelper g m x y)  
-- Pair needs to make sure that both eval e1 and eval e2 are values
-- otherwise return nothing. 
eval g m (Pair e1 e2) = 
     case eval g m e1 of 
       (Just x) -> case eval g m e2 of 
                      Just y -> Just (Eval_Pair x y) 
                      _ -> Nothing
       Nothing -> Nothing 
-- Left needs that eval of l to be a pair otherwise there is nothing
-- to take a left from.        
eval g m (Left l ) = 
    case eval g m l of 
         Just (Eval_Pair e1 e2) -> Just e1 
         _ -> Nothing 
-- Right needs that eval of l to be a pair otherwise there is nothing
-- to take a right from.          
eval g m (Right l ) = 
    case eval g m l of 
         Just (Eval_Pair e1 e2) -> Just e2
         _ -> Nothing 
-- Real_Pred returns true is eval e is a float, otherwise return false.          
eval g m (Real_Pred e) = case eval g m e of 
                          Just (Eval_Float _) -> Just (Eval_Boolean True)        
                          _ -> Just (Eval_Boolean False)
-- Integer_Pred returns true is eval e is a integer, otherwise return false.                          
eval g m (Integer_Pred e) = case eval g m e of 
                          Just (Eval_Integer _) -> Just (Eval_Boolean True)        
                          _ -> Just (Eval_Boolean False)
-- Number_Pred returns true is eval e is a float or integer, otherwise return false.
eval g m (Number_Pred e) = case eval g m e of 
                          Just (Eval_Float _) -> Just (Eval_Boolean True) 
                          Just (Eval_Integer _) -> Just (Eval_Boolean True)       
                          _ -> Just (Eval_Boolean False)
-- Boolean_Pred returns true is eval e is a boolean, otherwise return false.                          
eval g m (Boolean_Pred e) = case eval g m e of 
                          Just (Eval_Boolean _) -> Just (Eval_Boolean True)        
                          _ -> Just (Eval_Boolean False)               
-- Pair_Pred returns true is eval e is a pair, otherwise return false.                                     
eval g m (Pair_Pred e) = case eval g m e of 
                          Just (Eval_Pair _ _) -> Just (Eval_Boolean True)        
                          _ -> Just (Eval_Boolean False)                                                                                                        

-- Helper function for eval that handles a cond list 
evalTupleListHelper :: GlobalEnv -> Env -> [(Expr, Expr)] -> Maybe Expr -> Maybe ExprEval
evalTupleListHelper _ _ [] Nothing = Nothing 
evalTupleListHelper g m [] (Just e) = eval g m e 
evalTupleListHelper g m ((t1, t2):xs) y = case eval g m t1 of 
                                         (Just (Eval_Boolean True)) -> eval g m t2 
                                         (Just (Eval_Boolean False)) -> evalTupleListHelper g m xs y
                                         _ -> Nothing 


test_evalTupleListHelper = do 
    test "evalTupleListHelper basic test" (evalTupleListHelper empty empty [] Nothing ) Nothing 

    test "evalTupleListHelper else case basic " (evalTupleListHelper empty empty [] (Just (Integer 5))) (Just (Eval_Integer 5))

    test "evalTupleListHelper else case complex 1" (evalTupleListHelper empty empty 
     [(Boolean False, Float 5.5)] (Just (Integer 5))) (Just (Eval_Integer 5))

    test "evalTupleListHelper else case complex 2" (evalTupleListHelper empty empty 
     [(Boolean True, Float 5.5)] (Just (Integer 5))) (Just (Eval_Float 5.5))

    test "evalTupleListHelper no else complex 1" (evalTupleListHelper empty empty 
     [(Boolean False, Float 5.5), (Boolean False, (Integer 5))] Nothing) (Nothing)

    test "evalTupleListHelper no else complex 2" (evalTupleListHelper empty empty 
     [(Boolean True, Float 5.5), (Boolean False, (Integer 5))] Nothing) (Just (Eval_Float 5.5))

    test "evalTupleListHelper no else complex 3" (evalTupleListHelper empty empty 
     [(Boolean False, Float 5.5), (And (Boolean True) (Less_Than (Integer 1) (Integer 2)), 
     (Integer 5))] Nothing ) (Just (Eval_Integer 5)) 

    test "evalTupleListHelper no else complex 4" (evalTupleListHelper empty empty 
     [(Equal_To (Integer 10) (Float 10.0), Boolean True), (And (Boolean True) (Less_Than (Integer 1) (Integer 2)), 
     (Integer 5))] Nothing) (Just (Eval_Boolean True))  

    test "evalTupleListHelper no else complex 5" (evalTupleListHelper empty empty 
     [(Add (Integer 10) (Float 10.0) ,Boolean False), (And (Boolean True) (Less_Than (Integer 1) (Integer 2)), 
     (Integer 5))] Nothing ) (Nothing)   

                         
test_eval = do
    -- // Boolean Tests
    test "eval Boolean  True" (eval empty empty (Boolean True)) (Just (Eval_Boolean True))

    test "eval Boolean False" (eval empty empty (Boolean False)) (Just (Eval_Boolean False))
    
    test "eval Boolean: (+ True 30)" (eval empty empty (Add (Boolean True) (Integer 30))) (Nothing)

    test "eval Boolean: (let (x (+ 1 False)) (* 4 x))"
       (eval empty empty ( Let "x" (Add (Integer 1) (Boolean False)) (Mul (Integer 4) (Var "x"))))
       (Nothing)

    test "eval Boolean: (- 30 False)" (eval empty empty ( Sub (Integer 30) (Boolean False))) (Nothing)

    test "eval Boolean: (* True 12)" (eval empty empty ( Mul (Boolean True) (Integer 12))) (Nothing)
  
    test "eval Boolean: (/ False 12)" (eval empty empty ( Div (Boolean False) (Integer 12))) (Nothing)

    test "eval Boolean: (* (+ 5 10) (- 5 True))" (eval empty empty ( Mul (Add (Integer 5) (Integer 10))
     (Sub (Integer 5) (Boolean True)))) (Nothing)

    test "eval Boolean: nested let" (eval empty empty ( Let "y" (Sub (Integer 20) (Integer 8))
     (Let "x" (Add (Var "y") (Integer 4)) (Add (Var "x") (Boolean False))))) (Nothing)


    -- // Integer tests
    test "eval Integer: (+ 12 30)" (eval empty empty (Add (Integer 12) (Integer 30))) (Just (Eval_Integer 42))

    test "eval Integer: (let (x (+1 2)) (* 4 x))"
       (eval empty empty ( Let "x" (Add (Integer 1) (Integer 2)) (Mul (Integer 4) (Var "x"))))
       (Just (Eval_Integer 12))

    test "eval Integer not assigned Var Test 1" (eval empty empty (Var "x")) (Nothing)

    test "eval Integer not assigned Var Test 2" (eval empty empty (Add (Integer 2) (Var "x"))) (Nothing)

    test "eval Integer: simple Integer test" (eval empty empty (Integer 11)) (Just (Eval_Integer 11))

    test "eval Integer: (- 30 12)" (eval empty empty (Sub (Integer 30) (Integer 12))) (Just (Eval_Integer 18))

    test "eval Integer: (* 30 12)" (eval empty empty (Mul (Integer 30) (Integer 12))) (Just (Eval_Integer 360))
  
    test "eval Integer: (/ 30 12)" (eval empty empty (Div (Integer 30) (Integer 12))) (Just (Eval_Integer 2))

    test "eval Integer: (* (+ 5 10) (- 5 4))" (eval empty empty (Mul (Add (Integer 5) (Integer 10))
     (Sub (Integer 5) (Integer 4)))) (Just (Eval_Integer 15))

    test "eval Integer: nested let" (eval empty empty ( Let "y" (Sub (Integer 20) (Integer 8))
     (Let "x" (Add (Var "y") (Integer 4)) (Add (Var "x") (Integer 1))))) (Just (Eval_Integer 17))

    -- // Float tests 

    test "eval Float: (+ 12.2 30.5)" True (checkFloatEquality (eval empty empty (Add (Float 12.2) (Float 30.5))) (Just (Eval_Float 42.7)))

    test "eval Float: (let (x (+1.1 2.2)) (* 4.5 x))"
       True 
       (checkFloatEquality(eval empty empty ( Let "x" (Add (Float 1.1) (Float 2.2)) (Mul (Float 4.5) (Var "x")))) (Just (Eval_Float 14.85)))

    test "eval Float not assigned Var Test" (eval empty empty ( Add (Float 2.5) (Var "x"))) (Nothing)
   
    test "eval Float: simple Integer test" True (checkFloatEquality (eval empty empty ( Float 11.1)) (Just (Eval_Float 11.1)))

    test "eval Float: (- 30.5 12.5)" True (checkFloatEquality (eval empty empty (Sub (Float 30.5) (Float 12.5))) (Just (Eval_Float 18.0)))

    test "eval Float: (* 30.5 12.1)" True (checkFloatEquality (eval empty empty (Mul (Float 30.5) (Float 12.1))) (Just (Eval_Float 369.05)))

    test "eval Float: (/ 30.0 12.0)" True (checkFloatEquality (eval empty empty (Div (Float 30.0) (Float 12.0))) (Just (Eval_Float 2.5)))

    test "eval Float: (* (+ 5.5 10.5) (- 5.4 4.4))" True (checkFloatEquality (eval empty empty ( Mul (Add (Float 5.5) (Float 10.5))
     (Sub (Float 5.4) (Float 4.4)))) (Just (Eval_Float 16.0)))

    test "eval Float: nested let" True (checkFloatEquality (eval empty empty ( Let "y" (Sub (Float 20.2) (Float 8.4))
     (Let "x" (Add (Var "y") (Float 4.4)) (Add (Var "x") (Float 1.1))))) (Just (Eval_Float 17.3)))

    -- // Mixed tests 

    test "eval Mixed: (+ 12.2 30)" True (checkFloatEquality (eval empty empty (Add (Float 12.2) (Integer 30))) (Just (Eval_Float 42.2)))

    test "eval Mixed: (let (x (+1.1 20)) (* 4.5 x))" True
       (checkFloatEquality (eval empty empty ( Let "x" (Add (Float 1.1) (Integer 20)) (Mul (Integer 4) (Var "x"))))
       (Just (Eval_Float 84.4)))

    test "eval Mixed: (- 30.5 12)" True (checkFloatEquality (eval empty empty ( Sub (Float 30.5) (Integer 12))) (Just (Eval_Float 18.5)))

    test "eval Mixed: (* 30.5 12)" True (checkFloatEquality (eval empty empty ( Mul (Float 30.5) (Integer 12))) (Just (Eval_Float 366.0)))

    test "eval Mixed: (/ 32.5 10)" True (checkFloatEquality (eval empty empty ( Div (Float 32.5) (Float 10))) (Just (Eval_Float 3.25)))

    test "eval Mixed: (* (+ 5.5 10) (- 5.4 4))" True (checkFloatEquality (eval empty empty ( Mul (Add (Float 5.5) (Integer 10))
     (Sub (Integer 5) (Float 4.4)))) (Just (Eval_Float 9.299999999999994)))

    test "eval Mixed: nested let" True (checkFloatEquality (eval empty empty ( Let "y" (Sub (Float 20.2) (Integer 8))
     (Let "x" (Add (Var "y") (Integer 4)) (Add (Var "x") (Float 1.1))))) (Just (Eval_Float 17.3)))


    -- // If tests 

    test "eval If: e1 is True Simple" (eval empty empty (If (Boolean True) (Integer 10) (Float 15.1)))  
      (Just $ Eval_Integer 10)  

    test "eval If: e1 is False Simple" True (checkFloatEquality (eval empty empty (If (Boolean False) (Integer 10) (Float 15.1)))  
      (Just $ Eval_Float 15.1))

    test "eval If: e1 is True Complex" True (checkFloatEquality (eval empty empty (If (Boolean True) (Add (Integer 10) (Float 9.5)) (Float 15.1)))
      (Just $ Eval_Float 19.5))

    test "eval If: e1 is False Complex" True (checkFloatEquality (eval empty empty (If (Boolean False) (Float 15.1) (Sub (Integer 10) (Float 9.5))))
      (Just $ Eval_Float 0.5))

    test "eval If: e1 is not a boolean" (eval empty empty (If (Div (Integer 5) (Float 5.1)) (Boolean False) (Boolean True)))
        (Nothing)       

   -- // And tests 

    test "eval And: e1 not a boolean simple" (eval empty empty (And (Integer 10) (Boolean False))) (Nothing)    

    test "eval And: e1 not a boolean complex" (eval empty empty (And (If (Boolean False) (Float 5.5) 
      (Add (Boolean True) (Integer 10))) (Boolean True))) (Nothing)  

    test "eval And: e1 is False simple" (eval empty empty (And (Boolean False) (Integer 3))) (Just (Eval_Boolean False))  

    test "eval And: e1 is False complex" (eval empty empty (And (If (Boolean False) (Float 5.5) (Boolean False)) 
      (Float 3.5))) (Just (Eval_Boolean False))

    test "eval And: e1 is True, e2 is True simple" (eval empty empty (And (Boolean True) (Boolean True))) (Just (Eval_Boolean True))

    test "eval And: e1 is True, e2 is True complex"  (eval empty empty (And (If (And (Boolean True) (Boolean True)) (Boolean True) (Boolean False)) 
      (If (And (Boolean True) (Boolean False)) (Boolean False) (Boolean True)))) (Just (Eval_Boolean True))

    test "eval And: e1 is True, e2 is False simple"  (eval empty empty (And (Boolean True) (Boolean False))) (Just (Eval_Boolean False)) 

    test "eval And: e1 is True, e2 is False complex"  (eval empty empty (And (If (And (Boolean True) (Boolean True)) (Boolean True) (Boolean False)) 
      (If (And (Boolean True) (Boolean False)) (Boolean True) (Boolean False)))) (Just (Eval_Boolean False))

    test "eval And: e1 is True, e2 is not a boolean simple" (eval empty empty (And (Boolean True) (Integer 10))) (Nothing)  

    test "eval And: e1 is True, e2 is not a boolean complex" (eval empty empty (And (If (And (Boolean True) (Boolean True)) (Boolean True) (Boolean False)) 
      (If (And (Boolean True) (Boolean True)) (Mul (Float 5.5) (Integer 10)) (Boolean False)))) (Nothing)

    -- // Or tests 

    test "eval Or: e1 not a boolean, e2 is True simple" (eval empty empty (Or (Integer 10) (Boolean True))) (Just (Eval_Boolean True))    

    test "eval Or: e1 not a boolean, e2 is False simple" (eval empty empty (Or (Integer 10) (Boolean False))) (Just (Eval_Boolean False)) 
    
    test "eval Or: e1 not a boolean, e2 is not a boolean simple" (eval empty empty (Or (Integer 10) (Float 15.2))) (Nothing)

    test "eval Or: e1 not a boolean, e2 is True complex" (eval empty empty (Or (Let "x" (Float 5.5) (Add (Var "x") (Integer 5))) 
      (If (And (Boolean True) (Boolean True)) (Boolean True) (Boolean False)))) (Just (Eval_Boolean True))

    test "eval Or: e1 not a boolean, e2 is False complex" (eval empty empty (Or (Let "x" (Float 5.5) (Add (Var "x") (Integer 5)))
      (If (And (Boolean True) (Boolean False)) (Boolean True) (Boolean False)))) (Just (Eval_Boolean False))

    test "eval Or: e1 not a boolean, e2 is not a boolean complex" (eval empty empty (Or (Let "x" (Float 5.5) (Add (Var "x") (Integer 5))) 
      (If (And (Boolean True) (Boolean False)) (Boolean True) (Float 5.5)))) (Nothing)  

    test "eval Or: e1 is True, e2 is True simple" (eval empty empty (Or (Boolean True) (Boolean True))) (Just (Eval_Boolean True))
    
    test "eval Or: e1 is True, e2 is False simple" (eval empty empty (Or (Boolean True) (Boolean False))) (Just (Eval_Boolean True))

    test "eval Or: e1 is True, e2 is not a boolean simple" (eval empty empty (Or (Boolean True) (Integer 15))) (Just (Eval_Boolean True))
      
    test "eval Or: e1 is True, e2 is True complex" (eval empty empty (Or (Let "x" (Boolean True) (Var "x")) 
      (And (Boolean True) (Boolean True)))) (Just (Eval_Boolean True))
      
    test "eval Or: e1 is True, e2 is False complex" (eval empty empty (Or (Let "x" (Boolean True) (Var "x")) 
      (And (Boolean True) (Boolean False)))) (Just (Eval_Boolean True))  

    test "eval Or: e1 is True, e2 is not a boolean complex" (eval empty empty (Or (Let "x" (Boolean True) (Var "x")) 
      (Div (Float 5.5) (Integer 22)))) (Just (Eval_Boolean True))  

    test "eval Or: e1 is False, e2 is True simple" (eval empty empty (Or (Boolean False) (Boolean True))) (Just (Eval_Boolean True))
    
    test "eval Or: e1 is False, e2 is False simple" (eval empty empty (Or (Boolean False) (Boolean False))) (Just (Eval_Boolean False))

    test "eval Or: e1 is False, e2 is not a boolean simple" (eval empty empty (Or (Boolean False) (Integer 15))) (Just (Eval_Boolean False))
      
    test "eval Or: e1 is False, e2 is True complex" (eval empty empty (Or (Let "x" (Boolean False) (Var "x")) 
      (And (Boolean True) (Boolean True)))) (Just (Eval_Boolean True))
      
    test "eval Or: e1 is False, e2 is False complex" (eval empty empty (Or (Let "x" (Boolean False) (Var "x")) 
      (And (Boolean True) (Boolean False)))) (Just (Eval_Boolean False))  

    test "eval Or: e1 is False, e2 is not a boolean complex" (eval empty empty (Or (Let "x" (Boolean False) (Var "x")) 
      (Div (Float 5.5) (Integer 22)))) (Just (Eval_Boolean False))   
      
    -- // Not tests 
    
    test "eval Not: e1 True" (eval empty empty (Not (Boolean True))) (Just (Eval_Boolean False)) 

    test "eval Not: e1 False" (eval empty empty (Not (Boolean False))) (Just (Eval_Boolean True)) 
    
    test "eval Not: e1 boolean complex" (eval empty empty (Not (Or (Boolean False) (Boolean True))))
      (Just (Eval_Boolean False)) 

    test "eval Not: e1 boolean if complex" (eval empty empty (Not (If (Boolean False)(Boolean True)(Boolean False))))
      (Just (Eval_Boolean True)) 

    test "eval Not: e1 not boolean" (eval empty empty (Not (Integer 10))) (Nothing) 
    
    test "eval Not: e1 not boolean complex" (eval empty empty (Not (Add (Integer 5) (Integer 10))))
      (Nothing)  

    -- // And, Or, Not complex tests 

    test "eval Complex boolean operator test 1" (eval empty empty (If (Not (Let "x" (And (Boolean True) (Not (Boolean True))) (Or (Var "x") (Boolean True))))
      (Add (Integer 10) (Integer 15)) (Div (Integer 50) (Integer 25)))) (Just (Eval_Integer 2)) 

    test "eval Complex boolean operator test 2" (eval empty empty (If (Not (Let "x" (Or (Boolean False) (Not (Boolean True))) (And (Var "x") (Boolean True))))
      (Add (Integer 10) (Integer 15)) (Div (Integer 50) (Integer 25)))) (Just (Eval_Integer 25))      
    
    -- // Less_Than Tests 
   
    test "eval Less_Than: eval e1 is Integer and eval e2 is Integer greater than e1 simple" 
     (eval empty empty ( Less_Than (Integer 5) (Integer 10))) (Just (Eval_Boolean True))  
     
    test "eval Less_Than: eval e1 is Integer and eval e2 is Integer less than e1 simple" 
     (eval empty empty ( Less_Than (Integer 10) (Integer 5))) (Just (Eval_Boolean False))    
     
    test "eval Less_Than: eval e1 is Integer and eval e2 is Float greater than e1 simple" 
     (eval empty empty ( Less_Than (Integer 5) (Float 10))) (Just (Eval_Boolean True))  
     
    test "eval Less_Than: eval e1 is Integer and eval e2 is Float less than e1 simple" 
     (eval empty empty ( Less_Than (Integer 10) (Float 5))) (Just (Eval_Boolean False))     

    test "eval Less_Than: eval e1 is Integer and eval e2 not a numeric type simple" 
     (eval empty empty ( Less_Than (Integer 5) (Boolean True))) (Nothing)   

    test "eval Less_Than: eval e1 is Integer and eval e2 is Integer greater than e1 complex" 
     (eval empty empty ( Less_Than (Sub (Integer 5) (Integer  7)) (Add (Integer 10) (Integer 20)))) (Just (Eval_Boolean True))  
     
    test "eval Less_Than: eval e1 is Integer and eval e2 is Integer less than e1 complex" 
     (eval empty empty ( Less_Than (Add (Integer 10) (Integer 20)) (Sub (Integer 5) (Integer  7)))) (Just (Eval_Boolean False))    
     
    test "eval Less_Than: eval e1 is Integer and eval e2 is Float greater than e1 complex" 
     (eval empty empty ( Less_Than (Sub (Integer 5) (Integer  7)) (Add (Integer 5) (Float 10)))) (Just (Eval_Boolean True))  
     
    test "eval Less_Than: eval e1 is Integer and eval e2 is Float less than e1 complex" 
     (eval empty empty ( Less_Than (Mul (Integer 5) (Integer  7)) (Add (Integer 5) (Float 10)))) (Just (Eval_Boolean False))     

    test "eval Less_Than: eval e1 is Integer and eval e2 not a numeric type complex" 
     (eval empty empty ( Less_Than (Integer 5) (And (Boolean True) (Boolean True)))) (Nothing) 

    test "eval Less_Than: eval e1 is Float and eval e2 is Integer greater than e1 simple" 
     (eval empty empty ( Less_Than (Float 5) (Integer 10))) (Just (Eval_Boolean True))  
     
    test "eval Less_Than: eval e1 is Float and eval e2 is Integer less than e1 simple" 
     (eval empty empty ( Less_Than (Float 10) (Integer 5))) (Just (Eval_Boolean False))    
     
    test "eval Less_Than: eval e1 is Float and eval e2 is Float greater than e1 simple" 
     (eval empty empty ( Less_Than (Float 5) (Float 10))) (Just (Eval_Boolean True))  
     
    test "eval Less_Than: eval e1 is Float and eval e2 is Float less than e1 simple" 
     (eval empty empty ( Less_Than (Float 10) (Float 5))) (Just (Eval_Boolean False))     

    test "eval Less_Than: eval e1 is Float and eval e2 not a numeric type simple" 
     (eval empty empty ( Less_Than (Float 5) (Boolean True))) (Nothing)   

    test "eval Less_Than: eval e1 is Float and eval e2 is Integer greater than e1 complex" 
     (eval empty empty ( Less_Than (Sub (Float 5) (Integer  7)) (Add (Integer 10) (Integer 20)))) (Just (Eval_Boolean True))  
     
    test "eval Less_Than: eval e1 is Float and eval e2 is Integer less than e1 complex" 
     (eval empty empty ( Less_Than (Add (Float 10) (Float 20)) (Sub (Integer 5) (Integer  7)))) (Just (Eval_Boolean False))    
     
    test "eval Less_Than: eval e1 is Float and eval e2 is Float greater than e1 complex" 
     (eval empty empty ( Less_Than (Sub (Float 5) (Float  7)) (Add (Integer 5) (Float 10)))) (Just (Eval_Boolean True))  
     
    test "eval Less_Than: eval e1 is Float and eval e2 is Float less than e1 complex" 
     (eval empty empty ( Less_Than (Mul (Float 5) (Float  7)) (Add (Integer 5) (Float 10)))) (Just (Eval_Boolean False))     

    test "eval Less_Than: eval e1 is Float and eval e2 not a numeric type complex" 
     (eval empty empty ( Less_Than (Float 5) (And (Boolean True) (Boolean True)))) (Nothing)     

    test "eval Less_Than: eval e1 is not numeric" 
     (eval empty empty ( Less_Than (Boolean True)(Integer 10))) (Nothing) 

    test "eval Less_Than: eval e1 and eval e2 equal ints should be false" 
     (eval empty empty ( Less_Than (Integer 10) (Integer 10))) (Just (Eval_Boolean False))

    test "eval Less_Than: eval e1 and eval e2 equal floats should be false" 
     (eval empty empty ( Less_Than (Float 10) (Float 10))) (Just (Eval_Boolean False))  


    -- // Greater_Than Tests 
   
    test "eval Greater_Than: eval e1 is Integer and eval e2 is Integer greater than e1 simple" 
     (eval empty empty ( Greater_Than (Integer 5) (Integer 10))) (Just (Eval_Boolean False))  
     
    test "evalGreater_Than: eval e1 is Integer and eval e2 is Integer less than e1 simple" 
     (eval empty empty ( Greater_Than (Integer 10) (Integer 5))) (Just (Eval_Boolean True))    
     
    test "evalGreater_Than: eval e1 is Integer and eval e2 is Float greater than e1 simple" 
     (eval empty empty ( Greater_Than (Integer 5) (Float 10))) (Just (Eval_Boolean False))  
     
    test "eval Greater_Than: eval e1 is Integer and eval e2 is Float less than e1 simple" 
     (eval empty empty ( Greater_Than (Integer 10) (Float 5))) (Just (Eval_Boolean True))     

    test "eval Greater_Than: eval e1 is Integer and eval e2 not a numeric type simple" 
     (eval empty empty ( Greater_Than (Integer 5) (Boolean True))) (Nothing)   

    test "eval Greater_Than: eval e1 is Integer and eval e2 is Integer greater than e1 complex" 
     (eval empty empty ( Greater_Than (Sub (Integer 5) (Integer 7)) (Add (Integer 10) (Integer 20)))) (Just (Eval_Boolean False))  
     
    test "eval Greater_Than: eval e1 is Integer and eval e2 is Integer less than e1 complex" 
     (eval empty empty ( Greater_Than (Add (Integer 10) (Integer 20)) (Sub (Integer 5) (Integer  7)))) (Just (Eval_Boolean True))    
     
    test "eval Greater_Than: eval e1 is Integer and eval e2 is Float greater than e1 complex" 
     (eval empty empty ( Greater_Than (Sub (Integer 5) (Integer 7)) (Add (Integer 5) (Float 10)))) (Just (Eval_Boolean False))  
     
    test "eval Greater_Than: eval e1 is Integer and eval e2 is Float less than e1 complex" 
     (eval empty empty ( Greater_Than (Mul (Integer 5) (Integer 7)) (Add (Integer 5) (Float 10)))) (Just (Eval_Boolean True))     

    test "eval Greater_Than: eval e1 is Integer and eval e2 not a numeric type complex" 
     (eval empty empty ( Greater_Than (Integer 5) (And (Boolean True) (Boolean True)))) (Nothing) 

    test "eval Greater_Than: eval e1 is Float and eval e2 is Integer greater than e1 simple" 
     (eval empty empty ( Greater_Than (Float 5) (Integer 10))) (Just (Eval_Boolean False))  
     
    test "eval Greater_Than: eval e1 is Float and eval e2 is Integer less than e1 simple" 
     (eval empty empty ( Greater_Than (Float 10) (Integer 5))) (Just (Eval_Boolean True))    
     
    test "eval Greater_Than: eval e1 is Float and eval e2 is Float greater than e1 simple" 
     (eval empty empty ( Greater_Than (Float 5) (Float 10))) (Just (Eval_Boolean False))  
     
    test "eval Greater_Than: eval e1 is Float and eval e2 is Float less than e1 simple" 
     (eval empty empty ( Greater_Than (Float 10) (Float 5))) (Just (Eval_Boolean True))     

    test "eval Greater_Than: eval e1 is Float and eval e2 not a numeric type simple" 
     (eval empty empty ( Greater_Than (Float 5) (Boolean True))) (Nothing)   

    test "eval Greater_Than: eval e1 is Float and eval e2 is Integer greater than e1 complex" 
     (eval empty empty ( Greater_Than (Sub (Float 5) (Integer  7)) (Add (Integer 10) (Integer 20)))) (Just (Eval_Boolean False))  
     
    test "eval Greater_Than: eval e1 is Float and eval e2 is Integer less than e1 complex" 
     (eval empty empty ( Greater_Than (Add (Float 10) (Float 20)) (Sub (Integer 5) (Integer  7)))) (Just (Eval_Boolean True))    
     
    test "eval Greater_Than: eval e1 is Float and eval e2 is Float greater than e1 complex" 
     (eval empty empty ( Greater_Than (Sub (Float 5) (Float  7)) (Add (Integer 5) (Float 10)))) (Just (Eval_Boolean False))  
     
    test "eval Greater_Than: eval e1 is Float and eval e2 is Float less than e1 complex" 
     (eval empty empty ( Greater_Than (Mul (Float 5) (Float  7)) (Add (Integer 5) (Float 10)))) (Just (Eval_Boolean True))     

    test "eval Greater_Than: eval e1 is Float and eval e2 not a numeric type complex" 
     (eval empty empty ( Greater_Than (Float 5) (And (Boolean True) (Boolean True)))) (Nothing)     

    test "eval Greater_Than: eval e1 is not numeric" 
     (eval empty empty ( Greater_Than (Boolean True)(Integer 10))) (Nothing) 

    test "eval Greater_Than: eval e1 and eval e2 equal ints should be false" 
     (eval empty empty ( Greater_Than (Integer 10) (Integer 10))) (Just (Eval_Boolean False))

    test "eval Greater_Than: eval e1 and eval e2 equal floats should be false" 
     (eval empty empty ( Greater_Than (Float 10) (Float 10))) (Just (Eval_Boolean False)) 


    -- // Equal_To Tests 
   
    test "eval Equal_To: eval e1 is Integer and eval e2 is Integer not equal to e1 simple" 
     (eval empty empty ( Equal_To (Integer 5) (Integer 10))) (Just (Eval_Boolean False))  
     
    test "eval Equal_To: eval e1 is Integer and eval e2 is Integer equal to e1 simple" 
     (eval empty empty ( Equal_To (Integer 5) (Integer 5))) (Just (Eval_Boolean True))    
     
    test "eval Equal_To: eval e1 is Integer and eval e2 is Float not equal to e1 simple" 
     (eval empty empty ( Equal_To (Integer 5) (Float 10))) (Just (Eval_Boolean False))  
     
    test "eval Equal_To: eval e1 is Integer and eval e2 is Float equal to e1 simple" 
     (eval empty empty ( Equal_To (Integer 5) (Float 5))) (Just (Eval_Boolean True))     

    test "eval Equal_To: eval e1 is Integer and eval e2 not a numeric type simple" 
     (eval empty empty ( Equal_To (Integer 5) (Boolean True))) (Nothing)   

    test "eval Equal_To: eval e1 is Integer and eval e2 is Integer not equal e1 complex" 
     (eval empty empty ( Equal_To (Sub (Integer 5) (Integer  7)) (Add (Integer 10) (Integer 20)))) (Just (Eval_Boolean False))  
     
    test "eval Equal_To: eval e1 is Integer and eval e2 is Integer equal to e1 complex" 
     (eval empty empty ( Equal_To (Add (Integer 10) (Integer 20)) (Sub (Integer 35) (Integer  5)))) (Just (Eval_Boolean True))    
     
    test "eval Equal_To: eval e1 is Integer and eval e2 is Float not equal to e1 complex" 
     (eval empty empty ( Equal_To (Sub (Integer 5) (Integer  7)) (Add (Integer 5) (Float 10)))) (Just (Eval_Boolean False))  
     
    test "eval Equal_To: eval e1 is Integer and eval e2 is Float equal to e1 complex" 
     (eval empty empty ( Equal_To (Mul (Integer 5) (Integer  7)) (Add (Integer 25) (Float 10)))) (Just (Eval_Boolean True))     

    test "eval Equal_To: eval e1 is Integer and eval e2 not a numeric type complex" 
     (eval empty empty ( Equal_To (Integer 5) (And (Boolean True) (Boolean True)))) (Nothing) 

    test "eval Equal_To: eval e1 is Float and eval e2 is Integer not equal to e1 simple" 
     (eval empty empty ( Equal_To (Float 5) (Integer 10))) (Just (Eval_Boolean False))  
     
    test "eval Equal_To: eval e1 is Float and eval e2 is Integer equal to e1 simple" 
     (eval empty empty ( Equal_To (Float 10) (Integer 10))) (Just (Eval_Boolean True))    
     
    test "eval Equal_To: eval e1 is Float and eval e2 is Float not equal to e1 simple" 
     (eval empty empty ( Equal_To (Float 5) (Float 10))) (Just (Eval_Boolean False))  
     
    test "eval Equal_To: eval e1 is Float and eval e2 is Float equal to e1 simple" 
     (eval empty empty ( Equal_To (Float 10) (Float 10))) (Just (Eval_Boolean True))     

    test "eval Equal_To: eval e1 is Float and eval e2 not a numeric type simple" 
     (eval empty empty ( Equal_To (Float 5) (Boolean True))) (Nothing)   

    test "eval Equal_To: eval e1 is Float and eval e2 is Integer not equal to e1 complex" 
     (eval empty empty ( Equal_To (Sub (Float 5) (Integer  7)) (Add (Integer 10) (Integer 20)))) (Just (Eval_Boolean False))  
     
    test "eval Equal_To: eval e1 is Float and eval e2 is Integer equal to e1 complex" 
     (eval empty empty ( Equal_To (Add (Float 10) (Float 20)) (Sub (Integer 35) (Integer  5)))) (Just (Eval_Boolean True))    
     
    test "eval Equal_To: eval e1 is Float and eval e2 is Float not equal to e1 complex" 
     (eval empty empty ( Equal_To (Sub (Float 5) (Float  7)) (Add (Integer 5) (Float 10)))) (Just (Eval_Boolean False))  
     
    test "eval Equal_To: eval e1 is Float and eval e2 is Float equal to e1 complex" 
     (eval empty empty ( Equal_To (Mul (Float 5) (Float  7)) (Add (Integer 25) (Float 10)))) (Just (Eval_Boolean True))     

    test "eval Equal_To: eval e1 is Float and eval e2 not a numeric type complex" 
     (eval empty empty ( Equal_To (Float 5) (And (Boolean True) (Boolean True)))) (Nothing)     

    test "eval Equal_To: eval e1 is a boolean equal to eval e2 also boolean" 
     (eval empty empty ( Equal_To (Boolean True)(Boolean True))) (Just (Eval_Boolean True)) 

    test "eval Equal_To: eval e1 is a boolean not equal to eval e2 also boolean" 
     (eval empty empty ( Equal_To (Boolean True)(Boolean False))) (Just (Eval_Boolean False))  

    test "eval Equal_To: eval e1 is a Nothing and eval e2 also Nothing" 
     (eval empty empty ( Equal_To (Sub (Integer 5) (Boolean True))(Add (Integer 5) (Boolean False)))) (Just (Eval_Boolean True)) 

    test "eval Equal_To: eval e1 is a Nothing  not equal to eval e2 also boolean" 
     (eval empty empty ( Equal_To (Sub (Integer 5) (Boolean True))(Boolean False))) (Nothing)  


    -- Cond If equality tests 

    test "eval Cond and If are same test 1" (eval empty empty ( If (Boolean True) (Add (Integer 5) (Integer 2)) (Sub (Integer 5) (Integer 2))))
     (eval empty empty ( Cond [(Boolean True, (Add (Integer 5) (Integer 2)))] (Just (Sub (Integer 5) (Integer 2)))))  

    test "eval Cond and If are same test 2" (eval empty empty ( If (Boolean False) (Add (Integer 5) (Integer 2)) 
     (If (Boolean True) (Sub (Integer 5) (Integer 2)) (Mul (Integer 5) (Integer 2))))) 
       (eval empty empty ( Cond [(Boolean False, (Add (Integer 5) (Integer 2))), (Boolean True, (Sub (Integer 5) (Integer 2)))] 
         (Just (Mul (Integer 5) (Integer 2)))))
  
    -- // Cond Tests
    test "eval Cond: first true" (eval empty empty ( Cond [(Boolean True, (Add (Integer 5) (Integer 2)))] Nothing))
       (Just (Eval_Integer 7))

    test "eval Cond: next true" (eval empty empty ( Cond [(Boolean False, (Add (Integer 5) (Integer 2))), 
        (Boolean True, (Div (Integer 4) (Integer 2)))] Nothing))
       (Just (Eval_Integer 2))

    test "eval Cond: no true" (eval empty empty ( Cond [(Boolean False, (Add (Integer 5) (Integer 2))), 
        (Boolean False, (Div (Integer 4) (Integer 2)))] Nothing))
       (Nothing)

    test "eval Cond: not boolean values" (eval empty empty ( Cond [(Float 5.1, (Add (Integer 5) (Integer 2))), 
        (Boolean False, (Div (Integer 4) (Integer 2)))] Nothing))
       (Nothing)
       
    test "eval Cond: first true" (eval empty empty ( Cond [(Boolean True, (Add (Integer 5) (Integer 2)))] 
        (Just (Sub (Integer 5) (Integer 2)))))
       (Just (Eval_Integer 7))

    test "eval Cond: next true" (eval empty empty ( Cond [(Boolean False, (Add (Integer 5) (Integer 2))), 
        (Boolean True, (Div (Integer 4) (Integer 2)))] (Just (Mul (Float 5.1) (Float 2.0)))))
       (Just (Eval_Integer 2))

    test "eval Cond: no true" (eval empty empty ( Cond [(Boolean False, (Add (Integer 5) (Integer 2))), 
        (Boolean False, (Div (Integer 4) (Integer 2)))] (Just (Float 2.2))))
       (Just (Eval_Float 2.2))

    test "eval Cond: not boolean values" (eval empty empty ( Cond [(Float 5.1, (Add (Integer 5) (Integer 2))), 
        (Boolean False, (Div (Integer 4) (Integer 2)))] (Just (Float 2.1))))
       (Nothing)


    -- // Pair Tests    
    test "eval Pair: eval e1 and eval e2 are nothing, simple" (eval empty empty ( Pair 
     (Add (Integer 5) (Boolean False)) (Var "x"))) (Nothing)  

    test "eval Pair: eval e1 and eval e2 are nothing, complex" (eval empty empty ( Pair 
     (If (Boolean False) (Integer 5) (Div (Var "y") (Float 5.5))) 
      (Let "x" (Boolean True) (Equal_To (Integer 5) (Boolean True)))))
       (Nothing) 

    test "eval Pair: eval e1 is not nothing but eval e2 is nothing, simple" (eval empty empty ( Pair 
     (Add (Integer 5) (Float 6.5)) (Var "x"))) (Nothing)     

    test "eval Pair: eval e1 is not nothing but eval e2 is nothing, complex" (eval empty empty ( Pair 
     (If (Boolean False) (Integer 5) (Let "y" (Integer 10) (Div (Var "x") (Float 5.5)))) 
      (Let "x" (Boolean True) (Equal_To (Integer 5) (Boolean True)))))
       (Nothing)  

    test "eval Pair: eval e1 is not nothing but eval e2 is not nothing, simple" (eval empty empty ( Pair 
     (Add (Integer 5) (Float 6.5)) (Let "x" (Boolean False) (Var "x"))))
     (Just (Eval_Pair (Eval_Float 11.5) (Eval_Boolean False)))     

    test "eval Pair: eval e1 is not nothing but eval e2 is not nothing, complex" (eval empty empty ( Pair 
     (If (Boolean False) (Integer 5) (Let "y" (Integer 11) (Div (Var "y") (Float 5.5)))) 
      (Let "x" (Boolean True) (Equal_To (Integer 5) (Float 5)))))
       (Just (Eval_Pair (Eval_Float 2) (Eval_Boolean True)))     

    -- // Left Tests    
    test "eval Left: Expr is nothing, simple" (eval empty empty (
     Left (Add (Boolean True) (Integer 10)))) (Nothing)  

    test "eval Left: Expr is nothing, complex" (eval empty empty ( Left (Pair 
     (If (Boolean False) (Integer 5) (Div (Var "y") (Float 5.5))) 
      (Let "x" (Boolean True) (Equal_To (Integer 5) (Boolean True))))))
       (Nothing) 

    test "eval Left: Expr is something but not a pair, simple" (eval empty empty ( Left (Boolean False))) 
     (Nothing)   

    test "eval Left: Expr is something but not a pair, complex" (eval empty empty ( Left
     (Equal_To (Add (Integer 5) (Float 6.5)) (Let "x" (Float 11.5) (Var "x")))))
      (Nothing)

    test "eval Left: Expr is a pair that evals to nothing, simple" (eval empty empty ( Left 
     ( Pair (Add (Integer 5) (Boolean False)) (Var "x")))) (Nothing)     

    test "eval Left: Expr is a pair that evals to nothing, simplex" (eval empty empty ( Left ( Pair 
     (If (Boolean False) (Integer 5) (Let "y" (Integer 10) (Div (Var "x") (Float 5.5)))) 
      (Let "x" (Boolean True) (Equal_To (Integer 5) (Boolean True))))))
       (Nothing)  

    test "eval Left: Expr is a good pair, simplex" (eval empty empty ( Left (Pair 
     (Add (Integer 5) (Float 6.5)) (Let "x" (Boolean False) (Var "x")))))
     (Just (Eval_Float 11.5))     

    test "eval Left: Expr is a good pair, complex" (eval empty empty ( Left (Pair 
     (If (Boolean False) (Integer 5) (Let "y" (Integer 11) (Div (Var "y") (Float 5.5)))) 
      (Let "x" (Boolean True) (Equal_To (Integer 5) (Float 5))))))
       (Just (Eval_Float 2))     

    -- // Right Tests    
    test "eval Right: Expr is nothing, simple" (eval empty empty (
     Left (Add (Boolean True) (Integer 10)))) (Nothing)  

    test "eval Right: Expr is nothing, complex" (eval empty empty ( Left (Pair 
     (If (Boolean False) (Integer 5) (Div (Var "y") (Float 5.5))) 
      (Let "x" (Boolean True) (Equal_To (Integer 5) (Boolean True))))))
       (Nothing) 

    test "eval Right: Expr is something but not a pair, simple" (eval empty empty ( Right (Boolean False)) )
     (Nothing)   

    test "eval Right: Expr is something but not a pair, complex" (eval empty empty ( Right
     (Equal_To (Add (Integer 5) (Float 6.5)) (Let "x" (Float 11.5) (Var "x"))))) 
      (Nothing)

    test "eval Right: Expr is a pair that evals to nothing, simple" (eval empty empty ( Right 
     ( Pair (Add (Integer 5) (Boolean False)) (Var "x")))) (Nothing)     

    test "eval Right: Expr is a pair that evals to nothing, simplex" (eval empty empty ( Right ( Pair 
     (If (Boolean False) (Integer 5) (Let "y" (Integer 10) (Div (Var "x") (Float 5.5)))) 
      (Let "x" (Boolean True) (Equal_To (Integer 5) (Boolean True))))))
       (Nothing)  

    test "eval Right: Expr is a good pair, simplex" (eval empty empty ( Right (Pair 
     (Add (Integer 5) (Float 6.5)) (Let "x" (Boolean False) (Var "x")))))
     (Just (Eval_Boolean False))     

    test "eval Right: Expr is a good pair, complex" (eval empty empty ( Right (Pair 
     (If (Boolean False) (Integer 5) (Let "y" (Integer 11) (Div (Var "y") (Float 5.5)))) 
      (Let "x" (Boolean True) (Equal_To (Integer 5) (Float 5))))))
       (Just (Eval_Boolean True))      

    -- // Real_Pred tests 
    test "eval Real_Pred: Expr is a float simple" (eval empty empty ( Real_Pred 
     (Float 5.5))) (Just (Eval_Boolean True))

    test "eval Real_Pred: Expr is a float complex" (eval empty empty ( Real_Pred 
     (If (Boolean True) (Div (Integer 10) (Float 5.1)) (Integer 10))))
      (Just (Eval_Boolean True))  

    test "eval Real_Pred: Expr is not a float simple" (eval empty empty ( Real_Pred 
     (Integer 5))) (Just (Eval_Boolean False))

    test "eval Real_Pred: Expr is not a float complex" (eval empty empty ( Real_Pred 
     (If (Boolean True) (Div (Integer 10) (Boolean False)) (Integer 10))))
      (Just (Eval_Boolean False))      

    -- // Integer_Pred tests 
    test "eval Integer_Pred: Expr is a integer simple" (eval empty empty ( Integer_Pred 
     (Integer 5))) (Just (Eval_Boolean True))

    test "eval Integer_Pred: Expr is a integer complex" (eval empty empty ( Integer_Pred 
     (If (Boolean True) (Div (Integer 10) (Integer 5)) (Integer 10))))
      (Just (Eval_Boolean True))  

    test "eval Integer_Pred: Expr is not a integer simple" (eval empty empty ( Integer_Pred 
     (Float 5))) (Just (Eval_Boolean False))

    test "eval Integer_Pred: Expr is not a integer complex" (eval empty empty ( Integer_Pred 
     (If (Boolean True) (Div (Integer 10) (Boolean False)) (Integer 10))))
      (Just (Eval_Boolean False))     

    -- // Number_Pred tests 
    test "eval Number_Pred: Expr is a integer simple" (eval empty empty ( Number_Pred 
     (Integer 5))) (Just (Eval_Boolean True))

    test "eval Number_Pred: Expr is a integer complex" (eval empty empty ( Number_Pred 
     (If (Boolean True) (Div (Integer 10) (Integer 5)) (Integer 10))))
      (Just (Eval_Boolean True))  

    test "eval Number_Pred: Expr is a float simple" (eval empty empty ( Number_Pred 
     (Float 5.5))) (Just (Eval_Boolean True))

    test "eval Number_Pred: Expr is a float complex" (eval empty empty ( Number_Pred 
     (If (Boolean True) (Div (Integer 10) (Float 5.1)) (Integer 10))))
      (Just (Eval_Boolean True))   

    test "eval Number_Pred: Expr is not a integer or float simple" (eval empty empty ( Number_Pred 
     (Boolean False))) (Just (Eval_Boolean False))

    test "eval Number_Pred: Expr is not a integer or float complex" (eval empty empty ( Number_Pred 
     (If (Boolean True) (Div (Integer 10) (Boolean False)) (Integer 10))))
      (Just (Eval_Boolean False))     

    -- // Boolean_Pred tests 
    test "eval Boolean_Pred: Expr is a boolean simple" (eval empty empty ( Boolean_Pred 
     (Boolean False))) (Just (Eval_Boolean True))

    test "eval Boolean_Pred: Expr is a boolean complex" (eval empty empty ( Boolean_Pred 
     (If (Boolean True) (Less_Than (Integer 10) (Integer 5)) (Integer 10))))
      (Just (Eval_Boolean True))  

    test "eval Boolean_Pred: Expr is not a boolean simple" (eval empty empty ( Boolean_Pred 
     (Float 5))) (Just (Eval_Boolean False))

    test "eval Boolean_Pred: Expr is not a boolean complex" (eval empty empty ( Boolean_Pred 
     (If (Boolean True) (Div (Integer 10) (Boolean False)) (Integer 10))))
      (Just (Eval_Boolean False))   

    -- // Pair_Pred tests 
    test "eval Pair_Pred: Expr is a pair simple" (eval empty empty ( Pair_Pred 
     (Pair (Add (Integer 5) (Float 6.5)) (Let "x" (Boolean False) (Var "x")))))
      (Just (Eval_Boolean True))

    test "eval Pair_Pred: Expr is a pair complex" (eval empty empty ( Pair_Pred 
      (Pair (If (Boolean False) (Integer 5) 
       (Let "y" (Integer 11) (Div (Var "y") (Float 5.5)))) 
       (Let "x" (Boolean True) (Equal_To (Integer 5) (Float 5))))))
      (Just (Eval_Boolean True))        

    test "eval Pair_Pred: Expr is not a pair simple" (eval empty empty ( Pair_Pred 
     (Boolean False))) (Just (Eval_Boolean False))

    test "eval Pair_Pred: Expr is not a pair complex" (eval empty empty ( Pair_Pred 
     (If (Boolean True) (Less_Than (Integer 10) (Integer 5)) (Integer 10))))
      (Just (Eval_Boolean False))  

    -- // New Eval_Pair tests 
    test "eval Eval_Pair Add, e1 is pair" (eval empty empty ( Add (
      Pair (Integer 5) (Integer 10)) (Integer 5))) (Nothing)

    test "eval Eval_Pair Add, e2 is pair" (eval empty empty ( Add (Integer 5) (
      Pair (Integer 5) (Integer 10)))) (Nothing)  

    test "eval Eval_Pair Add, e1 and e2 are pairs" (eval empty empty ( Add (
      Pair (Integer 5) (Integer 10)) (Pair (Float 5.6) (Boolean False)))) (Nothing)   

    test "eval Eval_Pair Sub, e1 is pair" (eval empty empty ( Sub (
      Pair (Integer 5) (Integer 10)) (Integer 5))) (Nothing)

    test "eval Eval_Pair Sub, e2 is pair" (eval empty empty ( Sub (Integer 5) (
      Pair (Integer 5) (Integer 10)))) (Nothing)  

    test "eval Eval_Pair Sub, e1 and e2 are pairs" (eval empty empty ( Sub (
      Pair (Integer 5) (Integer 10)) (Pair (Float 5.6) (Boolean False)))) (Nothing)    

    test "eval Eval_Pair Mul, e1 is pair" (eval empty empty ( Mul (
      Pair (Integer 5) (Integer 10)) (Integer 5))) (Nothing)

    test "eval Eval_Pair Mul, e2 is pair" (eval empty empty ( Mul (Integer 5) (
      Pair (Integer 5) (Integer 10)))) (Nothing)  

    test "eval Eval_Pair Mul, e1 and e2 are pairs" (eval empty empty ( Mul (
      Pair (Integer 5) (Integer 10)) (Pair (Float 5.6) (Boolean False)))) (Nothing)    

    test "eval Eval_Pair Div, e1 is pair" (eval empty empty ( Div (
      Pair (Integer 5) (Integer 10)) (Integer 5))) (Nothing)

    test "eval Eval_Pair Div, e2 is pair" (eval empty empty ( Div (Integer 5) (
      Pair (Integer 5) (Integer 10)))) (Nothing)  

    test "eval Eval_Pair Div, e1 and e2 are pairs" (eval empty empty ( Div (
      Pair (Integer 5) (Integer 10)) (Pair (Float 5.6) (Boolean False)))) (Nothing)      

    test "eval Eval_Pair let" (eval empty empty ( Let "x" (
      Pair (Integer 5) (Float 5.5))
      (Var "x"))) (Just (Eval_Pair (Eval_Integer 5) (Eval_Float 5.5)))
 
         
   
     

-- |Substitutes the given value for the given variable in the given expression.
-- Given value can now be either a double or an integer 
{-
 For Assignment 5: 
 Added Pair, Left, and Right cases for Question 1.
 this includes a new Eval_Pair into the var case
 Added all five pred cases for Question 2.  
-}
subst :: Variable -> ExprEval -> Expr -> Expr
subst _ _ (Integer n) = Integer n
subst _ _ (Float f) = Float f
subst _ _ (Boolean b) = Boolean b
subst x v (Var y) | x == y = substVarReplacer v 
                  | otherwise = Var y
subst x v (Pair e1 e2) = Pair (subst x v e1) (subst x v e2)
subst x v (Left e1) = Left (subst x v e1)
subst x v (Right e1) = Right (subst x v e1)
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
subst x v (Cond l Nothing) = Cond (substTupleListHelper x v l) Nothing  
subst x v (Cond l (Just y)) = Cond (substTupleListHelper x v l) (Just (subst x v y))   
subst x v (Real_Pred e) = Real_Pred (subst x v e)
subst x v (Integer_Pred e) = Integer_Pred (subst x v e)
subst x v (Boolean_Pred e) = Boolean_Pred (subst x v e)
subst x v (Number_Pred e) = Number_Pred (subst x v e)
subst x v (Pair_Pred e) = Pair_Pred (subst x v e)

-- Function for handling substituting a var 
-- This is needed now that Eval_Pairs exist. 
substVarReplacer :: ExprEval -> Expr 
substVarReplacer (Eval_Integer i) = Integer i
substVarReplacer (Eval_Float f) = Float f 
substVarReplacer (Eval_Boolean b) = Boolean b 
substVarReplacer (Eval_Pair l r) = Pair (substVarReplacer l) (substVarReplacer r)

test_substVarReplacer = do 
    test "substVarReplacer int test" (substVarReplacer $ Eval_Integer 5) (Integer 5)
    test "substVarReplacer float test" (substVarReplacer $ Eval_Float 5) (Float 5)
    test "substVarReplacer boolean test" (substVarReplacer $ Eval_Boolean False) (Boolean False)
    test "substVarReplacer pair test simple" (substVarReplacer $ 
     Eval_Pair (Eval_Float 5.5) (Eval_Integer 3)) (Pair (Float 5.5) (Integer 3))
    test "substVarReplacer pair test complex" (substVarReplacer $ 
     Eval_Pair (Eval_Pair (Eval_Integer 5) (Eval_Boolean True)) (Eval_Boolean False)) 
     (Pair (Pair (Integer 5) (Boolean True)) (Boolean False))

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

    test "subst Cond basic test" (subst "x" (Eval_Integer 10) (Cond [] Nothing )) (Cond [] Nothing) 

    test "subst Cond complex test 1" (subst"x" (Eval_Integer 15) 
     (Cond [(Var "x", Integer 10)] Nothing)) (Cond [(Integer 15, Integer 10)] Nothing)

    test "subst Cond complex test 2" (subst "x" (Eval_Integer 15) 
     (Cond [(Var "x", Integer 10), (Float 5.5, Var "x")] Nothing))
       (Cond [(Integer 15, Integer 10), (Float 5.5, Integer 15)] Nothing)

    test "subst Cond complex test 3" (subst "x" (Eval_Integer 15) 
     (Cond [(Var "y", Integer 10), (Float 5.5, Var "y")] Nothing)) 
      (Cond [(Var "y", Integer 10), (Float 5.5,  Var "y")] Nothing)  

    test "subst Cond complex test with Else" (subst "x" (Eval_Integer 15) 
     (Cond [(Var "x", Integer 10)] (Just (Var "x")))) 
      (Cond [(Integer 15, Integer 10)] (Just (Integer 15)))                        
                           
    -- Pair tests

    test "subst Pair as sub value" (subst "x" (Eval_Pair (Eval_Integer 10) (Eval_Float 5)) (Var "x"))
     (Pair (Integer 10) (Float 5))

    test "subst Pair in left test" (subst "x" (Eval_Integer 1) (Pair (Var "x") (Float 1.6)))
      (Pair (Integer 1) (Float 1.6))

    test "subst Pair in right test" (subst "x" (Eval_Boolean True) (Pair (Integer 1) (Var "x")))
      (Pair (Integer 1) (Boolean True))

    test "subst Pair in none" (subst "x" (Eval_Boolean True) (Pair (Integer 1) (Boolean False)))
      (Pair (Integer 1) (Boolean False))
    
    test "subst Pair nested" (subst "y" (Eval_Integer 5) (If (Boolean True) (Pair (Var "y") (Float 6.1))
      (Pair (Integer 6) (Integer 7)))) 
      (If (Boolean True) (Pair (Integer 5) (Float 6.1)) (Pair (Integer 6) (Integer 7)))

    -- Left and Right test
    test "subst Left in pair" (subst "y" (Eval_Float 5.1) (Left (Pair (Integer 1) (Var "y"))))
       (Left (Pair (Integer 1) (Float 5.1)))
    
    test "subst Left not in pair" (subst "y" (Eval_Float 5.1) (Left (Pair (Integer 1) (Float 5.2))))
       (Left (Pair (Integer 1) (Float 5.2)))

    test "subst Left not pair" (subst "y" (Eval_Float 5.1) (Left (Float 5.2)))
       (Left (Float 5.2))

    test "subst Right in pair" (subst "y" (Eval_Float 5.1) (Right (Pair (Var "y") (Integer 1))))
       (Right (Pair (Float 5.1) (Integer 1)))
    
    test "subst Right in pair2" (subst "y" (Eval_Float 5.1) (Right (Pair (Integer 1) (Var "y"))))
       (Right (Pair (Integer 1) (Float 5.1)))
    
    test "subst Right not in pair" (subst "y" (Eval_Float 5.1) (Right (Pair (Integer 1) (Float 5.2))))
       (Right (Pair (Integer 1) (Float 5.2)))

    test "subst Right not pair" (subst "y" (Eval_Float 5.1) (Right (Var "y")))
       (Right (Float 5.1))

    -- // Real_Pred tests 
    test "subst Real_Pred no subst" (subst "x" (Eval_Integer 5) (Real_Pred 
     (Float 5.5))) (Real_Pred (Float 5.5))

    test "subst Real_Pred subst simple" (subst "x" (Eval_Integer 5) (Real_Pred 
     (Var "x"))) (Real_Pred (Integer 5))

    test "subst Real_Pred subst complex" (subst "x" (Eval_Pair (Eval_Integer 5) (Eval_Float 5.5))
     (Real_Pred (Let "y" (Integer 20) (Add (Var "x") (Var "y")))))
      (Real_Pred (Let "y" (Integer 20) (Add (Pair (Integer 5) (Float 5.5)) (Var "y"))))

    -- // Integer_Pred tests 
    test "subst Integer_Pred no subst" (subst "x" (Eval_Integer 5) (Integer_Pred 
     (Float 5.5))) (Integer_Pred (Float 5.5))

    test "subst Integer_Pred subst simple" (subst "x" (Eval_Integer 5) (Integer_Pred 
     (Var "x"))) (Integer_Pred (Integer 5))

    test "subst Integer_Pred subst complex" (subst "x" (Eval_Pair (Eval_Integer 5) (Eval_Float 5.5))
     (Integer_Pred (Let "y" (Integer 20) (Add (Var "x") (Var "y")))))
      (Integer_Pred (Let "y" (Integer 20) (Add (Pair (Integer 5) (Float 5.5)) (Var "y"))))

    -- // Number_Pred tests 
    test "subst Number_Pred no subst" (subst "x" (Eval_Integer 5) (Number_Pred 
     (Float 5.5))) (Number_Pred (Float 5.5))

    test "subst Number_Pred subst simple" (subst "x" (Eval_Integer 5) (Number_Pred 
     (Var "x"))) (Number_Pred (Integer 5))

    test "subst Number_Pred subst complex" (subst "x" (Eval_Pair (Eval_Integer 5) (Eval_Float 5.5))
     (Number_Pred (Let "y" (Integer 20) (Add (Var "x") (Var "y")))))
      (Number_Pred (Let "y" (Integer 20) (Add (Pair (Integer 5) (Float 5.5)) (Var "y"))))      

    -- // Boolean_Pred tests 
    test "subst Boolean_Pred no subst" (subst "x" (Eval_Integer 5) (Boolean_Pred 
     (Float 5.5))) (Boolean_Pred (Float 5.5))

    test "subst Boolean_Pred subst simple" (subst "x" (Eval_Integer 5) (Boolean_Pred 
     (Var "x"))) (Boolean_Pred (Integer 5))

    test "subst Boolean_Pred subst complex" (subst "x" (Eval_Pair (Eval_Integer 5) (Eval_Float 5.5))
     (Boolean_Pred (Let "y" (Integer 20) (Add (Var "x") (Var "y")))))
      (Boolean_Pred (Let "y" (Integer 20) (Add (Pair (Integer 5) (Float 5.5)) (Var "y"))))  

    -- // Pair_Pred tests 
    test "subst Pair_Pred no subst" (subst "x" (Eval_Integer 5) (Pair_Pred 
     (Float 5.5))) (Pair_Pred (Float 5.5))

    test "subst Pair_Pred subst simple" (subst "x" (Eval_Integer 5) (Pair_Pred 
     (Var "x"))) (Pair_Pred (Integer 5))

    test "subst Pair_Pred subst complex" (subst "x" (Eval_Pair (Eval_Integer 5) (Eval_Float 5.5))
     (Pair_Pred (Let "y" (Integer 20) (Add (Var "x") (Var "y")))))
      (Pair_Pred (Let "y" (Integer 20) (Add (Pair (Integer 5) (Float 5.5)) (Var "y"))))   
   

       
       
-- |Run the given protoScheme s-expression, returning an s-expression
-- representation of the result.
runSExpression :: S.Expr -> Maybe S.Expr
runSExpression se =
    case eval empty empty (fromSExpression se) of
         (Just (Eval_Integer v)) -> Just (valueToSExpression (Eval_Integer v))
         (Just (Eval_Float v)) -> Just (valueToSExpression (Eval_Float v))
         (Just (Eval_Boolean v)) -> Just (valueToSExpression (Eval_Boolean v))
         (Just (Eval_Pair e1 e2)) -> Just (valueToSExpression (Eval_Pair e1 e2))
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
        S.List[S.Symbol "+", S.Integer 3, S.Integer 2]]], S.Symbol "Nothing"])
        (Just $ S.Integer 5)

    test "Cond runSExpression Test 2" (runSExpression $ S.List[S.Symbol "Cond", S.List[S.List[S.Boolean False, 
        S.List[S.Symbol "-", S.Integer 3, S.Integer 2]], S.List[S.Boolean True, 
          S.List[S.Symbol "+", S.Integer 3, S.Integer 1]]], S.Symbol "Nothing"])
        (Just $ S.Integer 4)
        
    test "Cond runSExpression Test 3" (runSExpression $ S.List[S.Symbol "Cond", S.List[S.List[S.Boolean False, 
        S.List[S.Symbol "-", S.Integer 3, S.Integer 2]], S.List[S.Boolean False, 
          S.List[S.Symbol "+", S.Integer 3, S.Integer 1]]],
           S.List[S.Symbol "/", S.Integer 3, S.Integer 1]])
        (Just $ S.Integer 3)

    test "Cond runSExpression Test 4" (runSExpression $ S.List[S.Symbol "Cond", S.List[S.List[S.Boolean False, 
        S.List[S.Symbol "-", S.Integer 3, S.Integer 2]], S.List[S.Boolean True, 
          S.List[S.Symbol "+", S.Integer 3, S.Integer 1]]], S.List[S.Symbol "/", S.Integer 3, S.Integer 1]])
        (Just $ S.Integer 4)

    test "Cond runSExpression Test 5" (runSExpression $ S.List[S.Symbol "Cond", S.List[S.List[S.Real 5.3, 
        S.List[S.Symbol "+", S.Integer 3, S.Integer 2]]], S.Symbol "Nothing"])
        (Nothing)

    test "Cond runSExpression Test 6" (runSExpression $ S.List[S.Symbol "Cond", S.List[S.List[S.Integer 1, 
        S.List[S.Symbol "-", S.Integer 3, S.Integer 2]], S.List[S.Boolean False, 
          S.List[S.Symbol "+", S.Integer 3, S.Integer 1]]], S.List[S.Symbol "/", S.Integer 3, S.Integer 1]])
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

     -- // Pair Tests 

    test "Pair runSExpression Test 1" (runSExpression $ S.List [
       S.Symbol "Pair", S.Integer 10, S.Real 11.1
     ]) (Just $ S.Dotted (S.Integer 10) (S.Real 11.1))  

    test "Pair runSExpression Test 2" (runSExpression $ S.List [
       S.Symbol "Pair", S.List [S.Symbol "Pair", S.Integer 15, S.Boolean True],
        S.Real 11.1]) 
        (Just $ S.Dotted (S.Dotted (S.Integer 15) (S.Boolean True)) (S.Real 11.1))   

    test "Pair runSExpression Test 3" (runSExpression $ S.List [
      S.Symbol "Pair", S.List [S.Symbol "+", S.Boolean False, S.Boolean True],
      S.Integer 10]) (Nothing)

    -- // Left Tests 

    test "Left runSExpression Test 1" (runSExpression $ S.List [
      S.Symbol "Left", S.Integer 10]) (Nothing)  

    test "Left runSExpression Test 2" (runSExpression $ S.List [
      S.Symbol "Left", S.List [S.Symbol "Pair", S.Real 5.5, S.Integer 10]]) 
       (Just (S.Real 5.5))    

    test "Left runSExpression Test 3" (runSExpression $ S.List [S.Symbol "Left", 
      S.List [S.Symbol "Left", S.List [
       S.Symbol "Pair", S.List [S.Symbol "Pair", S.Integer 15, S.Boolean True],
        S.Real 11.1]]])
        (Just $ S.Integer 15)   

    -- // Right Tests 

    test "Right runSExpression Test 1" (runSExpression $ S.List [
      S.Symbol "Right", S.Integer 10]) (Nothing)  

    test "Right runSExpression Test 2" (runSExpression $ S.List [
      S.Symbol "Right", S.List [S.Symbol "Pair", S.Real 5.5, S.Integer 10]]) 
       (Just (S.Integer 10))    

    test "Right runSExpression Test 3" (runSExpression $ S.List [S.Symbol "Right", 
      S.List [S.Symbol "Right", S.List [
       S.Symbol "Pair", S.Real 11.1 , 
        S.List [S.Symbol "Pair", S.Integer 15, S.Boolean True]]]])
        (Just $ S.Boolean True)       