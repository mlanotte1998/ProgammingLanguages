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

import Maps (get, set, empty)

import SimpleTestsColor (test)

import qualified Result as R


-- ===============================================================================






-- ======================================================================================================

-- Function for testing doubles that takes go to the thousandths place. 
-- Without this, some results were for example 14.850000000000001
checkFloatEquality :: R.Result Value -> R.Result Value -> Bool 
checkFloatEquality (R.Success (Float x)) (R.Success (Float y)) = if (abs (x - y) < 0.001) 
                                                             then True 
                                                             else False
checkFloatEquality x y = False             

-- Tests for the checkFloatEquality function
test_checkFloatEquality = do 
    test "checkFloatEquality nothing with nothing" False (checkFloatEquality (fail "") (fail ""))
    test "checkFloatEquality int with nothing" False (checkFloatEquality (R.Success (Integer 1)) (fail ""))
    test "checkFloatEquality nothing with int" False (checkFloatEquality (fail "") (R.Success (Integer 1)))
    test "checkFloatEquality int with int" False (checkFloatEquality (R.Success (Integer 1)) (R.Success (Integer 1)))
    test "checkFloatEquality float with nothing" False (checkFloatEquality (R.Success (Float 1.1)) (fail ""))
    test "checkFloatEquality nothing with float" False (checkFloatEquality (fail "") (R.Success (Float 1.1)))
    test "checkFloatEquality float with int" False (checkFloatEquality (R.Success (Float 1.1)) (R.Success (Integer 1)))
    test "checkFloatEquality int with float" False (checkFloatEquality (R.Success (Integer 1)) (R.Success (Float 1.1)))
    test "checkFloatEquality float with float should not be equal 1" False (checkFloatEquality (R.Success (Float 12.1)) 
     (R.Success (Float 12.101000001)))
    test "checkFloatEquality float with float should not be equal 2" False (checkFloatEquality (R.Success (Float 12.1)) 
     (R.Success (Float 8.0)))
    test "checkFloatEquality float with float should be equal 1" True (checkFloatEquality (R.Success (Float 12.1)) 
     (R.Success (Float 12.100000001)))
    test "checkFloatEquality float with float should be equal 2" True (checkFloatEquality (R.Success (Float 12.1)) 
     (R.Success (Float 12.1)))
 

-- ================================================================================================
--Examples of Programs using Defun, containing both singular Expr and lists of Expr

ex_program1 = Program [Defun "incr" ("x", []) (Add (Var "x") (Val (Integer 1)))] 
                 (Call "incr" [(Call "incr" [(Call "incr" [(Val (Integer 1))])])])
ex_program2 = Program [Defun "f" ("x", []) (Add (Var "x") (Var "y"))]
                 (Let "y" (Val (Integer 10)) (Call "f" [(Val (Integer 10))]))
ex_program3 = Program [Defun "incr" ("x", []) (Add (Var "x") (Val (Integer 1)))] 
                 (Let "z" (Val (Integer 20)) (Call "incr" [(Var "z")]))

ex_program4 = Program 
                [ Defun "fact" ("n", []) 
                    (If  
                      (Equal_To (Val (Integer 0)) (Var "n"))
                      (Val (Integer 1)) 
                      (Mul (Var "n") (Call "fact" [(Sub (Var "n") (Val (Integer 1)))])))]
                (Call "fact" [(Val (Integer 5))])  

ex_program5 = Program 
                [ Defun "fact" ("n", []) 
                    (If  
                      (Equal_To (Val (Integer 0)) (Var "n"))
                      (Val (Integer 1)) 
                      (Mul (Var "n") (Call "fact" [(Sub (Var "n") (Val (Integer 1)))]))), 
                      Defun "incr" ("x", []) (Add (Var "x") (Val (Integer 1)))]
                (Call "incr" [(Call "fact" [(Val (Integer 5))])])        

ex_program6 = Program 
                [ Defun "fact" ("n", []) 
                    (If  
                      (Equal_To (Val (Integer 0)) (Var "n"))
                      (Val (Integer 1)) 
                      (Mul (Var "n") (Call "fact" [(Sub (Var "n") (Val (Integer 1)))]))), 
                      Defun "incr" ("x", []) (Add (Var "x") (Val (Integer 1))),
                      Define "z" (Val (Integer 10))]
                (Add (Var "z") (Call "incr" [(Call "fact" [(Val (Integer 5))])]))   

ex_program7 = Program 
                [ Defun "fact" ("n", []) 
                    (If  
                      (Equal_To (Val (Integer 0)) (Var "n"))
                      (Val (Integer 1)) 
                      (Mul (Var "n") (Call "fact" [(Sub (Var "n") (Val (Integer 1)))]))), 
                      Defun "incr" ("x",[]) (Add (Var "x") (Val (Integer 1))),
                      Define "z" (Val (Integer 10)),
                      Define "a" (Val (Boolean False))]
                (If (Var "a") (Val (Boolean True)) (Add (Var "z") (Call "incr" [(Call "fact" [(Val (Integer 5))])])))              

ex_program8 = Program [Defun "incr" ("x", []) (Add (Var "x") (Val (Integer 1)))] 
                 (Call "incr" [(Call "incr" [(Let "incr" (Val (Integer 5)) (Var "incr"))])])    

ex_program9 = Program [Define "x" (Val (Integer 2))] 
                 (Add (Var "x") (Let "x" (Val (Integer 1)) (Var "x")))    

ex_program10 = Program [Define "x" (Val (Integer 2))] 
                 (Call "x" [(Val (Integer 1))])       


-- add has multiple variables and is called with enough args
ex_program_11 = Program 
                [ Defun "fact" ("n", []) 
                    (If  
                      (Equal_To (Val (Integer 0)) (Var "n"))
                      (Val (Integer 1)) 
                      (Mul (Var "n") (Call "fact" [(Sub (Var "n") (Val (Integer 1)))]))), 
                      Defun "add" ("x",["y"]) (Add (Var "x") (Var "y")),
                      Define "z" (Val (Integer 10)),
                      Define "a" (Val (Boolean False))]
                (If (Var "a") (Val (Boolean True)) (Call "add" [(Call "fact" [(Val (Integer 5))]),  Var "z"]))       

-- add has multiple variables and is called with not enough args
ex_program_12 = Program 
                [ Defun "fact" ("n", []) 
                    (If  
                      (Equal_To (Val (Integer 0)) (Var "n"))
                      (Val (Integer 1)) 
                      (Mul (Var "n") (Call "fact" [(Sub (Var "n") (Val (Integer 1)))]))), 
                      Defun "add" ("x",["y"]) (Add (Var "x") (Var "y")),
                      Define "z" (Val (Integer 10)),
                      Define "a" (Val (Boolean False))]
                (If (Var "a") (Val (Boolean True)) (Call "add" [(Call "fact" [(Val (Integer 5))])]))     

-- add has one variables and is called with multiple args
ex_program_13 = Program 
                [ Defun "fact" ("n", []) 
                    (If  
                      (Equal_To (Val (Integer 0)) (Var "n"))
                      (Val (Integer 1)) 
                      (Mul (Var "n") (Call "fact" [(Sub (Var "n") (Val (Integer 1)))]))), 
                      Defun "add" ("x",[]) (Add (Var "x") (Var "y")),
                      Define "z" (Val (Integer 10)),
                      Define "a" (Val (Boolean False))]
                (If (Var "a") (Val (Boolean True)) (Call "add" [(Call "fact" [(Val (Integer 5))]), (Val (Integer 10))]))   

--  ================================================================================================                                                                                                    

-- Function that takes in a Program and evaluates the program to get a resulting Maybe ExprEval
evalProgram :: Program -> R.Result Value
evalProgram (Program globalDefs e) = eval globals empty e
  where 
    globals = collectDefs (reverse globalDefs)
    collectDefs [] = empty
    collectDefs (Defun f x body : globalDefs) = 
        set (collectDefs globalDefs) f (Defun f x body)
    collectDefs (Define v e : globalDefs) = 
        set (collectDefs globalDefs) v (Define v e)    

--tests of the evalProgram function
test_evalProgram = do 
    test "evalProgram empty globalDefs and simple expression" (evalProgram $ Program [] (Val (Integer 10)))
     (R.Success (Integer 10))

    test "evalProgram single variable globalDefs and simple expression" (evalProgram $ Program 
     [Define "x" (Val (Integer 10))] (Var "x"))
     (R.Success (Integer 10))  

    -- test "evalProgram multiple variable globalDefs and simple expression" (evalProgram $ Program 
    --  [Define "x" (Val (Integer 10)), Define "y" (Val (Integer 20))] (Add (Var "y") (Var "x")))
    --  (R.Success (Integer 30))  

    -- test "evalProgram multiple of same variable globalDefs and simple expression" (evalProgram $ Program 
    --  [Define "x" (Val (Integer 10)), Define "x" (Val (Integer 20))] (Add (Var "x") (Var "x")))
    --  (R.Success (Integer 40))       

    -- test "evalProgram single function and simple expression 1" (evalProgram ex_program1)  
    --  (R.Success (Integer 4))  

    -- test "evalProgram single function and simple expression 2" (evalProgram ex_program2)  
    --  (fail "")  

    -- test "evalProgram single function and simple expression 3" (evalProgram ex_program3)  
    --  (R.Success (Integer 21))  

    -- test "evalProgram single function and simple expression 4" (evalProgram ex_program4)  
    --  (R.Success (Integer 120))     

    -- test "evalProgram multiple functions" (evalProgram ex_program5)  
    --  (R.Success (Integer 121))  

    -- test "evalProgram multiple functions and a variable" (evalProgram ex_program6)  
    --  (R.Success (Integer 131)) 

    -- test "evalProgram multiple functions and multiple variables" (evalProgram ex_program7)  
    --  (R.Success (Integer 131))  

    -- test "evalProgram function with same name as let variable" (evalProgram ex_program8)  
    --  (R.Success (Integer 7))

    -- test "evalProgram variable with same name as let variable" (evalProgram ex_program9)    
    --  (R.Success (Integer 3)) 

    -- test "evalProgram global variable called like a function" (evalProgram ex_program10)
    --  (fail "") 

    -- test "evalProgram ex1 from pdf"(evalProgram (Program [
    --   Define "x" (Val (Integer 32))] (Let "x" (Val (Float 3.14)) (Var "x")))) 
    --    (R.Success (Float 3.14)) 

    -- test "evalProgram ex2 from pdf"(evalProgram (Program [
    --   Define "x" (Val (Integer 32))] (Let "x" (Mul (Var "x") (Val (Integer 2))) (Var "x")))) 
    --    (R.Success (Integer 64))   

    -- test "evalProgram ex3 from pdf"(evalProgram (Program [
    --   Define "x" (Val (Integer 32))] (Let "y" (Mul (Var "x") (Val (Integer 2))) (Var "x")))) 
    --    (R.Success (Integer 32))    

    -- test "evalProgram ex4 from pdf"(evalProgram (Program [
    --   Define "x" (Val (Integer 32))] (Let "y" (Mul (Var "x") (Val (Integer 2))) (Var "z")))) 
    --    (fail "")   

    -- -- // Tests for programs that have functions with multiple arguments 
    -- test "evalProgram functions with multiple arguments test 1" (evalProgram ex_program_11) 
    --  (R.Success $ Integer 130) 

    -- test "evalProgram functions with multiple arguments test 2" (evalProgram ex_program_12) 
    --  (fail "")  

    -- test "evalProgram functions with multiple arguments test 3" (evalProgram ex_program_13) 
    --  (fail "")  
   
 -- ===============================================================================================

-- |Evaluates the given expression to a value.
eval :: GlobalEnv -> Env -> Expr -> R.Result Value
eval g m (Val (Integer i)) = return (Integer i)
eval g m (Val (Float d)) = return (Float d)
eval g m (Val (Boolean b)) = return (Boolean b)
eval g m (Var x) =
    case get m x of
         Just v -> return v
         _ -> case get g x of 
                   Just (Define _ v) -> eval g m v
                   _ -> fail $ "Variable " ++ x ++ " not defined."     
eval g m (Let x e1 e2) = do
     v1 <- eval g m e1
     eval g (set m x v1) e2
eval g m (Call f e) = do 
    case get g f of
         Just (Defun name (x, extra) body) -> runFunction name g m empty e variableList body
            where 
              variableList = x : extra
              runFunction :: Variable -> GlobalEnv -> Env -> Env -> [Expr] -> [Variable] -> Expr -> R.Result Value
              runFunction name g m m2 [] [] _ = eval g m2 body 
              runFunction name g m m2 [] _  _ = fail $ "Function " ++ name ++ " needs more arguments." 
              runFunction name g m m2 _ [] _ = fail $ "Function " ++ name ++ "was given too many arguments."
              runFunction name g m m2 (x:xs) (y:ys) body = do
                  v <- eval g m x 
                  runFunction name g m (set m2 y v) xs ys body
         _ -> fail $ "Called function " ++ f ++ " does not exist."                                      
eval g m (If e1 e2 e3) = do
      Boolean b <- eval g m e1
      if b then eval g m e2
         else eval g m e3
--In the case of a Cond Expr, refer to the EvalTupleListHelper to identify
--the inputs and find the correct branch to follow 
eval g m (Cond x y) = (evalTupleListHelper g m x y)  
-- Pair needs to make sure that both eval e1 and eval e2 are values
-- otherwise return nothing. 
eval g m (Val (Pair e1 e2)) = return (Pair e1 e2)
-- Left needs that eval of l to be a pair otherwise there is nothing
-- to take a left from.        
eval g m (Left l ) = do 
    v <- eval g m l 
    case v of 
        Pair left right -> do 
            eval g m left
        _ -> fail $ "Left not applied to pair."     
-- Right needs that eval of l to be a pair otherwise there is nothing
-- to take a right from.          
eval g m (Right l ) = do
    v <- eval g m l 
    case v of 
        Pair left right -> do 
            eval g m left
        _ -> fail $ "Right not applied to pair."          
eval g m (Real_Pred e) = do 
    v <- eval g m e 
    case v of 
        (Float _) -> return (Boolean True)
        _ -> return (Boolean False)                          
eval g m (Integer_Pred e) = do 
    v <- eval g m e 
    case v of 
        (Integer _) -> return (Boolean True)
        _ -> return (Boolean False)
eval g m (Number_Pred e) = do 
    v <- eval g m e 
    case v of 
        (Float _) -> return (Boolean True)
        (Integer _) -> return (Boolean True)
        _ -> return (Boolean False)                      
eval g m (Boolean_Pred e) = do 
    v <- eval g m e 
    case v of 
        (Boolean _ ) -> return (Boolean True)
        _ -> return(Boolean False)                                             
eval g m (Pair_Pred e) = do 
    v <- eval g m e 
    case v of 
        (Pair _ _) -> return (Boolean True)
        _ -> return (Boolean False)                                                                                                   

-- Helper function for eval that handles a cond list by identifying the inputs using pattern matching
--and follows the cond branch that has a corresponding true value 
evalTupleListHelper :: GlobalEnv -> Env -> [(Expr, Expr)] -> Maybe Expr -> R.Result Value
evalTupleListHelper _ _ [] Nothing = fail $ "Cond ended without a returned expression." 
evalTupleListHelper g m [] (Just e) = eval g m e 
evalTupleListHelper g m ((t1, t2):xs) y = do 
    v <- eval g m t1 
    case v of 
        (Boolean True) -> eval g m t2
        (Boolean False) -> evalTupleListHelper g m xs y 
        _ -> fail $ "Cond clause was not a boolean."


-- Tests of the Eval
test_evalTupleListHelper = do 
    test "evalTupleListHelper basic test" (evalTupleListHelper empty empty [] Nothing ) (fail $ "Cond ended without a returned expression.") 

    test "evalTupleListHelper else case basic " (evalTupleListHelper empty empty [] (Just (Val (Integer 5)))) (R.Success (Integer 5))

    -- test "evalTupleListHelper else case complex 1" (evalTupleListHelper empty empty 
    --  [(Boolean False, Float 5.5)] (Just (Integer 5))) (Just (Integer 5))

    -- test "evalTupleListHelper else case complex 2" (evalTupleListHelper empty empty 
    --  [(Boolean True, Float 5.5)] (Just (Integer 5))) (Just (Float 5.5))

    -- test "evalTupleListHelper no else complex 1" (evalTupleListHelper empty empty 
    --  [(Boolean False, Float 5.5), (Boolean False, (Integer 5))] Nothing) (Nothing)

    -- test "evalTupleListHelper no else complex 2" (evalTupleListHelper empty empty 
    --  [(Boolean True, Float 5.5), (Boolean False, (Integer 5))] Nothing) (Just (Float 5.5))

    -- test "evalTupleListHelper no else complex 3" (evalTupleListHelper empty empty 
    --  [(Boolean False, Float 5.5), (And (Boolean True) (Less_Than (Integer 1) (Integer 2)), 
    --  (Integer 5))] Nothing ) (Just (Integer 5)) 

    -- test "evalTupleListHelper no else complex 4" (evalTupleListHelper empty empty 
    --  [(Equal_To (Integer 10) (Float 10.0), Boolean True), (And (Boolean True) (Less_Than (Integer 1) (Integer 2)), 
    --  (Integer 5))] Nothing) (Just (Boolean True))  

    -- test "evalTupleListHelper no else complex 5" (evalTupleListHelper empty empty 
    --  [(Add (Integer 10) (Float 10.0) ,Boolean False), (And (Boolean True) (Less_Than (Integer 1) (Integer 2)), 
    --  (Integer 5))] Nothing ) (Nothing)   

                         
test_eval = do
    -- // Boolean Tests
    test "eval Boolean  True" (eval empty empty (Val (Boolean True))) (R.Success (Boolean True))

    test "eval Boolean False" (eval empty empty (Val (Boolean False))) (R.Success (Boolean False))
    
    -- test "eval Boolean: (+ True 30)" (eval empty empty (Add (Boolean True) (Integer 30))) (Nothing)

    -- test "eval Boolean: (let (x (+ 1 False)) (* 4 x))"
    --    (eval empty empty ( Let "x" (Add (Integer 1) (Boolean False)) (Mul (Integer 4) (Var "x"))))
    --    (Nothing)

    -- test "eval Boolean: (- 30 False)" (eval empty empty ( Sub (Integer 30) (Boolean False))) (Nothing)

    -- test "eval Boolean: (* True 12)" (eval empty empty ( Mul (Boolean True) (Integer 12))) (Nothing)
  
    -- test "eval Boolean: (/ False 12)" (eval empty empty ( Div (Boolean False) (Integer 12))) (Nothing)

    -- test "eval Boolean: (* (+ 5 10) (- 5 True))" (eval empty empty ( Mul (Add (Integer 5) (Integer 10))
    --  (Sub (Integer 5) (Boolean True)))) (Nothing)

    -- test "eval Boolean: nested let" (eval empty empty ( Let "y" (Sub (Integer 20) (Integer 8))
    --  (Let "x" (Add (Var "y") (Integer 4)) (Add (Var "x") (Boolean False))))) (Nothing)


    -- // Integer tests
    -- test "eval Integer: (+ 12 30)" (eval empty empty (Add (Integer 12) (Integer 30))) (Just (Integer 42))

    -- test "eval Integer: (let (x (+1 2)) (* 4 x))"
    --    (eval empty empty ( Let "x" (Add (Integer 1) (Integer 2)) (Mul (Integer 4) (Var "x"))))
    --    (Just (Integer 12))

    -- test "eval Integer not assigned Var Test 1" (eval empty empty (Var "x")) (Nothing)

    -- test "eval Integer not assigned Var Test 2" (eval empty empty (Add (Integer 2) (Var "x"))) (Nothing)

    -- test "eval Integer: simple Integer test" (eval empty empty (Integer 11)) (Just (Integer 11))

    -- test "eval Integer: (- 30 12)" (eval empty empty (Sub (Integer 30) (Integer 12))) (Just (Integer 18))

    -- test "eval Integer: (* 30 12)" (eval empty empty (Mul (Integer 30) (Integer 12))) (Just (Integer 360))
  
    -- test "eval Integer: (/ 30 12)" (eval empty empty (Div (Integer 30) (Integer 12))) (Just (Integer 2))

    -- test "eval Integer: (* (+ 5 10) (- 5 4))" (eval empty empty (Mul (Add (Integer 5) (Integer 10))
    --  (Sub (Integer 5) (Integer 4)))) (Just (Integer 15))

    -- test "eval Integer: nested let" (eval empty empty ( Let "y" (Sub (Integer 20) (Integer 8))
    --  (Let "x" (Add (Var "y") (Integer 4)) (Add (Var "x") (Integer 1))))) (Just (Integer 17))

    -- -- // Float tests 

    -- test "eval Float: (+ 12.2 30.5)" True (checkFloatEquality (eval empty empty (Add (Float 12.2) (Float 30.5))) (Just (Float 42.7)))

    -- test "eval Float: (let (x (+1.1 2.2)) (* 4.5 x))"
    --    True 
    --    (checkFloatEquality(eval empty empty ( Let "x" (Add (Float 1.1) (Float 2.2)) (Mul (Float 4.5) (Var "x")))) (Just (Float 14.85)))

    -- test "eval Float not assigned Var Test" (eval empty empty ( Add (Float 2.5) (Var "x"))) (Nothing)
   
    test "eval Float: simple Integer test" True (checkFloatEquality (eval empty empty (Val (Float 11.1))) (R.Success (Float 11.1)))

    -- test "eval Float: (- 30.5 12.5)" True (checkFloatEquality (eval empty empty (Sub (Float 30.5) (Float 12.5))) (Just (Float 18.0)))

    -- test "eval Float: (* 30.5 12.1)" True (checkFloatEquality (eval empty empty (Mul (Float 30.5) (Float 12.1))) (Just (Float 369.05)))

    -- test "eval Float: (/ 30.0 12.0)" True (checkFloatEquality (eval empty empty (Div (Float 30.0) (Float 12.0))) (Just (Float 2.5)))

    -- test "eval Float: (* (+ 5.5 10.5) (- 5.4 4.4))" True (checkFloatEquality (eval empty empty ( Mul (Add (Float 5.5) (Float 10.5))
    --  (Sub (Float 5.4) (Float 4.4)))) (Just (Float 16.0)))

    -- test "eval Float: nested let" True (checkFloatEquality (eval empty empty ( Let "y" (Sub (Float 20.2) (Float 8.4))
    --  (Let "x" (Add (Var "y") (Float 4.4)) (Add (Var "x") (Float 1.1))))) (Just (Float 17.3)))

    -- // Mixed tests 

    -- test "eval Mixed: (+ 12.2 30)" True (checkFloatEquality (eval empty empty (Add (Float 12.2) (Integer 30))) (Just (Float 42.2)))

    -- test "eval Mixed: (let (x (+1.1 20)) (* 4.5 x))" True
    --    (checkFloatEquality (eval empty empty ( Let "x" (Add (Float 1.1) (Integer 20)) (Mul (Integer 4) (Var "x"))))
    --    (Just (Float 84.4)))

    -- test "eval Mixed: (- 30.5 12)" True (checkFloatEquality (eval empty empty ( Sub (Float 30.5) (Integer 12))) (Just (Float 18.5)))

    -- test "eval Mixed: (* 30.5 12)" True (checkFloatEquality (eval empty empty ( Mul (Float 30.5) (Integer 12))) (Just (Float 366.0)))

    -- test "eval Mixed: (/ 32.5 10)" True (checkFloatEquality (eval empty empty ( Div (Float 32.5) (Float 10))) (Just (Float 3.25)))

    -- test "eval Mixed: (* (+ 5.5 10) (- 5.4 4))" True (checkFloatEquality (eval empty empty ( Mul (Add (Float 5.5) (Integer 10))
    --  (Sub (Integer 5) (Float 4.4)))) (Just (Float 9.299999999999994)))

    -- test "eval Mixed: nested let" True (checkFloatEquality (eval empty empty ( Let "y" (Sub (Float 20.2) (Integer 8))
    --  (Let "x" (Add (Var "y") (Integer 4)) (Add (Var "x") (Float 1.1))))) (Just (Float 17.3)))


    -- // If tests 

    test "eval If: e1 is True Simple" (eval empty empty (If (Val (Boolean True)) (Val (Integer 10)) (Val (Float 15.1))))  
      (R.Success $ Integer 10)  

    test "eval If: e1 is False Simple" True (checkFloatEquality (eval empty empty 
     (If (Val (Boolean False)) (Val (Integer 10)) (Val (Float 15.1))))  
      (R.Success $ Float 15.1))

    -- test "eval If: e1 is True Complex" True (checkFloatEquality (eval empty empty (If (Boolean True) (Add (Integer 10) (Float 9.5)) (Float 15.1)))
    --   (Just $ Float 19.5))

    -- test "eval If: e1 is False Complex" True (checkFloatEquality (eval empty empty (If (Boolean False) (Float 15.1) (Sub (Integer 10) (Float 9.5))))
    --   (Just $ Float 0.5))

    -- test "eval If: e1 is not a boolean" (eval empty empty (If (Div (Integer 5) (Float 5.1)) (Boolean False) (Boolean True)))
    --     (Nothing)       

   -- // And tests 

    -- test "eval And: e1 not a boolean simple" (eval empty empty (And (Integer 10) (Boolean False))) (Nothing)    

    -- test "eval And: e1 not a boolean complex" (eval empty empty (And (If (Boolean False) (Float 5.5) 
    --   (Add (Boolean True) (Integer 10))) (Boolean True))) (Nothing)  

    -- test "eval And: e1 is False simple" (eval empty empty (And (Boolean False) (Integer 3))) (Just (Boolean False))  

    -- test "eval And: e1 is False complex" (eval empty empty (And (If (Boolean False) (Float 5.5) (Boolean False)) 
    --   (Float 3.5))) (Just (Boolean False))

    -- test "eval And: e1 is True, e2 is True simple" (eval empty empty (And (Boolean True) (Boolean True))) (Just (Boolean True))

    -- test "eval And: e1 is True, e2 is True complex"  (eval empty empty (And (If (And (Boolean True) (Boolean True)) (Boolean True) (Boolean False)) 
    --   (If (And (Boolean True) (Boolean False)) (Boolean False) (Boolean True)))) (Just (Boolean True))

    -- test "eval And: e1 is True, e2 is False simple"  (eval empty empty (And (Boolean True) (Boolean False))) (Just (Boolean False)) 

    -- test "eval And: e1 is True, e2 is False complex"  (eval empty empty (And (If (And (Boolean True) (Boolean True)) (Boolean True) (Boolean False)) 
    --   (If (And (Boolean True) (Boolean False)) (Boolean True) (Boolean False)))) (Just (Boolean False))

    -- test "eval And: e1 is True, e2 is not a boolean simple" (eval empty empty (And (Boolean True) (Integer 10))) (Nothing)  

    -- test "eval And: e1 is True, e2 is not a boolean complex" (eval empty empty (And (If (And (Boolean True) (Boolean True)) (Boolean True) (Boolean False)) 
    --   (If (And (Boolean True) (Boolean True)) (Mul (Float 5.5) (Integer 10)) (Boolean False)))) (Nothing)

    -- -- // Or tests 

    -- test "eval Or: e1 not a boolean, e2 is True simple" (eval empty empty (Or (Integer 10) (Boolean True))) (Just (Boolean True))    

    -- test "eval Or: e1 not a boolean, e2 is False simple" (eval empty empty (Or (Integer 10) (Boolean False))) (Just (Boolean False)) 
    
    -- test "eval Or: e1 not a boolean, e2 is not a boolean simple" (eval empty empty (Or (Integer 10) (Float 15.2))) (Nothing)

    -- test "eval Or: e1 not a boolean, e2 is True complex" (eval empty empty (Or (Let "x" (Float 5.5) (Add (Var "x") (Integer 5))) 
    --   (If (And (Boolean True) (Boolean True)) (Boolean True) (Boolean False)))) (Just (Boolean True))

    -- test "eval Or: e1 not a boolean, e2 is False complex" (eval empty empty (Or (Let "x" (Float 5.5) (Add (Var "x") (Integer 5)))
    --   (If (And (Boolean True) (Boolean False)) (Boolean True) (Boolean False)))) (Just (Boolean False))

    -- test "eval Or: e1 not a boolean, e2 is not a boolean complex" (eval empty empty (Or (Let "x" (Float 5.5) (Add (Var "x") (Integer 5))) 
    --   (If (And (Boolean True) (Boolean False)) (Boolean True) (Float 5.5)))) (Nothing)  

    -- test "eval Or: e1 is True, e2 is True simple" (eval empty empty (Or (Boolean True) (Boolean True))) (Just (Boolean True))
    
    -- test "eval Or: e1 is True, e2 is False simple" (eval empty empty (Or (Boolean True) (Boolean False))) (Just (Boolean True))

    -- test "eval Or: e1 is True, e2 is not a boolean simple" (eval empty empty (Or (Boolean True) (Integer 15))) (Just (Boolean True))
      
    -- test "eval Or: e1 is True, e2 is True complex" (eval empty empty (Or (Let "x" (Boolean True) (Var "x")) 
    --   (And (Boolean True) (Boolean True)))) (Just (Boolean True))
      
    -- test "eval Or: e1 is True, e2 is False complex" (eval empty empty (Or (Let "x" (Boolean True) (Var "x")) 
    --   (And (Boolean True) (Boolean False)))) (Just (Boolean True))  

    -- test "eval Or: e1 is True, e2 is not a boolean complex" (eval empty empty (Or (Let "x" (Boolean True) (Var "x")) 
    --   (Div (Float 5.5) (Integer 22)))) (Just (Boolean True))  

    -- test "eval Or: e1 is False, e2 is True simple" (eval empty empty (Or (Boolean False) (Boolean True))) (Just (Boolean True))
    
    -- test "eval Or: e1 is False, e2 is False simple" (eval empty empty (Or (Boolean False) (Boolean False))) (Just (Boolean False))

    -- test "eval Or: e1 is False, e2 is not a boolean simple" (eval empty empty (Or (Boolean False) (Integer 15))) (Just (Boolean False))
      
    -- test "eval Or: e1 is False, e2 is True complex" (eval empty empty (Or (Let "x" (Boolean False) (Var "x")) 
    --   (And (Boolean True) (Boolean True)))) (Just (Boolean True))
      
    -- test "eval Or: e1 is False, e2 is False complex" (eval empty empty (Or (Let "x" (Boolean False) (Var "x")) 
    --   (And (Boolean True) (Boolean False)))) (Just (Boolean False))  

    -- test "eval Or: e1 is False, e2 is not a boolean complex" (eval empty empty (Or (Let "x" (Boolean False) (Var "x")) 
    --   (Div (Float 5.5) (Integer 22)))) (Just (Boolean False))   
      
    -- -- // Not tests 
    
    -- test "eval Not: e1 True" (eval empty empty (Not (Boolean True))) (Just (Boolean False)) 

    -- test "eval Not: e1 False" (eval empty empty (Not (Boolean False))) (Just (Boolean True)) 
    
    -- test "eval Not: e1 boolean complex" (eval empty empty (Not (Or (Boolean False) (Boolean True))))
    --   (Just (Boolean False)) 

    -- test "eval Not: e1 boolean if complex" (eval empty empty (Not (If (Boolean False)(Boolean True)(Boolean False))))
    --   (Just (Boolean True)) 

    -- test "eval Not: e1 not boolean" (eval empty empty (Not (Integer 10))) (Nothing) 
    
    -- test "eval Not: e1 not boolean complex" (eval empty empty (Not (Add (Integer 5) (Integer 10))))
    --   (Nothing)  

    -- -- // And, Or, Not complex tests 

    -- test "eval Complex boolean operator test 1" (eval empty empty (If (Not (Let "x" (And (Boolean True) (Not (Boolean True))) (Or (Var "x") (Boolean True))))
    --   (Add (Integer 10) (Integer 15)) (Div (Integer 50) (Integer 25)))) (Just (Integer 2)) 

    -- test "eval Complex boolean operator test 2" (eval empty empty (If (Not (Let "x" (Or (Boolean False) (Not (Boolean True))) (And (Var "x") (Boolean True))))
    --   (Add (Integer 10) (Integer 15)) (Div (Integer 50) (Integer 25)))) (Just (Integer 25))      
    
    -- -- // Less_Than Tests 
   
    -- test "eval Less_Than: eval e1 is Integer and eval e2 is Integer greater than e1 simple" 
    --  (eval empty empty ( Less_Than (Integer 5) (Integer 10))) (Just (Boolean True))  
     
    -- test "eval Less_Than: eval e1 is Integer and eval e2 is Integer less than e1 simple" 
    --  (eval empty empty ( Less_Than (Integer 10) (Integer 5))) (Just (Boolean False))    
     
    -- test "eval Less_Than: eval e1 is Integer and eval e2 is Float greater than e1 simple" 
    --  (eval empty empty ( Less_Than (Integer 5) (Float 10))) (Just (Boolean True))  
     
    -- test "eval Less_Than: eval e1 is Integer and eval e2 is Float less than e1 simple" 
    --  (eval empty empty ( Less_Than (Integer 10) (Float 5))) (Just (Boolean False))     

    -- test "eval Less_Than: eval e1 is Integer and eval e2 not a numeric type simple" 
    --  (eval empty empty ( Less_Than (Integer 5) (Boolean True))) (Nothing)   

    -- test "eval Less_Than: eval e1 is Integer and eval e2 is Integer greater than e1 complex" 
    --  (eval empty empty ( Less_Than (Sub (Integer 5) (Integer  7)) (Add (Integer 10) (Integer 20)))) (Just (Boolean True))  
     
    -- test "eval Less_Than: eval e1 is Integer and eval e2 is Integer less than e1 complex" 
    --  (eval empty empty ( Less_Than (Add (Integer 10) (Integer 20)) (Sub (Integer 5) (Integer  7)))) (Just (Boolean False))    
     
    -- test "eval Less_Than: eval e1 is Integer and eval e2 is Float greater than e1 complex" 
    --  (eval empty empty ( Less_Than (Sub (Integer 5) (Integer  7)) (Add (Integer 5) (Float 10)))) (Just (Boolean True))  
     
    -- test "eval Less_Than: eval e1 is Integer and eval e2 is Float less than e1 complex" 
    --  (eval empty empty ( Less_Than (Mul (Integer 5) (Integer  7)) (Add (Integer 5) (Float 10)))) (Just (Boolean False))     

    -- test "eval Less_Than: eval e1 is Integer and eval e2 not a numeric type complex" 
    --  (eval empty empty ( Less_Than (Integer 5) (And (Boolean True) (Boolean True)))) (Nothing) 

    -- test "eval Less_Than: eval e1 is Float and eval e2 is Integer greater than e1 simple" 
    --  (eval empty empty ( Less_Than (Float 5) (Integer 10))) (Just (Boolean True))  
     
    -- test "eval Less_Than: eval e1 is Float and eval e2 is Integer less than e1 simple" 
    --  (eval empty empty ( Less_Than (Float 10) (Integer 5))) (Just (Boolean False))    
     
    -- test "eval Less_Than: eval e1 is Float and eval e2 is Float greater than e1 simple" 
    --  (eval empty empty ( Less_Than (Float 5) (Float 10))) (Just (Boolean True))  
     
    -- test "eval Less_Than: eval e1 is Float and eval e2 is Float less than e1 simple" 
    --  (eval empty empty ( Less_Than (Float 10) (Float 5))) (Just (Boolean False))     

    -- test "eval Less_Than: eval e1 is Float and eval e2 not a numeric type simple" 
    --  (eval empty empty ( Less_Than (Float 5) (Boolean True))) (Nothing)   

    -- test "eval Less_Than: eval e1 is Float and eval e2 is Integer greater than e1 complex" 
    --  (eval empty empty ( Less_Than (Sub (Float 5) (Integer  7)) (Add (Integer 10) (Integer 20)))) (Just (Boolean True))  
     
    -- test "eval Less_Than: eval e1 is Float and eval e2 is Integer less than e1 complex" 
    --  (eval empty empty ( Less_Than (Add (Float 10) (Float 20)) (Sub (Integer 5) (Integer  7)))) (Just (Boolean False))    
     
    -- test "eval Less_Than: eval e1 is Float and eval e2 is Float greater than e1 complex" 
    --  (eval empty empty ( Less_Than (Sub (Float 5) (Float  7)) (Add (Integer 5) (Float 10)))) (Just (Boolean True))  
     
    -- test "eval Less_Than: eval e1 is Float and eval e2 is Float less than e1 complex" 
    --  (eval empty empty ( Less_Than (Mul (Float 5) (Float  7)) (Add (Integer 5) (Float 10)))) (Just (Boolean False))     

    -- test "eval Less_Than: eval e1 is Float and eval e2 not a numeric type complex" 
    --  (eval empty empty ( Less_Than (Float 5) (And (Boolean True) (Boolean True)))) (Nothing)     

    -- test "eval Less_Than: eval e1 is not numeric" 
    --  (eval empty empty ( Less_Than (Boolean True)(Integer 10))) (Nothing) 

    -- test "eval Less_Than: eval e1 and eval e2 equal ints should be false" 
    --  (eval empty empty ( Less_Than (Integer 10) (Integer 10))) (Just (Boolean False))

    -- test "eval Less_Than: eval e1 and eval e2 equal floats should be false" 
    --  (eval empty empty ( Less_Than (Float 10) (Float 10))) (Just (Boolean False))  


    -- -- // Greater_Than Tests 
   
    -- test "eval Greater_Than: eval e1 is Integer and eval e2 is Integer greater than e1 simple" 
    --  (eval empty empty ( Greater_Than (Integer 5) (Integer 10))) (Just (Boolean False))  
     
    -- test "evalGreater_Than: eval e1 is Integer and eval e2 is Integer less than e1 simple" 
    --  (eval empty empty ( Greater_Than (Integer 10) (Integer 5))) (Just (Boolean True))    
     
    -- test "evalGreater_Than: eval e1 is Integer and eval e2 is Float greater than e1 simple" 
    --  (eval empty empty ( Greater_Than (Integer 5) (Float 10))) (Just (Boolean False))  
     
    -- test "eval Greater_Than: eval e1 is Integer and eval e2 is Float less than e1 simple" 
    --  (eval empty empty ( Greater_Than (Integer 10) (Float 5))) (Just (Boolean True))     

    -- test "eval Greater_Than: eval e1 is Integer and eval e2 not a numeric type simple" 
    --  (eval empty empty ( Greater_Than (Integer 5) (Boolean True))) (Nothing)   

    -- test "eval Greater_Than: eval e1 is Integer and eval e2 is Integer greater than e1 complex" 
    --  (eval empty empty ( Greater_Than (Sub (Integer 5) (Integer 7)) (Add (Integer 10) (Integer 20)))) (Just (Boolean False))  
     
    -- test "eval Greater_Than: eval e1 is Integer and eval e2 is Integer less than e1 complex" 
    --  (eval empty empty ( Greater_Than (Add (Integer 10) (Integer 20)) (Sub (Integer 5) (Integer  7)))) (Just (Boolean True))    
     
    -- test "eval Greater_Than: eval e1 is Integer and eval e2 is Float greater than e1 complex" 
    --  (eval empty empty ( Greater_Than (Sub (Integer 5) (Integer 7)) (Add (Integer 5) (Float 10)))) (Just (Boolean False))  
     
    -- test "eval Greater_Than: eval e1 is Integer and eval e2 is Float less than e1 complex" 
    --  (eval empty empty ( Greater_Than (Mul (Integer 5) (Integer 7)) (Add (Integer 5) (Float 10)))) (Just (Boolean True))     

    -- test "eval Greater_Than: eval e1 is Integer and eval e2 not a numeric type complex" 
    --  (eval empty empty ( Greater_Than (Integer 5) (And (Boolean True) (Boolean True)))) (Nothing) 

    -- test "eval Greater_Than: eval e1 is Float and eval e2 is Integer greater than e1 simple" 
    --  (eval empty empty ( Greater_Than (Float 5) (Integer 10))) (Just (Boolean False))  
     
    -- test "eval Greater_Than: eval e1 is Float and eval e2 is Integer less than e1 simple" 
    --  (eval empty empty ( Greater_Than (Float 10) (Integer 5))) (Just (Boolean True))    
     
    -- test "eval Greater_Than: eval e1 is Float and eval e2 is Float greater than e1 simple" 
    --  (eval empty empty ( Greater_Than (Float 5) (Float 10))) (Just (Boolean False))  
     
    -- test "eval Greater_Than: eval e1 is Float and eval e2 is Float less than e1 simple" 
    --  (eval empty empty ( Greater_Than (Float 10) (Float 5))) (Just (Boolean True))     

    -- test "eval Greater_Than: eval e1 is Float and eval e2 not a numeric type simple" 
    --  (eval empty empty ( Greater_Than (Float 5) (Boolean True))) (Nothing)   

    -- test "eval Greater_Than: eval e1 is Float and eval e2 is Integer greater than e1 complex" 
    --  (eval empty empty ( Greater_Than (Sub (Float 5) (Integer  7)) (Add (Integer 10) (Integer 20)))) (Just (Boolean False))  
     
    -- test "eval Greater_Than: eval e1 is Float and eval e2 is Integer less than e1 complex" 
    --  (eval empty empty ( Greater_Than (Add (Float 10) (Float 20)) (Sub (Integer 5) (Integer  7)))) (Just (Boolean True))    
     
    -- test "eval Greater_Than: eval e1 is Float and eval e2 is Float greater than e1 complex" 
    --  (eval empty empty ( Greater_Than (Sub (Float 5) (Float  7)) (Add (Integer 5) (Float 10)))) (Just (Boolean False))  
     
    -- test "eval Greater_Than: eval e1 is Float and eval e2 is Float less than e1 complex" 
    --  (eval empty empty ( Greater_Than (Mul (Float 5) (Float  7)) (Add (Integer 5) (Float 10)))) (Just (Boolean True))     

    -- test "eval Greater_Than: eval e1 is Float and eval e2 not a numeric type complex" 
    --  (eval empty empty ( Greater_Than (Float 5) (And (Boolean True) (Boolean True)))) (Nothing)     

    -- test "eval Greater_Than: eval e1 is not numeric" 
    --  (eval empty empty ( Greater_Than (Boolean True)(Integer 10))) (Nothing) 

    -- test "eval Greater_Than: eval e1 and eval e2 equal ints should be false" 
    --  (eval empty empty ( Greater_Than (Integer 10) (Integer 10))) (Just (Boolean False))

    -- test "eval Greater_Than: eval e1 and eval e2 equal floats should be false" 
    --  (eval empty empty ( Greater_Than (Float 10) (Float 10))) (Just (Boolean False)) 


    -- -- // Equal_To Tests 
   
    -- test "eval Equal_To: eval e1 is Integer and eval e2 is Integer not equal to e1 simple" 
    --  (eval empty empty ( Equal_To (Integer 5) (Integer 10))) (Just (Boolean False))  
     
    -- test "eval Equal_To: eval e1 is Integer and eval e2 is Integer equal to e1 simple" 
    --  (eval empty empty ( Equal_To (Integer 5) (Integer 5))) (Just (Boolean True))    
     
    -- test "eval Equal_To: eval e1 is Integer and eval e2 is Float not equal to e1 simple" 
    --  (eval empty empty ( Equal_To (Integer 5) (Float 10))) (Just (Boolean False))  
     
    -- test "eval Equal_To: eval e1 is Integer and eval e2 is Float equal to e1 simple" 
    --  (eval empty empty ( Equal_To (Integer 5) (Float 5))) (Just (Boolean True))     

    -- test "eval Equal_To: eval e1 is Integer and eval e2 not a numeric type simple" 
    --  (eval empty empty ( Equal_To (Integer 5) (Boolean True))) (Nothing)   

    -- test "eval Equal_To: eval e1 is Integer and eval e2 is Integer not equal e1 complex" 
    --  (eval empty empty ( Equal_To (Sub (Integer 5) (Integer  7)) (Add (Integer 10) (Integer 20)))) (Just (Boolean False))  
     
    -- test "eval Equal_To: eval e1 is Integer and eval e2 is Integer equal to e1 complex" 
    --  (eval empty empty ( Equal_To (Add (Integer 10) (Integer 20)) (Sub (Integer 35) (Integer  5)))) (Just (Boolean True))    
     
    -- test "eval Equal_To: eval e1 is Integer and eval e2 is Float not equal to e1 complex" 
    --  (eval empty empty ( Equal_To (Sub (Integer 5) (Integer  7)) (Add (Integer 5) (Float 10)))) (Just (Boolean False))  
     
    -- test "eval Equal_To: eval e1 is Integer and eval e2 is Float equal to e1 complex" 
    --  (eval empty empty ( Equal_To (Mul (Integer 5) (Integer  7)) (Add (Integer 25) (Float 10)))) (Just (Boolean True))     

    -- test "eval Equal_To: eval e1 is Integer and eval e2 not a numeric type complex" 
    --  (eval empty empty ( Equal_To (Integer 5) (And (Boolean True) (Boolean True)))) (Nothing) 

    -- test "eval Equal_To: eval e1 is Float and eval e2 is Integer not equal to e1 simple" 
    --  (eval empty empty ( Equal_To (Float 5) (Integer 10))) (Just (Boolean False))  
     
    -- test "eval Equal_To: eval e1 is Float and eval e2 is Integer equal to e1 simple" 
    --  (eval empty empty ( Equal_To (Float 10) (Integer 10))) (Just (Boolean True))    
     
    -- test "eval Equal_To: eval e1 is Float and eval e2 is Float not equal to e1 simple" 
    --  (eval empty empty ( Equal_To (Float 5) (Float 10))) (Just (Boolean False))  
     
    -- test "eval Equal_To: eval e1 is Float and eval e2 is Float equal to e1 simple" 
    --  (eval empty empty ( Equal_To (Float 10) (Float 10))) (Just (Boolean True))     

    -- test "eval Equal_To: eval e1 is Float and eval e2 not a numeric type simple" 
    --  (eval empty empty ( Equal_To (Float 5) (Boolean True))) (Nothing)   

    -- test "eval Equal_To: eval e1 is Float and eval e2 is Integer not equal to e1 complex" 
    --  (eval empty empty ( Equal_To (Sub (Float 5) (Integer  7)) (Add (Integer 10) (Integer 20)))) (Just (Boolean False))  
     
    -- test "eval Equal_To: eval e1 is Float and eval e2 is Integer equal to e1 complex" 
    --  (eval empty empty ( Equal_To (Add (Float 10) (Float 20)) (Sub (Integer 35) (Integer  5)))) (Just (Boolean True))    
     
    -- test "eval Equal_To: eval e1 is Float and eval e2 is Float not equal to e1 complex" 
    --  (eval empty empty ( Equal_To (Sub (Float 5) (Float  7)) (Add (Integer 5) (Float 10)))) (Just (Boolean False))  
     
    -- test "eval Equal_To: eval e1 is Float and eval e2 is Float equal to e1 complex" 
    --  (eval empty empty ( Equal_To (Mul (Float 5) (Float  7)) (Add (Integer 25) (Float 10)))) (Just (Boolean True))     

    -- test "eval Equal_To: eval e1 is Float and eval e2 not a numeric type complex" 
    --  (eval empty empty ( Equal_To (Float 5) (And (Boolean True) (Boolean True)))) (Nothing)     

    -- test "eval Equal_To: eval e1 is a boolean equal to eval e2 also boolean" 
    --  (eval empty empty ( Equal_To (Boolean True)(Boolean True))) (Just (Boolean True)) 

    -- test "eval Equal_To: eval e1 is a boolean not equal to eval e2 also boolean" 
    --  (eval empty empty ( Equal_To (Boolean True)(Boolean False))) (Just (Boolean False))  

    -- test "eval Equal_To: eval e1 is a Nothing and eval e2 also Nothing" 
    --  (eval empty empty ( Equal_To (Sub (Integer 5) (Boolean True))(Add (Integer 5) (Boolean False)))) (Just (Boolean True)) 

    -- test "eval Equal_To: eval e1 is a Nothing  not equal to eval e2 also boolean" 
    --  (eval empty empty ( Equal_To (Sub (Integer 5) (Boolean True))(Boolean False))) (Nothing)  


    -- Cond If equality tests 

    -- test "eval Cond and If are same test 1" (eval empty empty ( If (Boolean True) (Add (Integer 5) (Integer 2)) (Sub (Integer 5) (Integer 2))))
    --  (eval empty empty ( Cond [(Boolean True, (Add (Integer 5) (Integer 2)))] (Just (Sub (Integer 5) (Integer 2)))))  

    -- test "eval Cond and If are same test 2" (eval empty empty ( If (Boolean False) (Add (Integer 5) (Integer 2)) 
    --  (If (Boolean True) (Sub (Integer 5) (Integer 2)) (Mul (Integer 5) (Integer 2))))) 
    --    (eval empty empty ( Cond [(Boolean False, (Add (Integer 5) (Integer 2))), (Boolean True, (Sub (Integer 5) (Integer 2)))] 
    --      (Just (Mul (Integer 5) (Integer 2)))))
  
    -- -- // Cond Tests
    -- test "eval Cond: first true" (eval empty empty ( Cond [(Boolean True, (Add (Integer 5) (Integer 2)))] Nothing))
    --    (Just (Integer 7))

    -- test "eval Cond: next true" (eval empty empty ( Cond [(Boolean False, (Add (Integer 5) (Integer 2))), 
    --     (Boolean True, (Div (Integer 4) (Integer 2)))] Nothing))
    --    (Just (Integer 2))

    -- test "eval Cond: no true" (eval empty empty ( Cond [(Boolean False, (Add (Integer 5) (Integer 2))), 
    --     (Boolean False, (Div (Integer 4) (Integer 2)))] Nothing))
    --    (Nothing)

    -- test "eval Cond: not boolean values" (eval empty empty ( Cond [(Float 5.1, (Add (Integer 5) (Integer 2))), 
    --     (Boolean False, (Div (Integer 4) (Integer 2)))] Nothing))
    --    (Nothing)
       
    -- test "eval Cond: first true" (eval empty empty ( Cond [(Boolean True, (Add (Integer 5) (Integer 2)))] 
    --     (Just (Sub (Integer 5) (Integer 2)))))
    --    (Just (Integer 7))

    -- test "eval Cond: next true" (eval empty empty ( Cond [(Boolean False, (Add (Integer 5) (Integer 2))), 
    --     (Boolean True, (Div (Integer 4) (Integer 2)))] (Just (Mul (Float 5.1) (Float 2.0)))))
    --    (Just (Integer 2))

    -- test "eval Cond: no true" (eval empty empty ( Cond [(Boolean False, (Add (Integer 5) (Integer 2))), 
    --     (Boolean False, (Div (Integer 4) (Integer 2)))] (Just (Float 2.2))))
    --    (Just (Float 2.2))

    -- test "eval Cond: not boolean values" (eval empty empty ( Cond [(Float 5.1, (Add (Integer 5) (Integer 2))), 
    --     (Boolean False, (Div (Integer 4) (Integer 2)))] (Just (Float 2.1))))
    --    (Nothing)


    -- // Pair Tests    
    -- test "eval Pair: eval e1 and eval e2 are nothing, simple" (eval empty empty ( Pair 
    --  (Add (Integer 5) (Boolean False)) (Var "x"))) (Nothing)  

    -- test "eval Pair: eval e1 and eval e2 are nothing, complex" (eval empty empty ( Pair 
    --  (If (Boolean False) (Integer 5) (Div (Var "y") (Float 5.5))) 
    --   (Let "x" (Boolean True) (Equal_To (Integer 5) (Boolean True)))))
    --    (Nothing) 

    -- test "eval Pair: eval e1 is not nothing but eval e2 is nothing, simple" (eval empty empty ( Pair 
    --  (Add (Integer 5) (Float 6.5)) (Var "x"))) (Nothing)     

    -- test "eval Pair: eval e1 is not nothing but eval e2 is nothing, complex" (eval empty empty ( Pair 
    --  (If (Boolean False) (Integer 5) (Let "y" (Integer 10) (Div (Var "x") (Float 5.5)))) 
    --   (Let "x" (Boolean True) (Equal_To (Integer 5) (Boolean True)))))
    --    (Nothing)  

    -- test "eval Pair: eval e1 is not nothing but eval e2 is not nothing, simple" (eval empty empty ( Pair 
    --  (Add (Integer 5) (Float 6.5)) (Let "x" (Boolean False) (Var "x"))))
    --  (Just (Pair (Float 11.5) (Boolean False)))     

    -- test "eval Pair: eval e1 is not nothing but eval e2 is not nothing, complex" (eval empty empty ( Pair 
    --  (If (Boolean False) (Integer 5) (Let "y" (Integer 11) (Div (Var "y") (Float 5.5)))) 
    --   (Let "x" (Boolean True) (Equal_To (Integer 5) (Float 5)))))
    --    (Just (Pair (Float 2) (Boolean True)))     

    -- -- // Left Tests    
    -- test "eval Left: Expr is nothing, simple" (eval empty empty (
    --  Left (Add (Boolean True) (Integer 10)))) (Nothing)  

    -- test "eval Left: Expr is nothing, complex" (eval empty empty ( Left (Pair 
    --  (If (Boolean False) (Integer 5) (Div (Var "y") (Float 5.5))) 
    --   (Let "x" (Boolean True) (Equal_To (Integer 5) (Boolean True))))))
    --    (Nothing) 

    -- test "eval Left: Expr is something but not a pair, simple" (eval empty empty ( Left (Boolean False))) 
    --  (Nothing)   

    -- test "eval Left: Expr is something but not a pair, complex" (eval empty empty ( Left
    --  (Equal_To (Add (Integer 5) (Float 6.5)) (Let "x" (Float 11.5) (Var "x")))))
    --   (Nothing)

    -- test "eval Left: Expr is a pair that evals to nothing, simple" (eval empty empty ( Left 
    --  ( Pair (Add (Integer 5) (Boolean False)) (Var "x")))) (Nothing)     

    -- test "eval Left: Expr is a pair that evals to nothing, simplex" (eval empty empty ( Left ( Pair 
    --  (If (Boolean False) (Integer 5) (Let "y" (Integer 10) (Div (Var "x") (Float 5.5)))) 
    --   (Let "x" (Boolean True) (Equal_To (Integer 5) (Boolean True))))))
    --    (Nothing)  

    -- test "eval Left: Expr is a good pair, simplex" (eval empty empty ( Left (Pair 
    --  (Add (Integer 5) (Float 6.5)) (Let "x" (Boolean False) (Var "x")))))
    --  (Just (Float 11.5))     

    -- test "eval Left: Expr is a good pair, complex" (eval empty empty ( Left (Pair 
    --  (If (Boolean False) (Integer 5) (Let "y" (Integer 11) (Div (Var "y") (Float 5.5)))) 
    --   (Let "x" (Boolean True) (Equal_To (Integer 5) (Float 5))))))
    --    (Just (Float 2))     

    -- -- // Right Tests    
    -- test "eval Right: Expr is nothing, simple" (eval empty empty (
    --  Left (Add (Boolean True) (Integer 10)))) (Nothing)  

    -- test "eval Right: Expr is nothing, complex" (eval empty empty ( Left (Pair 
    --  (If (Boolean False) (Integer 5) (Div (Var "y") (Float 5.5))) 
    --   (Let "x" (Boolean True) (Equal_To (Integer 5) (Boolean True))))))
    --    (Nothing) 

    -- test "eval Right: Expr is something but not a pair, simple" (eval empty empty ( Right (Boolean False)) )
    --  (Nothing)   

    -- test "eval Right: Expr is something but not a pair, complex" (eval empty empty ( Right
    --  (Equal_To (Add (Integer 5) (Float 6.5)) (Let "x" (Float 11.5) (Var "x"))))) 
    --   (Nothing)

    -- test "eval Right: Expr is a pair that evals to nothing, simple" (eval empty empty ( Right 
    --  ( Pair (Add (Integer 5) (Boolean False)) (Var "x")))) (Nothing)     

    -- test "eval Right: Expr is a pair that evals to nothing, simplex" (eval empty empty ( Right ( Pair 
    --  (If (Boolean False) (Integer 5) (Let "y" (Integer 10) (Div (Var "x") (Float 5.5)))) 
    --   (Let "x" (Boolean True) (Equal_To (Integer 5) (Boolean True))))))
    --    (Nothing)  

    -- test "eval Right: Expr is a good pair, simplex" (eval empty empty ( Right (Pair 
    --  (Add (Integer 5) (Float 6.5)) (Let "x" (Boolean False) (Var "x")))))
    --  (Just (Boolean False))     

    -- test "eval Right: Expr is a good pair, complex" (eval empty empty ( Right (Pair 
    --  (If (Boolean False) (Integer 5) (Let "y" (Integer 11) (Div (Var "y") (Float 5.5)))) 
    --   (Let "x" (Boolean True) (Equal_To (Integer 5) (Float 5))))))
    --    (Just (Boolean True))      

    -- // Real_Pred tests 
    test "eval Real_Pred: Expr is a float simple" (eval empty empty ( Real_Pred 
     (Val (Float 5.5)))) (R.Success (Boolean True))

    -- test "eval Real_Pred: Expr is a float complex" (eval empty empty ( Real_Pred 
    --  (If (Boolean True) (Div (Integer 10) (Float 5.1)) (Integer 10))))
    --   (Just (Boolean True))  

    test "eval Real_Pred: Expr is not a float simple" (eval empty empty ( Real_Pred 
     (Val (Integer 5)))) (R.Success (Boolean False))

    -- test "eval Real_Pred: Expr is not a float complex" (eval empty empty ( Real_Pred 
    --  (If (Boolean True) (Div (Integer 10) (Boolean False)) (Integer 10))))
    --   (Just (Boolean False))      

    -- // Integer_Pred tests 
    test "eval Integer_Pred: Expr is a integer simple" (eval empty empty ( Integer_Pred 
     (Val (Integer 5)))) (R.Success (Boolean True))

    -- test "eval Integer_Pred: Expr is a integer complex" (eval empty empty ( Integer_Pred 
    --  (If (Boolean True) (Div (Integer 10) (Integer 5)) (Integer 10))))
    --   (Just (Boolean True))  

    test "eval Integer_Pred: Expr is not a integer simple" (eval empty empty ( Integer_Pred 
     (Val (Float 5)))) (R.Success (Boolean False))

    -- test "eval Integer_Pred: Expr is not a integer complex" (eval empty empty ( Integer_Pred 
    --  (If (Boolean True) (Div (Integer 10) (Boolean False)) (Integer 10))))
    --   (Just (Boolean False))     

    -- // Number_Pred tests 
    test "eval Number_Pred: Expr is a integer simple" (eval empty empty ( Number_Pred 
     (Val (Integer 5)))) (R.Success (Boolean True))

    -- test "eval Number_Pred: Expr is a integer complex" (eval empty empty ( Number_Pred 
    --  (If (Boolean True) (Div (Integer 10) (Integer 5)) (Integer 10))))
    --   (Just (Boolean True))  

    test "eval Number_Pred: Expr is a float simple" (eval empty empty ( Number_Pred 
     (Val (Float 5.5)))) (R.Success (Boolean True))

    -- test "eval Number_Pred: Expr is a float complex" (eval empty empty ( Number_Pred 
    --  (If (Boolean True) (Div (Integer 10) (Float 5.1)) (Integer 10))))
    --   (Just (Boolean True))   

    test "eval Number_Pred: Expr is not a integer or float simple" (eval empty empty ( Number_Pred 
     (Val (Boolean False)))) (R.Success (Boolean False))

    -- test "eval Number_Pred: Expr is not a integer or float complex" (eval empty empty ( Number_Pred 
    --  (If (Boolean True) (Div (Integer 10) (Boolean False)) (Integer 10))))
    --   (Just (Boolean False))     

    -- // Boolean_Pred tests 
    test "eval Boolean_Pred: Expr is a boolean simple" (eval empty empty ( Boolean_Pred 
     (Val (Boolean False)))) (R.Success (Boolean True))

    -- test "eval Boolean_Pred: Expr is a boolean complex" (eval empty empty ( Boolean_Pred 
    --  (If (Boolean True) (Less_Than (Integer 10) (Integer 5)) (Integer 10))))
    --   (Just (Boolean True))  

    test "eval Boolean_Pred: Expr is not a boolean simple" (eval empty empty ( Boolean_Pred 
     (Val (Float 5)))) (R.Success (Boolean False))

    -- test "eval Boolean_Pred: Expr is not a boolean complex" (eval empty empty ( Boolean_Pred 
    --  (If (Boolean True) (Div (Integer 10) (Boolean False)) (Integer 10))))
    --   (Just (Boolean False))   

    -- // Pair_Pred tests 
    -- test "eval Pair_Pred: Expr is a pair simple" (eval empty empty ( Pair_Pred 
    --  (Pair (Add (Integer 5) (Float 6.5)) (Let "x" (Boolean False) (Var "x")))))
    --   (Just (Boolean True))

    -- test "eval Pair_Pred: Expr is a pair complex" (eval empty empty ( Pair_Pred 
    --   (Pair (If (Boolean False) (Integer 5) 
    --    (Let "y" (Integer 11) (Div (Var "y") (Float 5.5)))) 
    --    (Let "x" (Boolean True) (Equal_To (Integer 5) (Float 5))))))
    --   (Just (Boolean True))        

    test "eval Pair_Pred: Expr is not a pair simple" (eval empty empty ( Pair_Pred 
     (Val (Boolean False)))) (R.Success (Boolean False))

    -- test "eval Pair_Pred: Expr is not a pair complex" (eval empty empty ( Pair_Pred 
    --  (If (Boolean True) (Less_Than (Integer 10) (Integer 5)) (Integer 10))))
    --   (Just (Boolean False))  

    -- // New Pair tests 
    -- test "eval Pair Add, e1 is pair" (eval empty empty ( Add (
    --   Pair (Integer 5) (Integer 10)) (Integer 5))) (Nothing)

    -- test "eval Pair Add, e2 is pair" (eval empty empty ( Add (Integer 5) (
    --   Pair (Integer 5) (Integer 10)))) (Nothing)  

    -- test "eval Pair Add, e1 and e2 are pairs" (eval empty empty ( Add (
    --   Pair (Integer 5) (Integer 10)) (Pair (Float 5.6) (Boolean False)))) (Nothing)   

    -- test "eval Pair Sub, e1 is pair" (eval empty empty ( Sub (
    --   Pair (Integer 5) (Integer 10)) (Integer 5))) (Nothing)

    -- test "eval Pair Sub, e2 is pair" (eval empty empty ( Sub (Integer 5) (
    --   Pair (Integer 5) (Integer 10)))) (Nothing)  

    -- test "eval Pair Sub, e1 and e2 are pairs" (eval empty empty ( Sub (
    --   Pair (Integer 5) (Integer 10)) (Pair (Float 5.6) (Boolean False)))) (Nothing)    

    -- test "eval Pair Mul, e1 is pair" (eval empty empty ( Mul (
    --   Pair (Integer 5) (Integer 10)) (Integer 5))) (Nothing)

    -- test "eval Pair Mul, e2 is pair" (eval empty empty ( Mul (Integer 5) (
    --   Pair (Integer 5) (Integer 10)))) (Nothing)  

    -- test "eval Pair Mul, e1 and e2 are pairs" (eval empty empty ( Mul (
    --   Pair (Integer 5) (Integer 10)) (Pair (Float 5.6) (Boolean False)))) (Nothing)    

    -- test "eval Pair Div, e1 is pair" (eval empty empty ( Div (
    --   Pair (Integer 5) (Integer 10)) (Integer 5))) (Nothing)

    -- test "eval Pair Div, e2 is pair" (eval empty empty ( Div (Integer 5) (
    --   Pair (Integer 5) (Integer 10)))) (Nothing)  

    -- test "eval Pair Div, e1 and e2 are pairs" (eval empty empty ( Div (
    --   Pair (Integer 5) (Integer 10)) (Pair (Float 5.6) (Boolean False)))) (Nothing)      

    -- test "eval Pair let" (eval empty empty ( Let "x" (
    --   Pair (Integer 5) (Float 5.5))
    --   (Var "x"))) (Just (Pair (Integer 5) (Float 5.5)))

    -- // Tests for call 
    test "eval Call: call with no function known" (eval empty empty (Call "hello" [Val (Integer 10)]))
     (fail "Called function hello does not exist.")  

    test "eval Call: call with a variable of same name in env" (eval empty (set empty "hello" (Integer 10)) (Call "hello" [Val (Integer 10)]))
     (fail "Called function hello does not exist.")  

    -- test "eval Call: call with a variable of same name in globalenv" (eval [("hello", (Define "hello" $ Integer 10))] empty (Call "hello" [(Integer 10)]))
    --  (Nothing)   

    -- test "eval Call: call with a function of same name" (eval [("hello", (Defun "hello" ("x",[]) (Var "x")))] 
    --  empty (Call "hello" [(Integer 10)]))  (Just (Integer 10))

    -- test "eval Call: call with a function of same name with nothing input" (eval [("hello", 
    --  (Defun "hello" ("x", []) (Var "x")))] 
    --   empty (Call "hello" [(Add (Boolean False) (Integer 10))]))  (Nothing)  

    -- -- // Tests for call with functions with multiple args 
    -- test "eval Call: call with a function with multiple variables and enough arguments 1" (eval 
    --  [("hello", (Defun "hello" ("x",["y"]) (Var "x")))] empty (Call "hello" [Integer 10, Integer 20])) 
    --  (Just (Integer 10))  

    -- test "eval Call: call with a function with multiple variables and enough arguments 2" (eval 
    --  [("hello", (Defun "hello" ("x",["y"]) (Add (Var "x") (Var "y"))))] empty (Call "hello" [Integer 10, Integer 20]))  
    --  (Just (Integer 30))    

    -- test "eval Call: call with a function with multiple variables and enough arguments 3" (eval 
    --  [("hello", (Defun "hello" ("x",["y"]) (Add (Var "x") (Div (Var "y") (Integer 2)))))] empty (Call "hello" [Integer 10, Integer 20]))  
    --  (Just (Integer 20))    

    -- test "eval Call: call with a function with multiple variables and enough arguments 4" (eval 
    --  [("hello", (Defun "hello" ("x",["y"]) (Add (Var "y") (Div (Var "x") (Integer 2)))))] empty (Call "hello" [Integer 10, Integer 20]))  
    --  (Just (Integer 25))     

    -- test "eval Call: call with a function with multiple variables and enough arguments 5" (eval 
    --  [("hello", (Defun "hello" ("x",["y", "z"]) (If (Var "z") (Boolean True) (Add (Var "y") (Div (Var "x") (Integer 2))))))] empty 
    --   (Call "hello" [Integer 10, Integer 20, Boolean False]))  
    --  (Just (Integer 25))      

    -- test "eval Call: call with a function with multiple variables and not enough arguments " (eval 
    --  [("hello", (Defun "hello" ("x",["y"]) (Var "x")))] empty (Call "hello" [Integer 10])) 
    --   (Nothing)    

    -- test "eval Call: call with a function with variables and but too many arguments " (eval 
    --  [("hello", (Defun "hello" ("x",["y"]) (Var "x")))] empty (Call "hello" 
    --   [Integer 10, Integer 30, Integer 40])) 
    --   (Nothing)         
     
-- |Run the given protoScheme s-expression, returning an s-expression
-- representation of the result.
{-
  Added in check for if the S.Expr is a program or not. 
    If it is a program then do the evalProgram, otherwise do the normal eval 
-}
runSExpression :: S.Expr -> R.Result S.Expr
runSExpression se =
    case se of 
      (S.List[S.Symbol "Program", S.List defs, e]) -> do
          v <- evalProgram (programFromSExpression se) 
          return (valueToSExpression v)
      _ -> do 
          v <- eval empty empty (fromSExpression se) 
          return (valueToSExpression v)
    

test_runSExpression = do

    -- test "run: (+ 1 2)"
    --     (runSExpression $ S.List [S.Symbol "+", S.Integer 1, S.Integer 2])
    --     (R.Success $ S.Integer 3)

    test "runSExpression Test Variable" (runSExpression $ S.Symbol "v") (fail "Variable v not defined.")

    -- Integer Tests

    test "Integer runSExpression 42" (runSExpression $ S.Integer 42) (R.Success (S.Integer 42))

    -- test "Integer runSExpression Test Add" (runSExpression $ S.List [S.Symbol "+",
    --  S.Integer 4, S.Integer 10]) (R.Success $ S.Integer 14)

    -- test "Integer runSExpression Test Sub" (runSExpression $ S.List [S.Symbol "-",
    --  S.Integer 4, S.Integer 10]) (R.Success $ S.Integer (-6))

    -- test "Integer runSExpression Test Mul" (runSExpression $ S.List [S.Symbol "*",
    --  S.Integer 4, S.Integer 10]) (R.Success $ S.Integer 40)

    -- test "Integer runSExpression Test Div" (runSExpression $ S.List [S.Symbol "/",
    --  S.Integer 4, S.Integer 10]) (R.Success $ S.Integer 0)

    -- test "Integer runSExpression Test Nested Operations" (runSExpression $ S.List [S.Symbol "/",
    --  S.List [S.Symbol "+", S.Integer 4, S.Integer 10], S.List [S.Symbol "-",
    --   S.Integer 10, S.Integer 6]]) 
    --  (R.Success $ S.Integer 3)

    -- test "Integer runSExpression Test Let  Simple" (runSExpression $ S.List [S.Symbol "let", S.List [S.Symbol "x",
    --  S.List [S.Symbol "+", S.Integer 10, S.Integer 4]], S.List [S.Symbol "+", S.Symbol "x", S.Integer 1]])
    --  (R.Success $ S.Integer 15)

    -- test "Integer runExpression Test Let Complex" (runSExpression $ S.List [S.Symbol "let", S.List [S.Symbol "y",
    --  S.List [S.Symbol "-", S.Integer 20, S.Integer 8]], S.List [S.Symbol "let", S.List [S.Symbol "x",
    --   S.List [S.Symbol "+", S.Symbol "y", S.Integer 4]], S.List [S.Symbol "+",
    --    S.Symbol "x", S.Integer 1]]])
    --    (R.Success $ S.Integer 17)

    -- Real Tests 

    test "Real runSExpression 42" (runSExpression $ S.Real 42.0) (R.Success $ S.Real 42.0)

    -- test "Real runSExpression Test Add" (runSExpression $ S.List [S.Symbol "+",
    --  S.Real 4.1, S.Real 10.1]) (R.Success $ S.Real 14.2)

    -- test "Real runSExpression Test Sub" (runSExpression $ S.List [S.Symbol "-",
    --  S.Real 4.1, S.Real 10.1]) (R.Success $ S.Real (-6.0))

    -- test "Real runSExpression Test Mul" (runSExpression $ S.List [S.Symbol "*",
    --  S.Real 4.1, S.Real 10.1]) (R.Success $ S.Real 41.41)

    -- test "Real runSExpression Test Div" (runSExpression $ S.List [S.Symbol "/",
    --  S.Real 4.1, S.Real 10.1]) (R.Success $ S.Real 0.4059405940594059)

    -- test "Real runSExpression Test Nested Operations" (runSExpression $ S.List [S.Symbol "/",
    --  S.List [S.Symbol "+", S.Real 4.1, S.Real 10.1], S.List [S.Symbol "-",
    --   S.Real 4.1, S.Real 10.1]]) (R.Success $ S.Real (-2.3666666666666667))

    -- test "Real runSExpression Test Let  Simple" (runSExpression $ S.List [S.Symbol "let", S.List [S.Symbol "x",
    --  S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]])
    --  (R.Success $ S.Real 15.299999999999999)

    -- test "Real runSExpression Test Let Complex" (runSExpression $ S.List [S.Symbol "let", S.List [S.Symbol "y",
    --  S.List [S.Symbol "-", S.Real 20.1, S.Real 8.1]], S.List [S.Symbol "let", S.List [S.Symbol "x",
    --   S.List [S.Symbol "+", S.Symbol "y", S.Real 4.1]], S.List [S.Symbol "+",
    --    S.Symbol "x", S.Real 1.1]]])
    --  (R.Success $ S.Real 17.200000000000003) 

    -- -- Mixed Tests 

    -- test "Mixed runSExpression Test Add" (runSExpression $ S.List [S.Symbol "+",
    --  S.Real 4.1, S.Integer 10]) (R.Success $ S.Real 14.1)

    -- test "Mixed runSExpression Test Sub" (runSExpression $ S.List [S.Symbol "-",
    --  S.Real 4.1, S.Integer 10]) (R.Success $ S.Real (-5.9))

    -- test "Mixed runSExpression Test Mul" (runSExpression $ S.List [S.Symbol "*",
    --  S.Real 4.1, S.Integer 10]) (Just $ S.Real 41)

    -- test "Mixed runSExpression Test Div" (runSExpression $ S.List [S.Symbol "/",
    --  S.Real 4.1, S.Integer 10]) (Just $ S.Real 0.41)

    -- test "Mixed runSExpression Test Nested Operations" (runSExpression $ S.List [S.Symbol "/",
    --  S.List [S.Symbol "+", S.Real 4.1, S.Integer 10], S.List [S.Symbol "-",
    --   S.Real 4.1, S.Real 10.1]]) (Just $ S.Real (-2.35))

    -- test "Mixed runSExpression Test Let  Simple" (runSExpression $ S.List [S.Symbol "let", S.List [S.Symbol "x",
    --  S.List [S.Symbol "+", S.Integer 10, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]])
    --  (Just $ S.Real 15.2)

    -- test "Mixed runSExpression Test Let Complex" (runSExpression $ S.List [S.Symbol "let", S.List [S.Symbol "y",
    --  S.List [S.Symbol "-", S.Integer 20, S.Real 8.1]], S.List [S.Symbol "let", S.List [S.Symbol "x",
    --   S.List [S.Symbol "+", S.Symbol "y", S.Real 4.1]], S.List [S.Symbol "+",
    --    S.Symbol "x", S.Real 1.1]]])
    --  (Just $ S.Real 17.1)   


    -- -- Boolean tests

    -- test "Boolean runSExpression Test 1" (runSExpression $ S.Boolean False) 
    --   (Just $ S.Boolean False)

    -- test "Boolean runSExpression Test 2" (runSExpression $ S.Boolean True) 
    --   (Just $ S.Boolean True)  

    -- -- If tests 

    -- test "If runSExpression Test e1 is True Simple" (runSExpression $ S.List 
    --   [S.Symbol "if", S.Boolean True, S.Integer 10, S.Real 15])
    --     (Just $ S.Integer 10)  

    -- test "If runSExpression Test e1 is False Simple" (runSExpression $ S.List 
    --   [S.Symbol "if", S.Boolean False, S.Integer 10, S.Real 15])
    --     (Just $ S.Real 15)      

    -- test "If runSExpression Test e1 is True Complex" (runSExpression $ S.List 
    --   [S.Symbol "if", S.Boolean True, S.List [S.Symbol "+", S.Integer 10, S.Integer 15] , S.Real 15])
    --     (Just $ S.Integer 25)  

    -- test "If runSExpression Test e1 is False Complex" (runSExpression $ S.List 
    --   [S.Symbol "if", S.Boolean False, S.Integer 10, S.List [S.Symbol "+", S.Real 10.1, S.Real 15.1]])
    --     (Just $ S.Real 25.2)     

    -- test "If runSExpression Test e1 is not a boolean" (runSExpression $ S.List 
    --   [S.Symbol "if", S.List [S.Symbol "+", S.Integer 10, S.Integer 15], S.Integer 10, S.Real 15])
    --     (Nothing)       

    -- -- And tests
    -- test "And runSExpression Test 1" (runSExpression $ S.List [S.Symbol "and" , S.Boolean True, S.Integer 10]) 
    --     (Nothing)   

    -- test "And runSExpression Test 2" (runSExpression $ S.List [
    --     S.Symbol "and" , S.Boolean False, S.List [S.Symbol "let", S.List [S.Symbol "x",
    --       S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
    --     (Just $ S.Boolean False)       

    -- test "And runSExpression Test 3" (runSExpression $ S.List [
    --     S.Symbol "and" , S.List [S.Symbol "and" , S.Integer 10, S.Real 15.1], 
    --      S.List [S.Symbol "let", S.List [S.Symbol "x",
    --       S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
    --     (Nothing)    

    -- test "And runSExpression Test 4" (runSExpression $ S.List [S.Symbol "and" , S.Boolean True, S.Boolean False]) 
    --     (Just $ S.Boolean False)
      
    -- test "And runSExpression Test 5" (runSExpression $ S.List [S.Symbol "and" , S.Boolean True, S.Boolean True]) 
    --     (Just $ S.Boolean True)

    -- -- Or tests
    -- test "Or runSExpression Test 1" (runSExpression $ S.List [
    --     S.Symbol "or" , S.Boolean True, S.Integer 10]) 
    --     (Just $ S.Boolean True)

    -- test "Or runSExpression Test 2" (runSExpression $ S.List [
    --     S.Symbol "or" , S.Boolean False, S.List [S.Symbol "let", S.List [S.Symbol "x",
    --       S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
    --     (Just $ S.Boolean False)    

    -- test "Or runSExpression Test 3" (runSExpression $ S.List [
    --     S.Symbol "or" , S.List [S.Symbol "or" , S.Integer 10, S.Real 15.1], 
    --      S.List [S.Symbol "let", S.List [S.Symbol "x",
    --       S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
    --     (Nothing)    

    -- test "Or runSExpression Test 4" (runSExpression $ S.List [
    --     S.Symbol "or" , S.Boolean True, S.Boolean False]) 
    --     (Just $ S.Boolean True)

    -- test "Or runSExpression Test 5" (runSExpression $ S.List [
    --     S.Symbol "or" , S.Boolean False, S.Boolean False]) 
    --     (Just $ S.Boolean False)

    -- -- Not tests
    -- test "Not runSExpression Test 1" (runSExpression $ S.List [
    --     S.Symbol "not" , S.Boolean True]) 
    --     (Just $ S.Boolean False)

    -- test "Not fromSExpression Test 2" (runSExpression $ S.List [
    --     S.Symbol "not" , S.List [S.Symbol "let", S.List [S.Symbol "x",
    --       S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
    --     (Nothing)      

    -- test "Not fromSExpression Test 3" (runSExpression $ S.List [
    --     S.Symbol "not" , S.List [S.Symbol "or" , S.Integer 10, 
    --      S.List [S.Symbol "let", S.List [S.Symbol "x",
    --       S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]]) 
    --     (Nothing)  

    -- test "Not runSExpression Test 4" (runSExpression $ S.List [
    --     S.Symbol "not" , S.Boolean False]) 
    --     (Just $ S.Boolean True)     

    -- -- //Less_Than tests 
    -- test "Less_Than runSExpression Test 1" (runSExpression $ S.List [
    --     S.Symbol "<", S.Boolean True, S.Integer 10]) 
    --     (Nothing)

    -- test "Less_Than runSExpression Test 2" (runSExpression $ S.List [
    --     S.Symbol "<", S.Integer 30, S.List [S.Symbol "let", S.List [S.Symbol "x",
    --       S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
    --     (Just $ S.Boolean False)    

    -- test "Less_Than runSExpression Test 3" (runSExpression $ S.List [
    --      S.Symbol "<", S.List [S.Symbol "let", S.List [S.Symbol "x",
    --       S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]], S.Integer 30]) 
    --     (Just $ S.Boolean True)      

    -- test "Less_Than runSExpression Test 4" (runSExpression $ S.List [
    --     S.Symbol "<", S.Real 15.1, S.Real 13.2]) 
    --     (Just $ S.Boolean False)

    -- test "Less_Than runSExpression Test 5" (runSExpression $ S.List [
    --     S.Symbol "<", S.Integer 5, S.Integer 6]) 
    --     (Just $ S.Boolean True)

    -- -- //Greater_Than tests 
    -- test "Greater_Than runSExpression Test 1" (runSExpression $ S.List [
    --     S.Symbol ">" , S.Boolean True, S.Integer 10]) 
    --     (Nothing)

    -- test "Greater_Than runSExpression Test 2" (runSExpression $ S.List [
    --     S.Symbol ">" , S.Integer 30, S.List [S.Symbol "let", S.List [S.Symbol "x",
    --       S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
    --     (Just $ S.Boolean True)    

    -- test "Greater_Than runSExpression Test 3" (runSExpression $ S.List [
    --      S.Symbol ">" , S.List [S.Symbol "let", S.List [S.Symbol "x",
    --       S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]], S.Integer 30]) 
    --     (Just $ S.Boolean False)      

    -- test "Greater_Than runSExpression Test 4" (runSExpression $ S.List [
    --     S.Symbol ">" , S.Real 15.1, S.Real 13.2]) 
    --     (Just $ S.Boolean True)

    -- test "Greater_Than runSExpression Test 5" (runSExpression $ S.List [
    --     S.Symbol ">" , S.Integer 5, S.Integer 6]) 
    --     (Just $ S.Boolean False)

    --  -- //Equal_To tests 
    -- test "Equal_To runSExpression Test 1" (runSExpression $ S.List [
    --     S.Symbol "=" , S.Boolean True, S.Integer 10]) 
    --     (Nothing)

    -- test "Equal_To runSExpression Test 2" (runSExpression $ S.List [
    --     S.Symbol "=" , S.Real 15.4, S.List [S.Symbol "let", S.List [S.Symbol "x",
    --       S.List [S.Symbol "+", S.Real 10.1, S.Real 4.2]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
    --     (Just $ S.Boolean True)    

    -- test "Equal_To runSExpression Test 3" (runSExpression $ S.List [
    --      S.Symbol "=" , S.List [S.Symbol "let", S.List [S.Symbol "x",
    --       S.List [S.Symbol "+", S.Real 10.0, S.Real 4.0]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.0]], S.Integer 15]) 
    --     (Just $ S.Boolean True)      

    -- test "Equal_To runSExpression Test 4" (runSExpression $ S.List [
    --     S.Symbol "=" , S.Integer 15, S.Integer 13]) 
    --     (Just $ S.Boolean False)

    -- test "Equal_To runSExpression Test 5" (runSExpression $ S.List [
    --     S.Symbol "=" , S.Integer 5, S.Integer 5]) 
    --     (Just $ S.Boolean True) 
    
    -- test "Equal_To runSExpression Test 6" (runSExpression $ S.List [
    --     S.Symbol "=" , S.Real 5.0, S.Integer 5]) 
    --     (Just $ S.Boolean True) 

    -- -- // Cond and Else tests
    -- test "Cond runSExpression Test 1" (runSExpression $ S.List[S.Symbol "cond", S.List[S.List[S.Boolean True, 
    --     S.List[S.Symbol "+", S.Integer 3, S.Integer 2]]], S.Symbol "Nothing"])
    --     (Just $ S.Integer 5)

    -- test "Cond runSExpression Test 2" (runSExpression $ S.List[S.Symbol "cond", S.List[S.List[S.Boolean False, 
    --     S.List[S.Symbol "-", S.Integer 3, S.Integer 2]], S.List[S.Boolean True, 
    --       S.List[S.Symbol "+", S.Integer 3, S.Integer 1]]], S.Symbol "Nothing"])
    --     (Just $ S.Integer 4)
        
    -- test "Cond runSExpression Test 3" (runSExpression $ S.List[S.Symbol "cond", S.List[S.List[S.Boolean False, 
    --     S.List[S.Symbol "-", S.Integer 3, S.Integer 2]], S.List[S.Boolean False, 
    --       S.List[S.Symbol "+", S.Integer 3, S.Integer 1]]],
    --        S.List[S.Symbol "/", S.Integer 3, S.Integer 1]])
    --     (Just $ S.Integer 3)

    -- test "Cond runSExpression Test 4" (runSExpression $ S.List[S.Symbol "cond", S.List[S.List[S.Boolean False, 
    --     S.List[S.Symbol "-", S.Integer 3, S.Integer 2]], S.List[S.Boolean True, 
    --       S.List[S.Symbol "+", S.Integer 3, S.Integer 1]]], S.List[S.Symbol "/", S.Integer 3, S.Integer 1]])
    --     (Just $ S.Integer 4)

    -- test "Cond runSExpression Test 5" (runSExpression $ S.List[S.Symbol "cond", S.List[S.List[S.Real 5.3, 
    --     S.List[S.Symbol "+", S.Integer 3, S.Integer 2]]], S.Symbol "Nothing"])
    --     (Nothing)

    -- test "Cond runSExpression Test 6" (runSExpression $ S.List[S.Symbol "cond", S.List[S.List[S.Integer 1, 
    --     S.List[S.Symbol "-", S.Integer 3, S.Integer 2]], S.List[S.Boolean False, 
    --       S.List[S.Symbol "+", S.Integer 3, S.Integer 1]]], S.List[S.Symbol "/", S.Integer 3, S.Integer 1]])
    --     (Nothing)
    
    -- -- // Complex Boolean tests
    -- test "Not runSExpression complex Test 1" (runSExpression $ S.List [
    --     S.Symbol "not" , S.List [S.Symbol "or", S.Boolean True, S.Boolean True]]) 
    --     (Just $ S.Boolean False)

    -- test "Not runSExpression complex Test 2" (runSExpression $ S.List [
    --     S.Symbol "not" , S.List [S.Symbol "and", S.Boolean True, S.Boolean True]]) 
    --     (Just $ S.Boolean False)

    -- test "Not runSExpression complex Test 3" (runSExpression $ S.List [
    --     S.Symbol "and" , S.List [S.Symbol "not", S.Boolean True], 
    --       S.List [S.Symbol "or", S.Boolean False, S.Boolean True]]) 
    --     (Just $ S.Boolean False) 

    --  -- // Pair Tests 

    -- test "Pair runSExpression Test 1" (runSExpression $ S.List [
    --    S.Symbol "pair", S.Integer 10, S.Real 11.1
    --  ]) (Just $ S.Dotted (S.Integer 10) (S.Real 11.1))  

    -- test "Pair runSExpression Test 2" (runSExpression $ S.List [
    --    S.Symbol "pair", S.List [S.Symbol "pair", S.Integer 15, S.Boolean True],
    --     S.Real 11.1]) 
    --     (Just $ S.Dotted (S.Dotted (S.Integer 15) (S.Boolean True)) (S.Real 11.1))   

    -- test "Pair runSExpression Test 3" (runSExpression $ S.List [
    --   S.Symbol "pair", S.List [S.Symbol "+", S.Boolean False, S.Boolean True],
    --   S.Integer 10]) (Nothing)

    -- -- // Left Tests 

    -- test "Left runSExpression Test 1" (runSExpression $ S.List [
    --   S.Symbol "left", S.Integer 10]) (Nothing)  

    -- test "Left runSExpression Test 2" (runSExpression $ S.List [
    --   S.Symbol "left", S.List [S.Symbol "pair", S.Real 5.5, S.Integer 10]]) 
    --    (Just (S.Real 5.5))    

    -- test "Left runSExpression Test 3" (runSExpression $ S.List [S.Symbol "left", 
    --   S.List [S.Symbol "left", S.List [
    --    S.Symbol "pair", S.List [S.Symbol "pair", S.Integer 15, S.Boolean True],
    --     S.Real 11.1]]])
    --     (Just $ S.Integer 15)   

    -- -- // Right Tests 

    -- test "Right runSExpression Test 1" (runSExpression $ S.List [
    --   S.Symbol "right", S.Integer 10]) (Nothing)  

    -- test "Right runSExpression Test 2" (runSExpression $ S.List [
    --   S.Symbol "right", S.List [S.Symbol "pair", S.Real 5.5, S.Integer 10]]) 
    --    (Just (S.Integer 10))    

    -- test "Right runSExpression Test 3" (runSExpression $ S.List [S.Symbol "right", 
    --   S.List [S.Symbol "right", S.List [
    --    S.Symbol "pair", S.Real 11.1 , 
    --     S.List [S.Symbol "pair", S.Integer 15, S.Boolean True]]]])
    --     (Just $ S.Boolean True)     

    -- --Real_Pred tests

    -- test "Real? runSExpression test  1" (runSExpression $ S.List[(S.Symbol "real?"), (S.Integer 1)]) (Just $ S.Boolean False)

    -- test "Real? runSExpression test 2" (runSExpression $ S.List[(S.Symbol "real?"), (S.Real 1.0)]) (Just $ S.Boolean True)
    
    -- test "Real? runSExpression test 3" (runSExpression $ S.List[(S.Symbol "real?"), (S.Boolean True)]) (Just $ S.Boolean False)
    
    -- test "Real? runSExpression test 4" (runSExpression $ S.List[(S.Symbol "real?"), (S.List[S.Symbol "right", 
    --  (S.List[S.Symbol "pair", (S.List[S.Symbol "+", (S.Integer 2), (S.Integer 1)]), (S.Integer 4)])])])
    --  (Just $ S.Boolean False)
    
    --  --Integer_Pred tests

    -- test "Integer? runSExpression test 1" (runSExpression $ S.List[(S.Symbol "integer?"), (S.Integer 1)]) (Just $ S.Boolean True)

    -- test "Integer? runSExpression test 2" (runSExpression $ S.List[(S.Symbol "integer?"), (S.Real 1.0)]) (Just $ S.Boolean False)
    
    -- test "Integer? runSExpression test 3" (runSExpression $ S.List[(S.Symbol "integer?"), (S.Boolean True)]) (Just $ S.Boolean False)
    
    -- test "Integer? runSExpression test 4" (runSExpression $ S.List[(S.Symbol "integer?"), (S.List[S.Symbol "right", 
    --  (S.List[S.Symbol "pair", (S.List[S.Symbol "+", (S.Integer 2), (S.Integer 1)]), (S.Integer 4)])])])
    --  (Just $ S.Boolean True)

    -- --Number_Pred tests

    -- test "Number? runSExpression test 1" (runSExpression $ S.List[(S.Symbol "number?"), (S.Integer 1)]) (Just $ S.Boolean True)

    -- test "Number? runSExpression test 2" (runSExpression $ S.List[(S.Symbol "number?"), (S.Real 1.0)]) (Just $ S.Boolean True)
    
    -- test "Number? runSExpression test 3" (runSExpression $ S.List[(S.Symbol "number?"), (S.Boolean True)]) (Just $ S.Boolean False)
    
    -- test "Number? runSExpression test 4" (runSExpression $ S.List[(S.Symbol "number?"), (S.List[S.Symbol "right", 
    --  (S.List[S.Symbol "pair", (S.List[S.Symbol "+", (S.Integer 2), (S.Integer 1)]), (S.Integer 4)])])])
    --  (Just $ S.Boolean True)

    -- --Boolean_Pred tests

    -- test "Boolean? runSExpression test 1" (runSExpression $ S.List[(S.Symbol "boolean?"), (S.Integer 1)]) (Just $ S.Boolean False)

    -- test "Boolean? runSExpression test 2" (runSExpression $ S.List[(S.Symbol "boolean?"), (S.Real 1.0)]) (Just $ S.Boolean False)
    
    -- test "Boolean? runSExpression test 3" (runSExpression $ S.List[(S.Symbol "boolean?"), (S.Boolean True)]) (Just $ S.Boolean True) 
    
    -- test "Boolean? runSExpression test 4" (runSExpression $ S.List[(S.Symbol "boolean?"), (S.List[S.Symbol "right", 
    --  (S.List[S.Symbol "pair", (S.List[S.Symbol "+", (S.Integer 2), (S.Integer 1)]), (S.Integer 4)])])])
    --  (Just $ S.Boolean False)

    -- --Pair_Pred tests

    -- test "Pair? runSExpression test 1" (runSExpression $ S.List[(S.Symbol "pair?"), (S.Integer 1)]) (Just $ S.Boolean False)

    -- test "Pair? runSExpression test 2" (runSExpression $ S.List[(S.Symbol "pair?"), (S.Real 1.0)]) (Just $ S.Boolean False)
    
    -- test "Pair? runSExpression test 3" (runSExpression $ S.List[(S.Symbol "pair?"), (S.Boolean True)]) (Just $ S.Boolean False)
    
    -- test "Pair? runSExpression test 4" (runSExpression $ S.List[(S.Symbol "pair?"), (S.List[S.Symbol "right", 
    --  (S.List[S.Symbol "pair", (S.List[S.Symbol "+", (S.Integer 2), (S.Integer 1)]), (S.Integer 4)])])])
    --  (Just $ S.Boolean False)

    -- test "Pair? runSExpression test 5" (runSExpression $ S.List[S.Symbol "pair?", S.List[S.Symbol "pair", (S.Integer 1), (S.Integer 2)]])
    --  (Just $ S.Boolean True)    

    -- -- Program tests 
    -- test "Program runSExpression test 1 one defun" (runSExpression $ S.List[S.Symbol "Program", S.List [S.List[S.Symbol "Defun", S.Symbol "incr", S.List [S.Symbol "x"], 
    --  S.List[S.Symbol "+", S.Symbol "x", S.Integer 1]]], S.List[S.Symbol "call", S.Symbol "incr", 
    --  S.List [S.List [S.Symbol "call", S.Symbol "incr", S.List [S.List [S.Symbol "call", S.Symbol "incr", S.List [S.Integer 1]]]]]]]) 
    --  (Just $ S.Integer 4)

    -- test "Program runSExpression test 2 one defun " (runSExpression sexpr_ex1) (Just $ S.Integer 4) 

    -- test "Program runSExpression test 3 two defuns" (runSExpression sexpr_ex1B) (Just $ S.Integer 6) 

    -- test "Program runSExpression test 4 one defun with Let " (runSExpression sexpr_ex3) (Just $ S.Integer 21) 

    -- test "Program runSExpression test 5 one define" (runSExpression sexpr_ex4) (Just $ S.Integer 9) 

    -- test "Program runSExpression test 6 two defines" (runSExpression sexpr_ex5) (Just $ S.Dotted (S.Integer 20) (S.Integer 4)) 

    -- test "Program runSExpression test 7 define with diff types" (runSExpression sexpr_ex7) (Just $ S.Boolean False)
