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

import qualified Parser as P

import Prelude hiding (Left, Right)

import qualified SExpression as S

import Maps (get, set, empty)

import SimpleTestsColor (test)

import qualified Result as R

import System.IO.Unsafe (unsafePerformIO)

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
  
--Example of Program
-- deleted old program tests now that runProgram exists on the bottom and calls on evalProgram with complicated programs. 

-- fail test
ex_program1 = Program [Define "incr" (App [(Var "+"), (Var "x"), (Val (Integer 1))])] (App [Var "incr", (Val (Integer 3))])

ex_program1pass = Program [Define "incr" (Lambda ["x"] (App [(Var "+"), (Var "x"), (Val (Integer 1))]))] (App [Var "incr", (Val (Integer 3))])

--  ================================================================================================                                                                                                    

-- Function that takes in a Program and evaluates the program to get a resulting Maybe ExprEval
evalProgram :: Program -> R.Result Value
evalProgram (Program globalDefs e) = do 
    case globals of 
        R.Success globals' -> eval globals' empty e
        R.Failure f -> fail f
  where 
    globals = collectDefs (reverse globalDefs)
    collectDefs :: [GlobalDef] -> R.Result Env
    collectDefs [] = return builtins
    collectDefs (Define v e : globalDefs) = 
        case eval builtins empty e of 
            R.Success e' ->  do 
                case collectDefs globalDefs of 
                    R.Success defs -> return (set defs v e')
                    R.Failure f -> fail f
            R.Failure f -> fail f 

--tests of the evalProgram function
test_evalProgram = do 
    
    test "evalProgram empty globalDefs and simple expression" (evalProgram $ Program [] (Val (Integer 10)))
     (R.Success (Integer 10))

    test "evalProgram single variable globalDefs and simple expression" (evalProgram $ Program 
     [Define "x" (Val (Integer 10))] (Var "x"))
     (R.Success (Integer 10))  

    test "evalProgram multiple variable globalDefs and simple expression" (evalProgram $ Program 
     [Define "x" (Val (Integer 10)), Define "y" (Val (Integer 20))] (App [(Var "+"), (Var "y"), (Var "x")]))
     (R.Success (Integer 30))  

    test "evalProgram multiple of same variable globalDefs and simple expression" (evalProgram $ Program 
     [Define "x" (Val (Integer 10)), Define "x" (Val (Integer 20))] (App [Var "+", (Var "x"), (Var "x")]))
     (R.Success (Integer 40))      

    test "evalProgram single function and simple expression 1" (evalProgram ex_program1)  
     (fail "Variable x not defined.")

    test "evalProgram single function and simple expression 2" (evalProgram ex_program1pass)  
     (R.Success (Integer 4)) 
   
 -- ===============================================================================================

-- |Evaluates the given expression to a value.
eval :: Env -> Env -> Expr -> R.Result Value
eval g m (Val (Integer i)) = return (Integer i)
eval g m (Val (Float d)) = return (Float d)
eval g m (Val (Boolean b)) = return (Boolean b)
--Handles and expressions, evaluates first, if True, check second
--if either is false, returns false. Fails if either arg is not a Boolean.
eval g m (And e1 e2) = do 
    v1 <- eval g m e1 
    case v1 of 
        Boolean True -> do 
            v2 <- eval g m e2 
            case v2 of 
                Boolean b -> return (Boolean b)
                _ -> fail "And not passed a boolean for second argument."
        Boolean False -> return (Boolean False)
        _ -> fail "And not passed a boolean for first argument."
--Handles or expressions, evaluates first, if True returns True
--else return value of second. Fails if either arg is not a Boolean.
eval g m (Or e1 e2) = do 
    v1 <- eval g m e1 
    case v1 of 
        Boolean True -> return (Boolean True) 
        Boolean False -> do 
            v2 <- eval g m e2 
            case v2 of 
                Boolean b -> return (Boolean b)
                _ -> fail "Or not passed a boolean for second argument."
        _ -> fail "Or not passed a boolean for first argument."    
--Gets values of defined variables. Fails if undefined.    
eval g m (Var x) =
    case get m x of
         Just v -> return v
         _ -> case get g x of 
                   Just v -> return v
                   _ -> fail $ "Variable " ++ x ++ " not defined."    
--Returns value of Lambda expression by turning it into Value type Closure 
eval g m (Lambda x e) = return $ Closure x e m    
--Evaluates a function call applied to its given arguments and fails
--if the arguments are inappropriate or no function is present
eval g m (App (x:xs)) = do 
    v <- eval g m x
    case v of 
        Closure vars e m' -> callLambda vars xs e g m'
        PrimOp op [] -> callOp op xs []
        _ -> fail "App called without a Closure as the first argument." 
        where 
            callLambda :: [Variable] -> [Expr] -> Expr -> Env -> Env -> R.Result Value
            callLambda [] [] e g m' = eval g m' e 
            callLambda [] _ _ _ _  = fail $ "Lambda call received too many arguments."
            callLambda _ [] _ _ _ = fail $ "Lambda call did not receive enough arguments."
            callLambda (x:xs) (y:ys) e g m' = do 
                y' <- eval g m y
                callLambda xs ys e g (set m' x y')
            callOp :: Op -> [Expr] -> [Value] -> R.Result Value 
            callOp op [] vals = apply op vals 
            callOp op (x:xs) vals = do 
                x' <- eval g m x 
                callOp op xs (vals ++ [x'])
--Sets the given variable to its corresponding value
--in the given environment and evaluates
eval g m (Let x e1 e2) = do
     v1 <- eval g m e1
     eval g (set m x v1) e2  
--Returns evaluated e2 if e1 represents True, e3 if e1 represents False     
--Fails if e1 is not a Boolean        
eval g m (If e1 e2 e3) = do
      b <- eval g m e1
      case b of 
          Boolean b' -> do 
              if b' then eval g m e2
                    else eval g m e3
          _ -> fail "If not passed a boolean for first expression."          
eval g m (Cond x y) = evalTupleListHelper g m x y 
--Returns a Pair with two evaluated Expressions (Results) stored in it
eval g m (Pair e1 e2) = do 
    v1 <- eval g m e1
    v2 <- eval g m e2 
    return (PairVal v1 v2)   
--Returns the left element of a pair
--Fails if a pair is not given          
eval g m (Left l ) = do 
    v <- eval g m l 
    case v of 
        PairVal left right -> do 
            return left
        _ -> fail $ "Left not applied to pair."  
--Returns the right element of a pair
--Fails if a pair is not given      
eval g m (Right l ) = do
    v <- eval g m l 
    case v of 
        PairVal left right -> do 
            return right
        _ -> fail $ "Right not applied to pair."  
--If the argument is a Float returns true, otherwise false           
eval g m (Real_Pred e) = do 
    v <- eval g m e 
    case v of 
        (Float _) -> return (Boolean True)
        _ -> return (Boolean False)  
--If the argument is an Integer returns true, otherwise false                           
eval g m (Integer_Pred e) = do 
    v <- eval g m e 
    case v of 
        (Integer _) -> return (Boolean True)
        _ -> return (Boolean False)
--If the argument is a Float or an Integer returns true, otherwise false   
eval g m (Number_Pred e) = do 
    v <- eval g m e 
    case v of 
        (Float _) -> return (Boolean True)
        (Integer _) -> return (Boolean True)
        _ -> return (Boolean False)  
--If the argument is a Boolean returns true, otherwise false                       
eval g m (Boolean_Pred e) = do 
    v <- eval g m e 
    case v of 
        (Boolean _ ) -> return (Boolean True)
        _ -> return(Boolean False)    
--If the argument is a PairVal returns true, otherwise false                                         
eval g m (Pair_Pred e) = do 
    v <- eval g m e 
    case v of 
        (PairVal _ _) -> return (Boolean True)
        _ -> return (Boolean False)                                                                                                                 

-- Helper function for eval that handles a cond list by identifying the inputs using pattern matching
--and follows the cond branch that has a corresponding true value 
evalTupleListHelper :: Env -> Env -> [(Expr, Expr)] -> Maybe Expr -> R.Result Value
evalTupleListHelper _ _ [] Nothing = fail $ "Cond ended without a returned expression." 
evalTupleListHelper g m [] (Just e) = eval g m e 
evalTupleListHelper g m ((t1, t2):xs) y = do 
    v <- eval g m t1 
    case v of 
        (Boolean True) -> eval g m t2
        (Boolean False) -> evalTupleListHelper g m xs y 
        _ -> fail $ "Cond clause was not a boolean."


-- Tests of the Eval and the evalTupleListHelper
test_evalTupleListHelper = do 

    test "evalTupleListHelper basic test" (evalTupleListHelper empty empty [] Nothing ) (fail $ "Cond ended without a returned expression.") 

    test "evalTupleListHelper else case basic " (evalTupleListHelper empty empty [] (Just (Val (Integer 5)))) (R.Success (Integer 5))

    test "evalTupleListHelper else case complex 1" (evalTupleListHelper empty empty 
     [((Val (Boolean False)), (Val (Float 5.5)))] (Just (Val (Integer 5)))) (R.Success (Integer 5))

    test "evalTupleListHelper else case complex 2" (evalTupleListHelper empty empty 
     [((Val (Boolean True)), (Val (Float 5.5)))] (Just (Val (Integer 5)))) (R.Success (Float 5.5))

    test "evalTupleListHelper no else complex 1" (evalTupleListHelper empty empty 
     [((Val (Boolean False)), (Val (Float 5.5))), ((Val (Boolean False)), (Val (Integer 5)))] Nothing) (fail $ "Cond ended without a returned expression.")

    test "evalTupleListHelper no else complex 2" (evalTupleListHelper empty empty 
     [((Val (Boolean True)), (Val (Float 5.5))), ((Val (Boolean False)), (Val (Integer 5)))] Nothing) (R.Success (Float 5.5))

    test "evalTupleListHelper no else complex 3" (evalTupleListHelper builtins empty 
     [((Val (Boolean False)), (Val (Float 5.5))), ((And (Val (Boolean True)) (App [Var "<", (Val (Integer 1)), (Val (Integer 2))])), 
     (Val (Integer 5)))] Nothing) (R.Success (Integer 5))


                         
test_eval = do
    -- // Boolean Tests
    test "eval Boolean  True" (eval empty empty (Val (Boolean True))) (R.Success (Boolean True))

    test "eval Boolean False" (eval empty empty (Val (Boolean False))) (R.Success (Boolean False))
    
    test "eval Boolean: (+ True 30)" (eval empty builtins (App [Var "+", Val (Boolean True) , Val (Integer 30)])) 
     (fail "Wrong number or type of arguments for +.")

    test "eval Boolean: (let (x (+ 1 False)) (* 4 x))"
       (eval empty builtins ( Let "x" (App [Var "+", Val (Integer 1), Val (Boolean False)]) 
       (App [Var "*", Val (Integer 4), Var "x"])))
       (fail "Wrong number or type of arguments for +.")

    test "eval Boolean: (- 30 False)" (eval empty builtins ( App [Var "-", Val (Integer 30), Val (Boolean False)])) 
     (fail "Wrong number or type of arguments for -.")

    test "eval Boolean: (* True 12)" (eval empty builtins ( App [Var "*", Val (Boolean True), Val (Integer 12)]))
     (fail "Wrong number or type of arguments for *.")
  
    test "eval Boolean: (/ False 12)" (eval empty builtins (App [Var "/", Val (Boolean False), Val (Integer 12)]))
     (fail "Wrong number or type of arguments for /.")

    test "eval Boolean: (* (+ 5 10) (- 5 True))" (eval empty builtins ( App [Var "*", 
     App [Var "*", Val (Integer 5), Val (Integer 10)], 
      App [Var "-", Val (Integer 5), Val (Boolean True)]])) (fail "Wrong number or type of arguments for -.")

    test "eval Boolean: nested let" (eval empty builtins ( Let "y" (App [Var "-",  Val (Integer 20), Val (Integer 8)])
     (Let "x" (App [Var "+", Var "y", Val (Integer 4)]) (App [Var "+", Var "x", Val (Boolean False)])))) 
      (fail "Wrong number or type of arguments for +.")


    -- // Integer tests
    test "eval Integer: (+ 12 30)" (eval empty builtins (App [Var "+", Val (Integer 12), Val (Integer 30)])) 
     (R.Success (Integer 42))

    test "eval Integer: (let (x (+1 2)) (* 4 x))"
       (eval empty builtins ( Let "x" (App [Var "+", Val (Integer 1), Val (Integer 2)]) (App [Var "*", Val (Integer 4), Var "x"])))
       (R.Success (Integer 12))

    test "eval Integer not assigned Var Test 1" (eval empty builtins (Var "x")) 
     (fail "Variable x not defined.")

    test "eval Integer not assigned Var Test 2" (eval empty builtins (App [Var "+", Val (Integer 2), Var "x"])) 
     (fail "Variable x not defined.")

    test "eval Integer: simple Integer test" (eval empty builtins (Val (Integer 11))) (R.Success (Integer 11))

    test "eval Integer: (- 30 12)" (eval empty builtins (App [Var "-", Val (Integer 30), Val (Integer 12)])) (R.Success (Integer 18))

    test "eval Integer: (* 30 12)" (eval empty builtins (App [Var "*", Val (Integer 30), Val (Integer 12)])) (R.Success (Integer 360))
  
    test "eval Integer: (/ 30 12)" (eval empty builtins (App [Var "/", Val (Integer 30), Val (Integer 12)])) (R.Success (Integer 2))

    test "eval Integer: (* (+ 5 10) (- 5 4))" (eval empty builtins (App [Var "*", 
     App [Var "+", Val (Integer 5), Val (Integer 10)],
     App [Var "-", Val (Integer 5), Val (Integer 4)]])) (R.Success (Integer 15))

    test "eval Integer: nested let" (eval empty builtins ( Let "y" (App [Var "-", Val (Integer 20), Val (Integer 8)])
     (Let "x" (App [Var "+", Var "y", Val (Integer 4)]) (App [Var "+", Var "x", Val (Integer 1)])))) 
      (R.Success (Integer 17))

    -- -- // Float tests 

    test "eval Float: (+ 12.2 30.5)" True (checkFloatEquality (eval empty builtins (App [Var "+", Val (Float 12.2), Val (Float 30.5)])) 
     (R.Success (Float 42.7)))

    test "eval Float: (let (x (+1.1 2.2)) (* 4.5 x))"
       True 
       (checkFloatEquality(eval empty builtins ( Let "x" (App [Var "+", Val (Float 1.1) , Val (Float 2.2)]) 
        (App [Var "*", Val (Float 4.5), Var "x"]))) (R.Success (Float 14.85)))

    test "eval Float not assigned Var Test" (eval empty builtins (App [Var "+", Val (Float 2.5), Var "x"])) (fail "Variable x not defined.")
   
    test "eval Float: simple Integer test" True (checkFloatEquality (eval empty builtins (Val (Float 11.1))) (R.Success (Float 11.1)))

    test "eval Float: (- 30.5 12.5)" True (checkFloatEquality (eval empty builtins (App [Var "-", Val (Float 30.5), Val (Float 12.5)])) 
     (R.Success (Float 18.0)))

    test "eval Float: (* 30.5 12.1)" True (checkFloatEquality (eval empty builtins (App [Var "*", Val (Float 30.5), Val (Float 12.1)])) 
     (R.Success (Float 369.05)))

    test "eval Float: (/ 30.0 12.0)" True (checkFloatEquality (eval empty builtins (App [Var "/", Val (Float 30.0), Val (Float 12.0)])) 
     (R.Success (Float 2.5)))

    test "eval Float: (* (+ 5.5 10.5) (- 5.4 4.4))" True (checkFloatEquality (eval empty builtins 
     ( App [Var "*",  App [Var "+", Val (Float 5.5), Val (Float 10.5)], 
                      App [Var "-", Val (Float 5.4), Val (Float 4.4)]])) (R.Success (Float 16.0)))

    test "eval Float: nested let" True (checkFloatEquality (eval empty builtins ( Let "y" 
     (App [Var "-", Val (Float 20.2), Val (Float 8.4)])
      (Let "x" (App [Var "+", Var "y", Val (Float 4.4)]) 
       (App [Var "+", Var "x", Val (Float 1.1)])))) (R.Success (Float 17.3)))

    -- // Mixed tests 

    test "eval Mixed: (+ 12.2 30)" True (checkFloatEquality (eval empty builtins 
     (App [Var "+", Val (Float 12.2) , Val (Integer 30)])) (R.Success (Float 42.2)))

    test "eval Mixed: (let (x (+1.1 20)) (* 4 x))" True
       (checkFloatEquality (eval empty builtins ( Let "x" (App [Var "+", Val (Float 1.1), Val (Integer 20)]) 
        (App [Var "*", Val (Integer 4), Var "x"])))
       (R.Success (Float 84.4)))

    test "eval Mixed: (- 30.5 12)" True (checkFloatEquality (eval empty builtins 
     ( App [Var "-", Val (Float 30.5), Val (Integer 12)])) 
     (R.Success (Float 18.5)))

    test "eval Mixed: (* 30.5 12)" True (checkFloatEquality (eval empty builtins 
     ( App [Var "*", Val (Float 30.5), Val (Integer 12)])) 
     (R.Success (Float 366.0)))

    test "eval Mixed: (/ 32.5 10)" True (checkFloatEquality (eval empty builtins 
     (App [Var "/", Val (Float 32.5), Val (Float 10)])) (R.Success (Float 3.25)))

    test "eval Mixed: (* (+ 5.5 10) (- 5.4 4))" True (checkFloatEquality (eval empty builtins 
     (App [Var "*", App [Var "+", Val (Float 5.5), Val (Integer 10)],
                    App [Var "-", Val (Integer 5), Val (Float 4.4)]])) (R.Success (Float 9.299999999999994)))

    test "eval Mixed: nested let" True (checkFloatEquality (eval empty builtins 
     (Let "y" (App [Var "-", Val (Float 20.2), Val (Integer 8)])
      (Let "x" (App [Var "+", Var "y", Val (Integer 4)]) (App [Var "+", Var "x", Val (Float 1.1)])))) (R.Success (Float 17.3)))


    -- // If tests 

    test "eval If: e1 is True Simple" (eval empty builtins (If (Val (Boolean True)) (Val (Integer 10)) (Val (Float 15.1))))  
      (R.Success $ Integer 10)  

    test "eval If: e1 is False Simple" True (checkFloatEquality (eval empty builtins 
     (If (Val (Boolean False)) (Val (Integer 10)) (Val (Float 15.1))))  
      (R.Success $ Float 15.1))

    test "eval If: e1 is True Complex" True (checkFloatEquality (eval empty builtins (If (Val (Boolean True)) 
     (App [Var "+", Val (Integer 10), Val (Float 9.5)]) (Val (Float 15.1))))
      (R.Success $ Float 19.5))

    test "eval If: e1 is False Complex" True (checkFloatEquality (eval empty builtins (If (Val (Boolean False)) (Val (Float 15.1)) 
     (App [Var "-", Val (Integer 10), Val (Float 9.5)])))
      (R.Success $ Float 0.5))

    test "eval If: e1 is not a boolean" (eval empty builtins (If (App [Var "/", Val (Integer 5), Val (Float 5.1)]) 
     (Val (Boolean False)) (Val (Boolean True))))
        (fail "If not passed a boolean for first expression.")       

  -- // And tests 

    test "eval And: e1 not a boolean simple" (eval empty empty (And (Val (Integer 10)) (Val (Boolean False)))) (fail "And not passed a boolean for first argument.")    

    test "eval And: e1 not a boolean complex" (eval empty empty (And (If (Val (Boolean False)) (Val (Float 5.5)) 
      (App [Var "+", Val (Boolean True), Val (Integer 10)])) (Val (Boolean True)))) (fail "Variable + not defined.")  

    test "eval And: e1 is False simple" (eval empty empty (And (Val (Boolean False)) (Val (Integer 3)))) (R.Success (Boolean False))  

    test "eval And: e1 is False complex" (eval empty empty (And (If (Val (Boolean False)) (Val (Float 5.5)) (Val (Boolean False))) 
      (Val (Float 3.5)))) (R.Success (Boolean False))

    test "eval And: e1 is True, e2 is True simple" (eval empty empty (And (Val (Boolean True)) (Val (Boolean True)))) (R.Success (Boolean True))

    test "eval And: e1 is True, e2 is True complex"  (eval empty empty (And (If (And (Val (Boolean True)) (Val (Boolean True))) (Val (Boolean True)) (Val (Boolean False))) 
      (If (And (Val (Boolean True)) (Val (Boolean False))) (Val (Boolean False)) (Val (Boolean True))))) (R.Success (Boolean True))

    test "eval And: e1 is True, e2 is False simple"  (eval empty empty (And (Val (Boolean True)) (Val (Boolean False)))) (R.Success (Boolean False)) 

    test "eval And: e1 is True, e2 is False complex"  (eval empty empty (And (If (And (Val (Boolean True)) (Val (Boolean True))) (Val (Boolean True)) (Val (Boolean False))) 
      (If (And (Val (Boolean True)) (Val (Boolean False))) (Val (Boolean True)) (Val (Boolean False))))) (R.Success (Boolean False))

    test "eval And: e1 is True, e2 is not a boolean simple" (eval empty empty (And (Val (Boolean True)) (Val (Integer 10)))) (fail "And not passed a boolean for second argument.")  

    -- // Or tests 

    test "eval Or: e1 not a boolean, e2 is True simple" (eval empty empty (Or (Val (Integer 10)) (Val (Boolean True)))) (fail "Or not passed a boolean for first argument.")  

    test "eval Or: e1 not a boolean, e2 is False simple" (eval empty empty (Or (Val (Integer 10)) (Val (Boolean False)))) (fail "Or not passed a boolean for first argument.")
    
    test "eval Or: e1 not a boolean, e2 is not a boolean simple" (eval empty empty (Or (Val (Integer 10)) (Val (Float 15.2)))) (fail "Or not passed a boolean for first argument.") 

    test "eval Or: e1 is True, e2 is True simple" (eval empty empty (Or (Val (Boolean True)) (Val (Boolean True)))) (R.Success (Boolean True))
    
    test "eval Or: e1 is True, e2 is False simple" (eval empty empty (Or (Val (Boolean True)) (Val (Boolean False)))) (R.Success (Boolean True))

    test "eval Or: e1 is True, e2 is not a boolean simple" (eval empty empty (Or (Val (Boolean True)) (Val (Integer 15)))) (R.Success (Boolean True))

    test "eval Or: e1 is False, e2 is True simple" (eval empty empty (Or (Val (Boolean False)) (Val (Boolean True)))) (R.Success (Boolean True))
    
    test "eval Or: e1 is False, e2 is False simple" (eval empty empty (Or (Val (Boolean False)) (Val (Boolean False)))) (R.Success (Boolean False))

    test "eval Or: e1 is False, e2 is not a boolean simple" (eval empty empty (Or (Val (Boolean False)) (Val (Integer 15)))) (fail "Or not passed a boolean for second argument.")
      
    -- -- // Not tests 
    
    test "eval Not: e1 True" (eval empty builtins (App [Var "not", Val (Boolean True)])) (R.Success (Boolean False)) 

    test "eval Not: e1 False" (eval empty builtins (App [Var "not", Val (Boolean False)])) (R.Success (Boolean True)) 
    
    test "eval Not: e1 boolean complex" (eval empty builtins (App [Var "not", Or (Val (Boolean False)) (Val (Boolean True))]))
      (R.Success (Boolean False)) 

    test "eval Not: e1 not boolean" (eval empty builtins (App [Var "not", Val (Integer 10)])) 
     (fail "Wrong number or type of arguments for not.")
    
    test "eval Not: e1 not boolean complex" (eval empty builtins (App [Var "not", App [Var "+", Val (Integer 5), Val (Integer 10)]]))
      (fail "Wrong number or type of arguments for not.")      
    
    -- -- // Less_Than Tests 
   
    test "eval Less_Than: eval e1 is Integer and eval e2 is Integer greater than e1 simple" 
     (eval empty builtins (App [Var "<", Val (Integer 5), Val (Integer 10)])) (R.Success (Boolean True))  
     
    test "eval Less_Than: eval e1 is Integer and eval e2 is Integer less than e1 simple" 
     (eval empty builtins (App [Var "<", Val (Integer 10), Val (Integer 5)])) (R.Success (Boolean False))    
     
    test "eval Less_Than: eval e1 is Integer and eval e2 is Float greater than e1 simple" 
     (eval empty builtins (App [Var "<", Val (Integer 5), Val (Float 10)])) (R.Success (Boolean True))  
     
    test "eval Less_Than: eval e1 is Integer and eval e2 is Float less than e1 simple" 
     (eval empty builtins (App [Var "<", Val (Integer 10), Val (Float 5)])) (R.Success (Boolean False))     

    test "eval Less_Than: eval e1 is Integer and eval e2 not a numeric type simple" 
     (eval empty builtins (App [Var "<", Val (Integer 5), Val (Boolean True)])) (fail "Wrong number or type of arguments for <.")   

    test "eval Less_Than: eval e1 is Integer and eval e2 is Integer greater than e1 complex" 
     (eval empty builtins (App [Var "<", App [Var "-", Val (Integer 5), Val (Integer  7)], 
                                      App [Var "+", Val (Integer 10), Val (Integer 20)]])) 
                                    (R.Success (Boolean True)) 

    test "eval Less_Than: eval e1 is Integer and eval e2 is Integer less than e1 complex" 
     (eval empty builtins (App [Var "<", App [Var "+", Val (Integer 10), Val (Integer  20)], 
                                      App [Var "-", Val (Integer 5), Val (Integer 7)]])) 
                                    (R.Success (Boolean False))                   

    test "eval Less_Than: eval e1 is Integer and eval e2 is Float greater than e1 complex" 
     (eval empty builtins (App [Var "<", App [Var "+", Val (Integer 10), Val (Integer  20)], 
                                      App [Var "-", Val (Integer 50), Val (Float 7)]])) 
                                    (R.Success (Boolean True))   

    test "eval Less_Than: eval e1 is Integer and eval e2 is Float less than e1 complex" 
     (eval empty builtins (App [Var "<", App [Var "+", Val (Integer 10), Val (Integer  20)], 
                                      App [Var "-", Val (Integer 10), Val (Float 7)]])) 
                                    (R.Success (Boolean False))     

    test "eval Less_Than: eval e1 is Integer and eval e2 is not a numeric type complex" 
     (eval empty builtins (App [Var "<", App [Var "+", Val (Integer 10), Val (Integer  20)], 
                                      And (Val (Boolean True)) (Val (Boolean False))])) 
                                    (fail "Wrong number or type of arguments for <.")                                                                                                                                   
      
    test "eval Less_Than: eval e1 is Float and eval e2 is Integer greater than e1 simple" 
     (eval empty builtins (App [Var "<", Val (Float 5), Val (Integer 10)])) (R.Success (Boolean True))  
     
    test "eval Less_Than: eval e1 is Float and eval e2 is Integer less than e1 simple" 
     (eval empty builtins (App [Var "<", Val (Float 10), Val (Integer 5)])) (R.Success (Boolean False))    
     
    test "eval Less_Than: eval e1 is Float and eval e2 is Float greater than e1 simple" 
     (eval empty builtins (App [Var "<", Val (Float 5), Val (Float 10)])) (R.Success (Boolean True))  
     
    test "eval Less_Than: eval e1 is Float and eval e2 is Float less than e1 simple" 
     (eval empty builtins (App [Var "<", Val (Float 10), Val (Float 5)])) (R.Success (Boolean False))     

    test "eval Less_Than: eval e1 is Float and eval e2 not a numeric type simple" 
     (eval empty builtins (App [Var "<", Val (Float 5), Val (Boolean True)])) (fail "Wrong number or type of arguments for <.")    

    test "eval Less_Than: eval e1 is Float and eval e2 is Integer greater than e1 complex" 
     (eval empty builtins (App [Var "<", App [Var "-", Val (Float 5), Val (Integer  7)], 
                                      App [Var "+", Val (Integer 10), Val (Integer 20)]])) 
                                    (R.Success (Boolean True)) 

    test "eval Less_Than: eval e1 is Float and eval e2 is Integer less than e1 complex" 
     (eval empty builtins (App [Var "<", App [Var "+", Val (Float 10), Val (Integer  20)], 
                                      App [Var "-", Val (Integer 5), Val (Integer 7)]])) 
                                    (R.Success (Boolean False))                   

    test "eval Less_Than: eval e1 is Float and eval e2 is Float greater than e1 complex" 
     (eval empty builtins (App [Var "<", App [Var "+", Val (Float 10), Val (Integer  20)], 
                                      App [Var "-", Val (Integer 50), Val (Float 7)]])) 
                                    (R.Success (Boolean True))   

    test "eval Less_Than: eval e1 is Float and eval e2 is Float less than e1 complex" 
     (eval empty builtins (App [Var "<", App [Var "+", Val (Float 10), Val (Integer  20)], 
                                      App [Var "-", Val (Integer 10), Val (Float 7)]])) 
                                    (R.Success (Boolean False))     

    test "eval Less_Than: eval e1 is Float and eval e2 is not a numeric type complex" 
     (eval empty builtins (App [Var "<", App [Var "+", Val (Float 10), Val (Integer  20)], 
                                      (And (Val (Boolean True)) (Val (Boolean False)))])) 
                                    (fail "Wrong number or type of arguments for <.")                                      

    test "eval Less_Than: eval e1 is not numeric" 
     (eval empty builtins (App [Var "<", Val (Boolean True), Val (Integer 10)])) (fail "Wrong number or type of arguments for <.") 

    test "eval Less_Than: eval e1 and eval e2 equal ints should be false" 
     (eval empty builtins (App [Var "<", Val (Integer 10), Val (Integer 10)])) (R.Success (Boolean False))

    test "eval Less_Than: eval e1 and eval e2 equal floats should be false" 
     (eval empty builtins (App [Var "<" , Val (Float 10), Val (Float 10)])) (R.Success (Boolean False))  


    -- -- // Greater_Than Tests 
   
    test "eval Greater_Than: eval e1 is Integer and eval e2 is Integer greater than e1 simple" 
     (eval empty builtins (App [Var ">", Val (Integer 5), Val (Integer 10)])) (R.Success (Boolean False))  
     
    test "eval Greater_Than: eval e1 is Integer and eval e2 is Integer less than e1 simple" 
     (eval empty builtins (App [Var ">", Val (Integer 10), Val (Integer 5)])) (R.Success (Boolean True))    
     
    test "eval Greater_Than: eval e1 is Integer and eval e2 is Float greater than e1 simple" 
     (eval empty builtins (App [Var ">", Val (Integer 5), Val (Float 10)])) (R.Success (Boolean False))  
     
    test "eval Greater_Than: eval e1 is Integer and eval e2 is Float less than e1 simple" 
     (eval empty builtins (App [Var ">", Val (Integer 10), Val (Float 5)])) (R.Success (Boolean True))     

    test "eval Greater_Than: eval e1 is Integer and eval e2 not a numeric type simple" 
     (eval empty builtins (App [Var ">", Val (Integer 5), Val (Boolean True)])) (fail "Wrong number or type of arguments for >.")   

    test "eval Greater_Than: eval e1 is Integer and eval e2 is Integer greater than e1 complex" 
     (eval empty builtins (App [Var ">", App [Var "-", Val (Integer 5), Val (Integer  7)], 
                                      App [Var "+", Val (Integer 10), Val (Integer 20)]])) 
                                    (R.Success (Boolean False)) 

    test "eval Greater_Than: eval e1 is Integer and eval e2 is Integer less than e1 complex" 
     (eval empty builtins (App [Var ">", App [Var "+", Val (Integer 10), Val (Integer  20)], 
                                      App [Var "-", Val (Integer 5), Val (Integer 7)]])) 
                                    (R.Success (Boolean True))                   

    test "eval Greater_Than: eval e1 is Integer and eval e2 is Float greater than e1 complex" 
     (eval empty builtins (App [Var ">", App [Var "+", Val (Integer 10), Val (Integer  20)], 
                                      App [Var "-", Val (Integer 50), Val (Float 7)]])) 
                                    (R.Success (Boolean False))   

    test "eval Greater_Than: eval e1 is Integer and eval e2 is Float less than e1 complex" 
     (eval empty builtins (App [Var ">", App [Var "+", Val (Integer 10), Val (Integer  20)], 
                                      App [Var "-", Val (Integer 10), Val (Float 7)]])) 
                                    (R.Success (Boolean True))     

    test "eval Greater_Than: eval e1 is Integer and eval e2 is not a numeric type complex" 
     (eval empty builtins (App [Var ">", App [Var "+", Val (Integer 10), Val (Integer  20)], 
                                      (And  (Val (Boolean True)) (Val (Boolean False)))])) 
                                    (fail "Wrong number or type of arguments for >.")                                                                                                                                   
      
    test "eval Greater_Than: eval e1 is Float and eval e2 is Integer greater than e1 simple" 
     (eval empty builtins (App [Var ">", Val (Float 5), Val (Integer 10)])) (R.Success (Boolean False))  
     
    test "eval Greater_Than: eval e1 is Float and eval e2 is Integer less than e1 simple" 
     (eval empty builtins (App [Var ">", Val (Float 10), Val (Integer 5)])) (R.Success (Boolean True))    
     
    test "eval Greater_Than: eval e1 is Float and eval e2 is Float greater than e1 simple" 
     (eval empty builtins (App [Var ">", Val (Float 5), Val (Float 10)])) (R.Success (Boolean False))  
     
    test "eval Greater_Than: eval e1 is Float and eval e2 is Float less than e1 simple" 
     (eval empty builtins (App [Var ">", Val (Float 10), Val (Float 5)])) (R.Success (Boolean True))     

    test "eval Greater_Than: eval e1 is Float and eval e2 not a numeric type simple" 
     (eval empty builtins (App [Var ">", Val (Float 5), Val (Boolean True)])) (fail "Wrong number or type of arguments for >.")    

    test "eval Greater_Than: eval e1 is Float and eval e2 is Integer greater than e1 complex" 
     (eval empty builtins (App [Var ">", App [Var "-", Val (Float 5), Val (Integer  7)], 
                                      App [Var "+", Val (Integer 10), Val (Integer 20)]])) 
                                    (R.Success (Boolean False)) 

    test "eval Greater_Than: eval e1 is Float and eval e2 is Integer less than e1 complex" 
     (eval empty builtins (App [Var ">", App [Var "+", Val (Float 10), Val (Integer  20)], 
                                      App [Var "-", Val (Integer 5), Val (Integer 7)]])) 
                                    (R.Success (Boolean True))                   

    test "eval Greater_Than: eval e1 is Float and eval e2 is Float greater than e1 complex" 
     (eval empty builtins (App [Var ">", App [Var "+", Val (Float 10), Val (Integer  20)], 
                                      App [Var "-", Val (Integer 50), Val (Float 7)]])) 
                                    (R.Success (Boolean False))   

    test "eval Greater_Than: eval e1 is Float and eval e2 is Float less than e1 complex" 
     (eval empty builtins (App [Var ">", App [Var "+", Val (Float 10), Val (Integer  20)], 
                                      App [Var "-", Val (Integer 10), Val (Float 7)]])) 
                                    (R.Success (Boolean True))     

    test "eval Greater_Than: eval e1 is Float and eval e2 is not a numeric type complex" 
     (eval empty builtins (App [Var ">", App [Var "+", Val (Float 10), Val (Integer  20)], 
                                      (And (Val (Boolean True)) (Val (Boolean False)))])) 
                                    (fail "Wrong number or type of arguments for >.")                                      

    test "eval Greater_Than: eval e1 is not numeric" 
     (eval empty builtins (App [Var ">", Val (Boolean True), Val (Integer 10)])) (fail "Wrong number or type of arguments for >.") 

    test "eval Greater_Than: eval e1 and eval e2 equal ints should be false" 
     (eval empty builtins (App [Var ">", Val (Integer 10), Val (Integer 10)])) (R.Success (Boolean False))

    test "eval Greater_Than: eval e1 and eval e2 equal floats should be false" 
     (eval empty builtins (App [Var ">" , Val (Float 10), Val (Float 10)])) (R.Success (Boolean False))  


    -- -- // Equal_To Tests 
   
    test "eval Equal_To: eval e1 is Integer and eval e2 is Integer not equal to e1 simple" 
     (eval empty builtins (App [Var "=", Val (Integer 5), Val (Integer 10)])) (R.Success (Boolean False))  
     
    test "eval Equal_To: eval e1 is Integer and eval e2 is Integer equal to e1 simple" 
     (eval empty builtins (App [Var "=", Val (Integer 10), Val (Integer 10)])) (R.Success (Boolean True))    
     
    test "eval Equal_To: eval e1 is Integer and eval e2 is Float not equal to e1 simple" 
     (eval empty builtins (App [Var "=", Val (Integer 5), Val (Float 10)])) (R.Success (Boolean False))  
     
    test "eval Equal_To: eval e1 is Integer and eval e2 is Float equal to e1 simple" 
     (eval empty builtins (App [Var "=", Val (Float 5), Val (Float 5)])) (R.Success (Boolean True))     

    test "eval Equal_To: eval e1 is Integer and eval e2 not a numeric type simple" 
     (eval empty builtins (App [Var "=", Val (Integer 5), Val (Boolean True)])) 
      (fail "Wrong number or type of arguments for =.")   

    test "eval Equal_To: eval e1 is Integer and eval e2 is Integer not equal to e1 complex" 
     (eval empty builtins (App [Var "=", App [Var "-", Val (Integer 5), Val (Integer  7)], 
                                      App [Var "+", Val (Integer 10), Val (Integer 20)]])) 
                                    (R.Success (Boolean False)) 

    test "eval Equal_To: eval e1 is Integer and eval e2 is Integer equal to e1 complex" 
     (eval empty builtins (App [Var "=", App [Var "+", Val (Integer 10), Val (Integer  20)], 
                                      App [Var "-", Val (Integer 32), Val (Integer 2)]])) 
                                    (R.Success (Boolean True))                   

    test "eval Equal_To: eval e1 is Integer and eval e2 is Float not equal to e1 complex" 
     (eval empty builtins (App [Var "=", App [Var "+", Val (Integer 10), Val (Integer  20)], 
                                      App [Var "-", Val (Integer 50), Val (Float 7)]])) 
                                    (R.Success (Boolean False))   

    test "eval Equal_To: eval e1 is Integer and eval e2 is Float equal to complex" 
     (eval empty builtins (App [Var "=", App [Var "+", Val (Integer 10), Val (Integer  20)], 
                                      App [Var "-", Val (Integer 32), Val (Float 2)]])) 
                                    (R.Success (Boolean True))     

    test "eval Equal_To: eval e1 is Integer and eval e2 is not a numeric type complex" 
     (eval empty builtins (App [Var "=", App [Var "+", Val (Integer 10), Val (Integer  20)], 
                                      (And (Val (Boolean True)) (Val (Boolean False)))])) 
                                    (fail "Wrong number or type of arguments for =.")                                                                                                                                   
      
    test "eval Equal_To: eval e1 is Float and eval e2 is Integer not equal to e1 simple" 
     (eval empty builtins (App [Var "=", Val (Float 5), Val (Integer 10)])) (R.Success (Boolean False))  
     
    test "eval Equal_To: eval e1 is Float and eval e2 is Integer equal to e1 simple" 
     (eval empty builtins (App [Var "=", Val (Float 5), Val (Integer 5)])) (R.Success (Boolean True))    
     
    test "eval Equal_To: eval e1 is Float and eval e2 is Float not equal to e1 simple" 
     (eval empty builtins (App [Var "=", Val (Float 5), Val (Float 10)])) (R.Success (Boolean False))  
     
    test "eval Equal_To: eval e1 is Float and eval e2 is Float equal to e1 simple" 
     (eval empty builtins (App [Var "=", Val (Float 10), Val (Float 10)])) (R.Success (Boolean True))     

    test "eval Equal_To: eval e1 is Float and eval e2 not a numeric type simple" 
     (eval empty builtins (App [Var "=", Val (Float 5), Val (Boolean True)])) 
      (fail "Wrong number or type of arguments for =.")    

    test "eval Equal_To: eval e1 is Float and eval e2 is Integer not equal to e1 complex" 
     (eval empty builtins (App [Var "=", App [Var "-", Val (Float 5), Val (Integer  7)], 
                                      App [Var "+", Val (Integer 10), Val (Integer 20)]])) 
                                    (R.Success (Boolean False)) 

    test "eval Equal_To: eval e1 is Float and eval e2 is Integer equal to e1 complex" 
     (eval empty builtins (App [Var "=", App [Var "+", Val (Float 10), Val (Integer  20)], 
                                      App [Var "-", Val (Integer 32), Val (Integer 2)]])) 
                                    (R.Success (Boolean True))                   

    test "eval Equal_To: eval e1 is Float and eval e2 is Float not equal to e1 complex" 
     (eval empty builtins (App [Var "=", App [Var "+", Val (Float 10), Val (Integer  20)], 
                                      App [Var "-", Val (Integer 50), Val (Float 7)]])) 
                                    (R.Success (Boolean False))   

    test "eval Equal_To: eval e1 is Float and eval e2 is Float equal to e1 complex" 
     (eval empty builtins (App [Var "=", App [Var "+", Val (Float 10), Val (Integer  20)], 
                                      App [Var "-", Val (Integer 32), Val (Float 2)]])) 
                                    (R.Success (Boolean True))     

    test "eval Equal_To: eval e1 is Float and eval e2 is not a numeric type complex" 
     (eval empty builtins (App [Var "=", App [Var "+", Val (Float 10), Val (Integer  20)], 
                                      (And (Val (Boolean True)) (Val (Boolean False)))])) 
                                    (fail "Wrong number or type of arguments for =.")                                      

    test "eval Equal_To: eval e1 is not numeric" 
     (eval empty builtins (App [Var "=", Val (Boolean True), Val (Integer 10)])) 
      (fail "Wrong number or type of arguments for =.") 

    test "eval Equal_To: eval e1 is a boolean equal to eval e2 also boolean" 
     (eval empty builtins (App [Var "=", Val (Boolean True), Val (Boolean True)])) (R.Success (Boolean True)) 

    test "eval Equal_To: eval e1 is a boolean not equal to eval e2 also boolean" 
     (eval empty builtins (App [Var "=", Val (Boolean True), Val (Boolean False)])) (R.Success (Boolean False))  

    test "eval Equal_To: eval e1 is a Nothing and eval e2 also Nothing" 
     (eval empty builtins (App [Var "=", App [Var "-", Val (Integer 5), Val (Boolean True)],
                                      App [Var "+", Val (Integer 5), Val (Boolean False)]])) 
                                       (fail "Wrong number or type of arguments for -.") 


    -- -- // LEQ Tests 

    test "eval LEQ: eval e1 is Integer and eval e2 is Integer not LEQ to e1 simple" 
     (eval empty builtins (App [Var "<=", Val (Integer 15), Val (Integer 10)])) (R.Success (Boolean False))  
     
    test "eval LEQ: eval e1 is Integer and eval e2 is Integer LEQ to e1 simple" 
     (eval empty builtins (App [Var "<=", Val (Integer 10), Val (Integer 10)])) (R.Success (Boolean True))    
     
    test "eval LEQ: eval e1 is Integer and eval e2 is Float not LEQ to e1 simple" 
     (eval empty builtins (App [Var "<=", Val (Integer 40), Val (Float 10)])) (R.Success (Boolean False))  
     
    test "eval LEQ: eval e1 is Integer and eval e2 is Float LEQ to e1 simple" 
     (eval empty builtins (App [Var "<=", Val (Float 5), Val (Float 5)])) (R.Success (Boolean True))     

    test "eval LEQ: eval e1 is Integer and eval e2 not a numeric type simple" 
     (eval empty builtins (App [Var "<=", Val (Integer 5), Val (Boolean True)])) 
      (fail "Wrong number or type of arguments for <=.")   

    test "eval LEQ: eval e1 is Integer and eval e2 is Integer not LEQ to e1 complex" 
     (eval empty builtins (App [Var "<=", App [Var "-", Val (Integer 100), Val (Integer  7)], 
                                      App [Var "+", Val (Integer 10), Val (Integer 20)]])) 
                                    (R.Success (Boolean False)) 

    test "eval LEQ: eval e1 is Integer and eval e2 is Integer LEQ to e1 complex" 
     (eval empty builtins (App [Var "<=", App [Var "+", Val (Integer 1), Val (Integer  20)], 
                                      App [Var "-", Val (Integer 32), Val (Integer 2)]])) 
                                    (R.Success (Boolean True))                   

    test "eval LEQ: eval e1 is Integer and eval e2 is Float not LEQ to e1 complex" 
     (eval empty builtins (App [Var "<=", App [Var "+", Val (Integer 100), Val (Integer  20)], 
                                      App [Var "-", Val (Integer 50), Val (Float 7)]])) 
                                    (R.Success (Boolean False))   

    test "eval LEQ: eval e1 is Integer and eval e2 is Float LEQ to complex" 
     (eval empty builtins (App [Var "<=", App [Var "+", Val (Integer 10), Val (Integer  20)], 
                                      App [Var "-", Val (Integer 32), Val (Float 2)]])) 
                                    (R.Success (Boolean True))     

    test "eval LEQ: eval e1 is Integer and eval e2 is not a numeric type complex" 
     (eval empty builtins (App [Var "<=", App [Var "+", Val (Integer 10), Val (Integer  20)], 
                                      (And  (Val (Boolean True)) (Val (Boolean False)))])) 
                                    (fail "Wrong number or type of arguments for <=.")                                                                                                                                   
      
    test "eval LEQ: eval e1 is Float and eval e2 is Integer not LEQ to e1 simple" 
     (eval empty builtins (App [Var "<=", Val (Float 90), Val (Integer 10)])) (R.Success (Boolean False))  
     
    test "eval LEQ: eval e1 is Float and eval e2 is Integer LEQ to e1 simple" 
     (eval empty builtins (App [Var "<=", Val (Float 4), Val (Integer 5)])) (R.Success (Boolean True))    
     
    test "eval LEQ: eval e1 is Float and eval e2 is Float not LEQ to e1 simple" 
     (eval empty builtins (App [Var "<=", Val (Float 76), Val (Float 10)])) (R.Success (Boolean False))  
     
    test "eval LEQ: eval e1 is Float and eval e2 is Float LEQ to e1 simple" 
     (eval empty builtins (App [Var "<=", Val (Float 10), Val (Float 10)])) (R.Success (Boolean True))     

    test "eval LEQ: eval e1 is Float and eval e2 not a numeric type simple" 
     (eval empty builtins (App [Var "<=", Val (Float 5), Val (Boolean True)])) 
      (fail "Wrong number or type of arguments for <=.")    

    test "eval LEQ: eval e1 is Float and eval e2 is Integer not LEQ to e1 complex" 
     (eval empty builtins (App [Var "<=", App [Var "-", Val (Float 100), Val (Integer  7)], 
                                      App [Var "+", Val (Integer 10), Val (Integer 20)]])) 
                                    (R.Success (Boolean False)) 

    test "eval LEQ: eval e1 is Float and eval e2 is Integer LEQ to e1 complex" 
     (eval empty builtins (App [Var "<=", App [Var "+", Val (Float 10), Val (Integer  0)], 
                                      App [Var "-", Val (Integer 32), Val (Integer 2)]])) 
                                    (R.Success (Boolean True))                   

    test "eval LEQ: eval e1 is Float and eval e2 is Float not LEQ to e1 complex" 
     (eval empty builtins (App [Var "<=", App [Var "+", Val (Float 100), Val (Integer  20)], 
                                      App [Var "-", Val (Integer 50), Val (Float 7)]])) 
                                    (R.Success (Boolean False))   

    test "eval LEQ: eval e1 is Float and eval e2 is Float LEQ to e1 complex" 
     (eval empty builtins (App [Var "<=", App [Var "+", Val (Float 1), Val (Integer  20)], 
                                      App [Var "-", Val (Integer 32), Val (Float 2)]])) 
                                    (R.Success (Boolean True))     

    test "eval LEQ: eval e1 is Float and eval e2 is not a numeric type complex" 
     (eval empty builtins (App [Var "<=", App [Var "+", Val (Float 10), Val (Integer  20)], 
                                      (And  (Val (Boolean True)) (Val (Boolean False)))]))
                                    (fail "Wrong number or type of arguments for <=.")                                      

    test "eval LEQ: eval e1 is not numeric" 
     (eval empty builtins (App [Var "<=", Val (Boolean True), Val (Integer 10)])) 
      (fail "Wrong number or type of arguments for <=.") 

    test "eval LEQ: eval e1 is a Nothing and eval e2 also Nothing" 
     (eval empty builtins (App [Var "<=", App [Var "-", Val (Integer 5), Val (Boolean True)],
                                      App [Var "+", Val (Integer 5), Val (Boolean False)]])) 
                                       (fail "Wrong number or type of arguments for -.")    

    -- -- // GEQ Tests 
   
    test "eval GEQ: eval e1 is Integer and eval e2 is Integer not GEQ to e1 simple" 
     (eval empty builtins (App [Var ">=", Val (Integer 5), Val (Integer 10)])) (R.Success (Boolean False))  
     
    test "eval GEQ: eval e1 is Integer and eval e2 is Integer GEQ to e1 simple" 
     (eval empty builtins (App [Var ">=", Val (Integer 10), Val (Integer 10)])) (R.Success (Boolean True))    
     
    test "eval GEQ: eval e1 is Integer and eval e2 is Float not GEQ to e1 simple" 
     (eval empty builtins (App [Var ">=", Val (Integer 5), Val (Float 10)])) (R.Success (Boolean False))  
     
    test "eval GEQ: eval e1 is Integer and eval e2 is Float GEQ to e1 simple" 
     (eval empty builtins (App [Var ">=", Val (Float 5), Val (Float 5)])) (R.Success (Boolean True))     

    test "eval GEQ: eval e1 is Integer and eval e2 not a numeric type simple" 
     (eval empty builtins (App [Var ">=", Val (Integer 5), Val (Boolean True)])) 
      (fail "Wrong number or type of arguments for >=.")   

    test "eval GEQ: eval e1 is Integer and eval e2 is Integer not GEQ to e1 complex" 
     (eval empty builtins (App [Var ">=", App [Var "-", Val (Integer 5), Val (Integer  7)], 
                                      App [Var "+", Val (Integer 10), Val (Integer 20)]])) 
                                    (R.Success (Boolean False)) 

    test "eval GEQ: eval e1 is Integer and eval e2 is Integer GEQ to e1 complex" 
     (eval empty builtins (App [Var ">=", App [Var "+", Val (Integer 10), Val (Integer  22)], 
                                      App [Var "-", Val (Integer 32), Val (Integer 2)]])) 
                                    (R.Success (Boolean True))                   

    test "eval GEQ: eval e1 is Integer and eval e2 is Float not GEQ to e1 complex" 
     (eval empty builtins (App [Var ">=", App [Var "+", Val (Integer 10), Val (Integer  20)], 
                                      App [Var "-", Val (Integer 50), Val (Float 7)]])) 
                                    (R.Success (Boolean False))   

    test "eval GEQ: eval e1 is Integer and eval e2 is Float GEQ to complex" 
     (eval empty builtins (App [Var ">=", App [Var "+", Val (Integer 10), Val (Integer  24)], 
                                      App [Var "-", Val (Integer 32), Val (Float 2)]])) 
                                    (R.Success (Boolean True))     

    test "eval GEQ: eval e1 is Integer and eval e2 is not a numeric type complex" 
     (eval empty builtins (App [Var ">=", App [Var "+", Val (Integer 10), Val (Integer  20)], 
                                      (And (Val (Boolean True)) (Val (Boolean False)))]))
                                    (fail "Wrong number or type of arguments for >=.")                                                                                                                                   
      
    test "eval GEQ: eval e1 is Float and eval e2 is Integer not GEQ to e1 simple" 
     (eval empty builtins (App [Var ">=", Val (Float 5), Val (Integer 10)])) (R.Success (Boolean False))  
     
    test "eval GEQ: eval e1 is Float and eval e2 is Integer GEQ to e1 simple" 
     (eval empty builtins (App [Var ">=", Val (Float 5), Val (Integer 5)])) (R.Success (Boolean True))    
     
    test "eval GEQ: eval e1 is Float and eval e2 is Float not GEQ to e1 simple" 
     (eval empty builtins (App [Var ">=", Val (Float 5), Val (Float 10)])) (R.Success (Boolean False))  
     
    test "eval GEQ: eval e1 is Float and eval e2 is Float GEQ to e1 simple" 
     (eval empty builtins (App [Var ">=", Val (Float 12), Val (Float 10)])) (R.Success (Boolean True))     

    test "eval GEQ: eval e1 is Float and eval e2 not a numeric type simple" 
     (eval empty builtins (App [Var ">=", Val (Float 5), Val (Boolean True)])) 
      (fail "Wrong number or type of arguments for >=.")    

    test "eval GEQ: eval e1 is Float and eval e2 is Integer not GEQ to e1 complex" 
     (eval empty builtins (App [Var ">=", App [Var "-", Val (Float 5), Val (Integer  7)], 
                                      App [Var "+", Val (Integer 10), Val (Integer 20)]])) 
                                    (R.Success (Boolean False)) 

    test "eval GEQ: eval e1 is Float and eval e2 is Integer GEQ to e1 complex" 
     (eval empty builtins (App [Var ">=", App [Var "+", Val (Float 10), Val (Integer  30)], 
                                      App [Var "-", Val (Integer 32), Val (Integer 2)]])) 
                                    (R.Success (Boolean True))                   

    test "eval GEQ: eval e1 is Float and eval e2 is Float not GEQ to e1 complex" 
     (eval empty builtins (App [Var ">=", App [Var "+", Val (Float 10), Val (Integer  20)], 
                                      App [Var "-", Val (Integer 50), Val (Float 7)]])) 
                                    (R.Success (Boolean False))   

    test "eval GEQ: eval e1 is Float and eval e2 is Float GEQ to e1 complex" 
     (eval empty builtins (App [Var ">=", App [Var "+", Val (Float 15), Val (Integer  20)], 
                                      App [Var "-", Val (Integer 32), Val (Float 2)]])) 
                                    (R.Success (Boolean True))     

    test "eval GEQ: eval e1 is Float and eval e2 is not a numeric type complex" 
     (eval empty builtins (App [Var ">=", App [Var "+", Val (Float 10), Val (Integer  20)], 
                                      (And (Val (Boolean True)) (Val (Boolean False)))]))
                                    (fail "Wrong number or type of arguments for >=.")                                      

    test "eval GEQ: eval e1 is not numeric" 
     (eval empty builtins (App [Var ">=", Val (Boolean True), Val (Integer 10)])) 
      (fail "Wrong number or type of arguments for >=.") 

    test "eval GEQ: eval e1 is a Nothing and eval e2 also Nothing" 
     (eval empty builtins (App [Var ">=", App [Var "-", Val (Integer 5), Val (Boolean True)],
                                      App [Var "+", Val (Integer 5), Val (Boolean False)]])) 
                                       (fail "Wrong number or type of arguments for -.")                                                                    
  
    -- // Cond Tests
    test "eval Cond with nothing: first true" (eval empty builtins ( Cond [(Val (Boolean True), 
     App [Var "+", Val (Integer 5), Val (Integer 2)])]  Nothing))
       (R.Success  (Integer 7))

    test "eval Cond with nothing: next true" (eval empty builtins ( Cond [(Val (Boolean False), 
     App [Var "+", Val (Integer 5), Val (Integer 2)]), 
        (Val (Boolean True), App [Var "/", Val (Integer 4), Val (Integer 2)])] Nothing))
       (R.Success  (Integer 2))

    test "eval Cond with nothing: no true" (eval empty builtins ( Cond [(Val (Boolean False), 
     App [Var "+", Val (Integer 5), Val (Integer 2)]), 
        (Val (Boolean False), App [Var "/", Val (Integer 4), Val (Integer 2)])] Nothing))
       (fail "Cond ended without a returned expression.")

    test "eval Cond with nothing: clause isnt boolean" (eval empty builtins ( Cond [(Val (Integer 10), 
     App [Var "+", Val (Integer 5), Val (Integer 2)]), 
        (Val (Boolean False), App [Var "/", Val (Integer 4), Val (Integer 2)])] Nothing))
       (fail "Cond clause was not a boolean.")

    test "eval Cond with end: first true" (eval empty builtins ( Cond [(Val (Boolean True), 
     App [Var "+", Val (Integer 5), Val (Integer 2)])] 
      (Just (App [Var "-", Val (Integer 5), Val (Integer 2)]))))
       (R.Success  (Integer 7))

    test "eval Cond with end: next true" (eval empty builtins ( Cond [(Val (Boolean False), 
     App [Var "+", Val (Integer 5), Val (Integer 2)]), 
        (Val (Boolean True), App [Var "/", Val (Integer 4), Val (Integer 2)])]
         (Just (App [Var "-", Val (Integer 5), Val (Integer 2)]))))
       (R.Success  (Integer 2))

    test "eval Cond with end: no true" (eval empty builtins ( Cond [(Val (Boolean False), 
     App [Var "+", Val (Integer 5), Val (Integer 2)]), 
        (Val (Boolean False), App [Var "/", Val (Integer 4), Val (Integer 2)])]
         (Just (App [Var "-", Val (Integer 5), Val (Integer 2)]))))
       (R.Success (Integer 3))

    test "eval Cond with end: clause isnt boolean" (eval empty builtins ( Cond [(Val (Integer 10), 
     App [Var "+", Val (Integer 5), Val (Integer 2)]), 
        (Val (Boolean False), App [Var "/", Val (Integer 4), Val (Integer 2)])]
         (Just (App [Var "-", Val (Integer 5), Val (Integer 2)]))))
       (fail "Cond clause was not a boolean.")   

    -- // Pair Tests    
    test "eval Pair: eval e1 and eval e2 are nothing" (eval empty builtins (Pair 
     (App [Var "+", Val (Integer 5), Val (Boolean False)]) (Var "x")))
      (fail "Wrong number or type of arguments for +." )

    test "eval Pair: eval e1 is not nothing but eval e2 is nothing" (eval empty builtins ( Pair 
     (Val (Integer 10)) (Var "x")))
      (fail "Variable x not defined.")   

    test "eval Pair: eval e1 is not nothing but eval e2 is not nothing" (eval empty builtins (Pair 
     (Val (Integer 5)) (Let "x" (Val (Boolean False)) (Var "x"))))
     (R.Success (PairVal (Integer 5) (Boolean False)))

    -- -- // Left Tests    
    test "eval Left: Expr is nothing, simple" (eval empty builtins (
     Left (Var "x"))) (fail "Variable x not defined.")  

    test "eval Left: Expr is something but not a pair" (eval empty builtins ( Left (Val (Boolean False))))
     (fail "Left not applied to pair.")   

    test "eval Left: Expr is a pair that evals to nothing" (eval empty builtins ( Left 
     ( Pair (App [Var "+", Val (Integer 5), Val (Boolean False)]) (Var "x")))) 
      (fail "Wrong number or type of arguments for +.")     

    test "eval Left: Expr is a good pair" (eval empty builtins ( Left (Pair 
     (App [Var "+", Val (Integer 5), Val (Float 6.5)]) (Let "x" (Val (Boolean False)) (Var "x")))))
     (R.Success (Float 11.5))     

    -- -- // Right Tests    
    test "eval Right: Expr is nothing, simple" (eval empty builtins (
     Right (Var "x"))) (fail "Variable x not defined.")  

    test "eval Right: Expr is something but not a pair" (eval empty builtins ( Right (Val (Boolean False))))
     (fail "Right not applied to pair.")   

    test "eval Right: Expr is a pair that evals to nothing" (eval empty builtins ( Right 
     ( Pair (App [Var "+", Val (Integer 5), Val (Boolean False)]) (Var "x")))) 
      (fail "Wrong number or type of arguments for +.")     

    test "eval Right: Expr is a good pair" (eval empty builtins ( Right (Pair 
     (App [Var "+", Val (Integer 5), Val (Float 6.5)]) (Let "x" (Val (Boolean False)) (Var "x")))))
     (R.Success (Boolean False))    
 
    -- // Real_Pred tests 
    test "eval Real_Pred: Expr is a float simple" (eval empty builtins ( Real_Pred 
     (Val (Float 5.5)))) (R.Success (Boolean True))

    test "eval Real_Pred: Expr is a float complex" (eval empty builtins ( Real_Pred 
     (If (Val (Boolean True)) (App [Var "/",Val  (Integer 10), Val (Float 5.1)]) (Val (Integer 10)))))
      (R.Success (Boolean True))  

    test "eval Real_Pred: Expr is not a float" (eval empty builtins ( Real_Pred 
     (Val (Integer 5)))) (R.Success (Boolean False))     

    -- // Integer_Pred tests 
    test "eval Integer_Pred: Expr is a integer simple" (eval empty builtins ( Integer_Pred 
     (Val (Integer 5)))) (R.Success (Boolean True))

    test "eval Integer_Pred: Expr is a integer complex" (eval empty builtins ( Integer_Pred 
     (If (Val (Boolean True)) (App [Var "/",Val  (Integer 10), Val (Integer 5)]) (Val (Integer 10)))))
      (R.Success (Boolean True))  

    test "eval Integer_Pred: Expr is not a integer" (eval empty builtins ( Integer_Pred 
     (Val (Float 5)))) (R.Success (Boolean False))  

    -- // Number_Pred tests 
    test "eval Number_Pred: Expr is a integer simple" (eval empty builtins ( Number_Pred 
     (Val (Integer 5)))) (R.Success (Boolean True))

    test "eval Number_Pred: Expr is a integer complex" (eval empty builtins ( Number_Pred 
     (If (Val (Boolean True)) (App [Var "/",Val  (Integer 10), Val (Float 5.1)]) (Val (Integer 10)))))
      (R.Success (Boolean True))  

    test "eval Number_Pred: Expr is a float simple" (eval empty builtins ( Number_Pred 
     (Val (Float 5.5)))) (R.Success (Boolean True))

    test "eval Number_Pred: Expr is a float complex" (eval empty builtins ( Number_Pred 
     (If (Val (Boolean True)) (App [Var "/",Val  (Integer 10), Val (Float 5.1)]) (Val (Integer 10)))))
      (R.Success (Boolean True))   

    test "eval Number_Pred: Expr is not a integer or float simple" (eval empty builtins ( Number_Pred 
     (Val (Boolean False)))) (R.Success (Boolean False))   

    -- // Boolean_Pred tests 
    test "eval Boolean_Pred: Expr is a boolean simple" (eval empty builtins ( Boolean_Pred 
     (Val (Boolean False)))) (R.Success (Boolean True))

    test "eval Boolean_Pred: Expr is a boolean complex" (eval empty builtins ( Boolean_Pred 
     (If (Val (Boolean False)) (App [Var "/",Val  (Integer 10), Val (Float 5.1)]) (Val (Boolean True)))))
      (R.Success (Boolean True))  

    test "eval Boolean_Pred: Expr is not a boolean simple" (eval empty builtins ( Boolean_Pred 
     (Val (Float 5)))) (R.Success (Boolean False))

    -- // Pair_Pred tests 
    test "eval Pair_Pred: Expr is a pair" (eval empty builtins ( Pair_Pred 
     (Pair (App [Var "+", Val (Integer 5), Val (Float 6.5)]) (Let "x" (Val (Boolean False)) (Var "x")))))
      (R.Success (Boolean True))     

    test "eval Pair_Pred: Expr is not a pair simple" (eval empty builtins ( Pair_Pred 
     (Val (Boolean False)))) (R.Success (Boolean False))

    -- // Tests for Lambda and App
    test "eval lambda: simple 1" (eval empty empty (Lambda ["x"] (Var "x"))) 
     (R.Success (Closure ["x"] (Var "x") empty))

    test "eval lambda: simple 2" (eval empty empty (Lambda ["x", "y"] (Var "x"))) 
     (R.Success (Closure ["x", "y"] (Var "x") empty)) 

    test "eval App: simple 1" (eval empty empty (App [Lambda ["x"] (Var "x"), Val (Integer 10)])) 
     (R.Success (Integer 10))

    test "eval App: simple 2" (eval empty empty (App [Lambda ["x", "y"] 
     (Var "y"), Val (Integer 10), Val (Integer 15)])) 
     (R.Success (Integer 15)) 

    test "eval App: not enough args 1" (eval empty empty (App [Lambda ["x"] 
     (Var "y")])) 
     (fail "Lambda call did not receive enough arguments.")  

    test "eval App: not enough args 2" (eval empty empty (App [Lambda ["x", "y"] 
     (Var "y"), Val (Integer 10)])) 
     (fail "Lambda call did not receive enough arguments.") 

    test "eval App: too many args" (eval empty empty (App [Lambda ["x"] 
     (Var "y"), Val (Integer 10), Val (Float 5.5)])) 
     (fail "Lambda call received too many arguments.")    
     



-- |Run the given protoScheme s-expression, returning an s-expression
-- representation of the result.
{-
  Added in check for if the S.Expr is a program or not. 
    If it is a program then do the evalProgram, otherwise do the normal eval 
-}
runSExpression :: S.Expr -> R.Result S.Expr
runSExpression se =
    case se of 
      (S.List[S.Symbol "Program", S.List defs]) -> do
          v <- evalProgram (programFromSExpression se) 
          return (valueToSExpression v)
      _ -> do 
          v <- eval empty builtins (fromSExpression se) 
          return (valueToSExpression v)
    
-- tests of runSExpression
test_runSExpression = do

    test "run: (+ 1 2)"
        (runSExpression $ S.List [S.Symbol "+", S.Integer 1, S.Integer 2])
        (R.Success $ S.Integer 3)

    test "runSExpression Test Variable" (runSExpression $ S.Symbol "v") (fail "Variable v not defined.")

    -- Integer Tests

    test "Integer runSExpression 42" (runSExpression $ S.Integer 42) (R.Success (S.Integer 42))

    test "Integer runSExpression Test Add" (runSExpression $ S.List [S.Symbol "+",
     S.Integer 4, S.Integer 10]) (R.Success $ S.Integer 14)

    test "Integer runSExpression Test Sub" (runSExpression $ S.List [S.Symbol "-",
     S.Integer 4, S.Integer 10]) (R.Success $ S.Integer (-6))

    test "Integer runSExpression Test Mul" (runSExpression $ S.List [S.Symbol "*",
     S.Integer 4, S.Integer 10]) (R.Success $ S.Integer 40)

    test "Integer runSExpression Test Div" (runSExpression $ S.List [S.Symbol "/",
     S.Integer 4, S.Integer 10]) (R.Success $ S.Integer 0)

    test "Integer runSExpression Test Nested Operations" (runSExpression $ S.List [S.Symbol "/",
     S.List [S.Symbol "+", S.Integer 4, S.Integer 10], S.List [S.Symbol "-",
      S.Integer 10, S.Integer 6]]) 
     (R.Success $ S.Integer 3)

    test "Integer runSExpression Test Let  Simple" (runSExpression $ S.List [S.Symbol "let", S.List [S.Symbol "x",
     S.List [S.Symbol "+", S.Integer 10, S.Integer 4]], S.List [S.Symbol "+", S.Symbol "x", S.Integer 1]])
     (R.Success $ S.Integer 15)

    test "Integer runExpression Test Let Complex" (runSExpression $ S.List [S.Symbol "let", S.List [S.Symbol "y",
     S.List [S.Symbol "-", S.Integer 20, S.Integer 8]], S.List [S.Symbol "let", S.List [S.Symbol "x",
      S.List [S.Symbol "+", S.Symbol "y", S.Integer 4]], S.List [S.Symbol "+",
       S.Symbol "x", S.Integer 1]]])
       (R.Success $ S.Integer 17)

    -- Real Tests 

    test "Real runSExpression 42" (runSExpression $ S.Real 42.0) (R.Success $ S.Real 42.0)

    test "Real runSExpression Test Add" (runSExpression $ S.List [S.Symbol "+",
     S.Real 4.1, S.Real 10.1]) (R.Success $ S.Real 14.2)

    test "Real runSExpression Test Sub" (runSExpression $ S.List [S.Symbol "-",
     S.Real 4.1, S.Real 10.1]) (R.Success $ S.Real (-6.0))

    test "Real runSExpression Test Mul" (runSExpression $ S.List [S.Symbol "*",
     S.Real 4.1, S.Real 10.1]) (R.Success $ S.Real 41.41)

    test "Real runSExpression Test Div" (runSExpression $ S.List [S.Symbol "/",
     S.Real 4.1, S.Real 10.1]) (R.Success $ S.Real 0.4059405940594059)

    test "Real runSExpression Test Nested Operations" (runSExpression $ S.List [S.Symbol "/",
     S.List [S.Symbol "+", S.Real 4.1, S.Real 10.1], S.List [S.Symbol "-",
      S.Real 4.1, S.Real 10.1]]) (R.Success $ S.Real (-2.3666666666666667))

    test "Real runSExpression Test Let  Simple" (runSExpression $ S.List [S.Symbol "let", S.List [S.Symbol "x",
     S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]])
     (R.Success $ S.Real 15.299999999999999)

    test "Real runSExpression Test Let Complex" (runSExpression $ S.List [S.Symbol "let", S.List [S.Symbol "y",
     S.List [S.Symbol "-", S.Real 20.1, S.Real 8.1]], S.List [S.Symbol "let", S.List [S.Symbol "x",
      S.List [S.Symbol "+", S.Symbol "y", S.Real 4.1]], S.List [S.Symbol "+",
       S.Symbol "x", S.Real 1.1]]])
     (R.Success $ S.Real 17.200000000000003) 

    -- Mixed Tests 

    test "Mixed runSExpression Test Add" (runSExpression $ S.List [S.Symbol "+",
     S.Real 4.1, S.Integer 10]) (R.Success $ S.Real 14.1)

    test "Mixed runSExpression Test Sub" (runSExpression $ S.List [S.Symbol "-",
     S.Real 4.1, S.Integer 10]) (R.Success $ S.Real (-5.9))

    test "Mixed runSExpression Test Mul" (runSExpression $ S.List [S.Symbol "*",
     S.Real 4.1, S.Integer 10]) (R.Success $ S.Real 41)

    test "Mixed runSExpression Test Div" (runSExpression $ S.List [S.Symbol "/",
     S.Real 4.1, S.Integer 10]) (R.Success $ S.Real 0.41)

    test "Mixed runSExpression Test Nested Operations" (runSExpression $ S.List [S.Symbol "/",
     S.List [S.Symbol "+", S.Real 4.1, S.Integer 10], S.List [S.Symbol "-",
      S.Real 4.1, S.Real 10.1]]) (R.Success $ S.Real (-2.35))

    test "Mixed runSExpression Test Let  Simple" (runSExpression $ S.List [S.Symbol "let", S.List [S.Symbol "x",
     S.List [S.Symbol "+", S.Integer 10, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]])
     (R.Success $ S.Real 15.2)

    test "Mixed runSExpression Test Let Complex" (runSExpression $ S.List [S.Symbol "let", S.List [S.Symbol "y",
     S.List [S.Symbol "-", S.Integer 20, S.Real 8.1]], S.List [S.Symbol "let", S.List [S.Symbol "x",
      S.List [S.Symbol "+", S.Symbol "y", S.Real 4.1]], S.List [S.Symbol "+",
       S.Symbol "x", S.Real 1.1]]])
     (R.Success $ S.Real 17.1)   


    -- Boolean tests

    test "Boolean runSExpression Test 1" (runSExpression $ S.Boolean False) 
      (R.Success $ S.Boolean False)

    test "Boolean runSExpression Test 2" (runSExpression $ S.Boolean True) 
      (R.Success $ S.Boolean True)  

    -- If tests 

    test "If runSExpression Test e1 is True Simple" (runSExpression $ S.List 
      [S.Symbol "if", S.Boolean True, S.Integer 10, S.Real 15])
        (R.Success $ S.Integer 10)  

    test "If runSExpression Test e1 is False Simple" (runSExpression $ S.List 
      [S.Symbol "if", S.Boolean False, S.Integer 10, S.Real 15])
        (R.Success $ S.Real 15)      

    test "If runSExpression Test e1 is True Complex" (runSExpression $ S.List 
      [S.Symbol "if", S.Boolean True, S.List [S.Symbol "+", S.Integer 10, S.Integer 15] , S.Real 15])
        (R.Success $ S.Integer 25)  

    test "If runSExpression Test e1 is False Complex" (runSExpression $ S.List 
      [S.Symbol "if", S.Boolean False, S.Integer 10, S.List [S.Symbol "+", S.Real 10.1, S.Real 15.1]])
        (R.Success $ S.Real 25.2)     

    test "If runSExpression Test e1 is not a boolean" (runSExpression $ S.List 
      [S.Symbol "if", S.List [S.Symbol "+", S.Integer 10, S.Integer 15], S.Integer 10, S.Real 15])
        (fail "If not passed a boolean for first expression.")        

    -- And tests
    test "And runSExpression Test 1" (runSExpression $ S.List [S.Symbol "and" , S.Boolean True, S.Integer 10]) 
        (fail "And not passed a boolean for second argument.")    

    test "And runSExpression Test 3" (runSExpression $ S.List [
        S.Symbol "and" , S.List [S.Symbol "and" , S.Integer 10, S.Real 15.1], 
         S.List [S.Symbol "let", S.List [S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
        (fail "And not passed a boolean for first argument.")      

    test "And runSExpression Test 4" (runSExpression $ S.List [S.Symbol "and" , S.Boolean True, S.Boolean False]) 
        (R.Success $ S.Boolean False)
      
    test "And runSExpression Test 5" (runSExpression $ S.List [S.Symbol "and" , S.Boolean True, S.Boolean True]) 
        (R.Success $ S.Boolean True)

    -- Or tests
    test "Or runSExpression Test 1" (runSExpression $ S.List [
        S.Symbol "or" , S.Boolean True, S.Integer 10]) 
        (R.Success $ S.Boolean True)

    test "Or runSExpression Test 3" (runSExpression $ S.List [
        S.Symbol "or" , S.List [S.Symbol "or" , S.Integer 10, S.Real 15.1], 
         S.List [S.Symbol "let", S.List [S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
        (fail "Or not passed a boolean for first argument.")      

    test "Or runSExpression Test 4" (runSExpression $ S.List [
        S.Symbol "or" , S.Boolean True, S.Boolean False]) 
        (R.Success $ S.Boolean True)

    test "Or runSExpression Test 5" (runSExpression $ S.List [
        S.Symbol "or" , S.Boolean False, S.Boolean False]) 
        (R.Success $ S.Boolean False)

    -- Not tests
    test "Not runSExpression Test 1" (runSExpression $ S.List [
        S.Symbol "not" , S.Boolean True]) 
        (R.Success $ S.Boolean False)

    test "Not fromSExpression Test 2" (runSExpression $ S.List [
        S.Symbol "not" , S.List [S.Symbol "let", S.List [S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
        (fail "Wrong number or type of arguments for not.")        

    test "Not runSExpression Test 4" (runSExpression $ S.List [
        S.Symbol "not" , S.Boolean False]) 
        (R.Success $ S.Boolean True)     

    -- //Less_Than tests 
    test "Less_Than runSExpression Test 1" (runSExpression $ S.List [
        S.Symbol "<", S.Boolean True, S.Integer 10]) 
        (fail "Wrong number or type of arguments for <.")  

    test "Less_Than runSExpression Test 2" (runSExpression $ S.List [
        S.Symbol "<", S.Integer 30, S.List [S.Symbol "let", S.List [S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
        (R.Success $ S.Boolean False)    

    test "Less_Than runSExpression Test 3" (runSExpression $ S.List [
         S.Symbol "<", S.List [S.Symbol "let", S.List [S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]], S.Integer 30]) 
        (R.Success $ S.Boolean True)      

    test "Less_Than runSExpression Test 4" (runSExpression $ S.List [
        S.Symbol "<", S.Real 15.1, S.Real 13.2]) 
        (R.Success $ S.Boolean False)

    test "Less_Than runSExpression Test 5" (runSExpression $ S.List [
        S.Symbol "<", S.Integer 5, S.Integer 6]) 
        (R.Success $ S.Boolean True)

    -- //Greater_Than tests 
    test "Greater_Than runSExpression Test 1" (runSExpression $ S.List [
        S.Symbol ">" , S.Boolean True, S.Integer 10]) 
        (fail "Wrong number or type of arguments for >.")  

    test "Greater_Than runSExpression Test 2" (runSExpression $ S.List [
        S.Symbol ">" , S.Integer 30, S.List [S.Symbol "let", S.List [S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
        (R.Success $ S.Boolean True)    

    test "Greater_Than runSExpression Test 3" (runSExpression $ S.List [
         S.Symbol ">" , S.List [S.Symbol "let", S.List [S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]], S.Integer 30]) 
        (R.Success $ S.Boolean False)      

    test "Greater_Than runSExpression Test 4" (runSExpression $ S.List [
        S.Symbol ">" , S.Real 15.1, S.Real 13.2]) 
        (R.Success $ S.Boolean True)

    test "Greater_Than runSExpression Test 5" (runSExpression $ S.List [
        S.Symbol ">" , S.Integer 5, S.Integer 6]) 
        (R.Success $ S.Boolean False)

     -- //Equal_To tests 
    test "Equal_To runSExpression Test 1" (runSExpression $ S.List [
        S.Symbol "=" , S.Boolean True, S.Integer 10]) 
        (fail "Wrong number or type of arguments for =.")  

    test "Equal_To runSExpression Test 2" (runSExpression $ S.List [
        S.Symbol "=" , S.Real 15.4, S.List [S.Symbol "let", S.List [S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.2]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
        (R.Success $ S.Boolean True)    

    test "Equal_To runSExpression Test 3" (runSExpression $ S.List [
         S.Symbol "=" , S.List [S.Symbol "let", S.List [S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.0, S.Real 4.0]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.0]], S.Integer 15]) 
        (R.Success $ S.Boolean True)      

    test "Equal_To runSExpression Test 4" (runSExpression $ S.List [
        S.Symbol "=" , S.Integer 15, S.Integer 13]) 
        (R.Success $ S.Boolean False)

    test "Equal_To runSExpression Test 5" (runSExpression $ S.List [
        S.Symbol "=" , S.Integer 5, S.Integer 5]) 
        (R.Success $ S.Boolean True) 
    
    test "Equal_To runSExpression Test 6" (runSExpression $ S.List [
        S.Symbol "=" , S.Real 5.0, S.Integer 5]) 
        (R.Success $ S.Boolean True) 

    -- <= tests
    test "<= runSExpression Test 1" (runSExpression $ S.List [S.Symbol "<=", S.Integer 7, S.Integer 6])
      (R.Success $ S.Boolean False)

    test "<= runSExpression Test 2" (runSExpression $ S.List [S.Symbol "<=", S.Integer 6, S.Integer 7])
      (R.Success $ S.Boolean True)
    
    test "<= runSExpression Test 3" (runSExpression $ S.List [S.Symbol "<=", S.Real 6.8, S.Real 6.3])
      (R.Success $ S.Boolean False)
    
    test "<= runSExpression Test 4" (runSExpression $ S.List [S.Symbol "<=", S.Boolean True, S.Real 6.3])
      (fail "Wrong number or type of arguments for <=.") 
    
    test "<= runSExpression <= Test 5" (runSExpression $ S.List [S.Symbol "<=", S.List[S.Symbol "+", S.Integer 7, 
       S.Integer 6], S.Symbol "x"])
      (fail "Variable x not defined.")
        
    test "<= runSExpression Test 6" (runSExpression $ S.List [S.Symbol "<=", S.List [S.Symbol "if", S.Boolean True, 
       S.Boolean True, S.Boolean False], S.List[S.Symbol "let", S.List [S.Symbol "v", S.Real 6.3], S.Real 6.3]])   
     (fail "Wrong number or type of arguments for <=.") 

        -- >= tests
    test ">= runSExpression Test 1" (runSExpression $ S.List [S.Symbol ">=", S.Integer 7, S.Integer 6])
      (R.Success $ S.Boolean True) 

    test ">= runSExpression  Test 2" (runSExpression $ S.List [S.Symbol ">=", S.Integer 6, S.Integer 7])
      (R.Success $ S.Boolean False)
    
    test ">= runSExpression  Test 3" (runSExpression $ S.List [S.Symbol ">=", S.Real 6.8, S.Real 6.3])
      (R.Success $ S.Boolean True)
    
    test ">= runSExpression  Test 4" (runSExpression $ S.List [S.Symbol ">=", S.Boolean True, S.Real 6.3])
      (fail "Wrong number or type of arguments for >=.")
    
    test ">= runSExpression Test 5" (runSExpression $ S.List [S.Symbol ">=", S.List[S.Symbol "+", S.Integer 7, 
       S.Integer 6], S.Symbol "x"])
      (fail "Variable x not defined.") 
        
    test ">= runSExpression >= Test 6" (runSExpression $ S.List [S.Symbol ">=", S.List [S.Symbol "if", S.Boolean True, 
       S.Boolean True, S.Boolean False], S.List[S.Symbol "let", S.List [S.Symbol "v", S.Real 6.3], S.Real 6.3]])   
     (fail "Wrong number or type of arguments for >=.")     

    -- // Cond and Else tests
    test "Cond runSExpression Test 1" (runSExpression $ S.List[S.Symbol "cond", S.List[S.List[S.Boolean True, 
        S.List[S.Symbol "+", S.Integer 3, S.Integer 2]]], S.Symbol "Nothing"])
        (R.Success $ S.Integer 5)

    test "Cond runSExpression Test 2" (runSExpression $ S.List[S.Symbol "cond", S.List[S.List[S.Boolean False, 
        S.List[S.Symbol "-", S.Integer 3, S.Integer 2]], S.List[S.Boolean True, 
          S.List[S.Symbol "+", S.Integer 3, S.Integer 1]]], S.Symbol "Nothing"])
        (R.Success $ S.Integer 4)
        
    test "Cond runSExpression Test 3" (runSExpression $ S.List[S.Symbol "cond", S.List[S.List[S.Boolean False, 
        S.List[S.Symbol "-", S.Integer 3, S.Integer 2]], S.List[S.Boolean False, 
          S.List[S.Symbol "+", S.Integer 3, S.Integer 1]]],
           S.List[S.Symbol "/", S.Integer 3, S.Integer 1]])
        (R.Success $ S.Integer 3)

    test "Cond runSExpression Test 4" (runSExpression $ S.List[S.Symbol "cond", S.List[S.List[S.Boolean False, 
        S.List[S.Symbol "-", S.Integer 3, S.Integer 2]], S.List[S.Boolean True, 
          S.List[S.Symbol "+", S.Integer 3, S.Integer 1]]], S.List[S.Symbol "/", S.Integer 3, S.Integer 1]])
        (R.Success $ S.Integer 4)

    test "Cond runSExpression Test 5" (runSExpression $ S.List[S.Symbol "cond", S.List[S.List[S.Real 5.3, 
        S.List[S.Symbol "+", S.Integer 3, S.Integer 2]]], S.Symbol "Nothing"])
        (fail "Cond clause was not a boolean.")  

    test "Cond runSExpression Test 6" (runSExpression $ S.List[S.Symbol "cond", S.List[S.List[S.Integer 1, 
        S.List[S.Symbol "-", S.Integer 3, S.Integer 2]], S.List[S.Boolean False, 
          S.List[S.Symbol "+", S.Integer 3, S.Integer 1]]], S.List[S.Symbol "/", S.Integer 3, S.Integer 1]])
        (fail "Cond clause was not a boolean.")  
    
    -- // Complex Boolean tests
    test "Not runSExpression complex Test 1" (runSExpression $ S.List [
        S.Symbol "not" , S.List [S.Symbol "or", S.Boolean True, S.Boolean True]]) 
        (R.Success $ S.Boolean False)

    test "Not runSExpression complex Test 2" (runSExpression $ S.List [
        S.Symbol "not" , S.List [S.Symbol "and", S.Boolean True, S.Boolean True]]) 
        (R.Success $ S.Boolean False)

    test "Not runSExpression complex Test 3" (runSExpression $ S.List [
        S.Symbol "and" , S.List [S.Symbol "not", S.Boolean True], 
          S.List [S.Symbol "or", S.Boolean False, S.Boolean True]]) 
        (R.Success $ S.Boolean False) 

     -- // Pair Tests 

    test "Pair runSExpression Test 1" (runSExpression $ S.List [
       S.Symbol "pair", S.Integer 10, S.Real 11.1
     ]) (R.Success $ S.Dotted (S.Integer 10) (S.Real 11.1))  

    test "Pair runSExpression Test 2" (runSExpression $ S.List [
       S.Symbol "pair", S.List [S.Symbol "pair", S.Integer 15, S.Boolean True],
        S.Real 11.1]) 
        (R.Success $ S.Dotted (S.Dotted (S.Integer 15) (S.Boolean True)) (S.Real 11.1))   

    -- // Left Tests 

    test "Left runSExpression Test 1" (runSExpression $ S.List [
      S.Symbol "left", S.Integer 10]) (fail "Left not applied to pair.")   

    test "Left runSExpression Test 2" (runSExpression $ S.List [
      S.Symbol "left", S.List [S.Symbol "pair", S.Real 5.5, S.Integer 10]]) 
       (R.Success (S.Real 5.5))    

    test "Left runSExpression Test 3" (runSExpression $ S.List [S.Symbol "left", 
      S.List [S.Symbol "left", S.List [
       S.Symbol "pair", S.List [S.Symbol "pair", S.Integer 15, S.Boolean True],
        S.Real 11.1]]])
        (R.Success $ S.Integer 15)   

    -- // Right Tests 

    test "Right runSExpression Test 1" (runSExpression $ S.List [
      S.Symbol "right", S.Integer 10]) (fail "Right not applied to pair.")  

    test "Right runSExpression Test 2" (runSExpression $ S.List [
      S.Symbol "right", S.List [S.Symbol "pair", S.Real 5.5, S.Integer 10]]) 
       (R.Success (S.Integer 10))    

    test "Right runSExpression Test 3" (runSExpression $ S.List [S.Symbol "right", 
      S.List [S.Symbol "right", S.List [
       S.Symbol "pair", S.Real 11.1 , 
        S.List [S.Symbol "pair", S.Integer 15, S.Boolean True]]]])
        (R.Success $ S.Boolean True)     

    --Real_Pred tests

    test "Real? runSExpression test  1" (runSExpression $ S.List[(S.Symbol "real?"), (S.Integer 1)]) (R.Success $ S.Boolean False)

    test "Real? runSExpression test 2" (runSExpression $ S.List[(S.Symbol "real?"), (S.Real 1.0)]) (R.Success $ S.Boolean True)
    
    test "Real? runSExpression test 3" (runSExpression $ S.List[(S.Symbol "real?"), (S.Boolean True)]) (R.Success $ S.Boolean False)
    
    test "Real? runSExpression test 4" (runSExpression $ S.List[(S.Symbol "real?"), (S.List[S.Symbol "right", 
     (S.List[S.Symbol "pair", (S.List[S.Symbol "+", (S.Integer 2), (S.Integer 1)]), (S.Integer 4)])])])
     (R.Success $ S.Boolean False)
    
     --Integer_Pred tests

    test "Integer? runSExpression test 1" (runSExpression $ S.List[(S.Symbol "integer?"), (S.Integer 1)]) (R.Success $ S.Boolean True)

    test "Integer? runSExpression test 2" (runSExpression $ S.List[(S.Symbol "integer?"), (S.Real 1.0)]) (R.Success $ S.Boolean False)
    
    test "Integer? runSExpression test 3" (runSExpression $ S.List[(S.Symbol "integer?"), (S.Boolean True)]) (R.Success $ S.Boolean False)
    
    test "Integer? runSExpression test 4" (runSExpression $ S.List[(S.Symbol "integer?"), (S.List[S.Symbol "right", 
     (S.List[S.Symbol "pair", (S.List[S.Symbol "+", (S.Integer 2), (S.Integer 1)]), (S.Integer 4)])])])
     (R.Success $ S.Boolean True)

    --Number_Pred tests

    test "Number? runSExpression test 1" (runSExpression $ S.List[(S.Symbol "number?"), (S.Integer 1)]) (R.Success $ S.Boolean True)

    test "Number? runSExpression test 2" (runSExpression $ S.List[(S.Symbol "number?"), (S.Real 1.0)]) (R.Success $ S.Boolean True)
    
    test "Number? runSExpression test 3" (runSExpression $ S.List[(S.Symbol "number?"), (S.Boolean True)]) (R.Success $ S.Boolean False)
    
    test "Number? runSExpression test 4" (runSExpression $ S.List[(S.Symbol "number?"), (S.List[S.Symbol "right", 
     (S.List[S.Symbol "pair", (S.List[S.Symbol "+", (S.Integer 2), (S.Integer 1)]), (S.Integer 4)])])])
     (R.Success $ S.Boolean True)

    --Boolean_Pred tests

    test "Boolean? runSExpression test 1" (runSExpression $ S.List[(S.Symbol "boolean?"), (S.Integer 1)]) (R.Success $ S.Boolean False)

    test "Boolean? runSExpression test 2" (runSExpression $ S.List[(S.Symbol "boolean?"), (S.Real 1.0)]) (R.Success $ S.Boolean False)
    
    test "Boolean? runSExpression test 3" (runSExpression $ S.List[(S.Symbol "boolean?"), (S.Boolean True)]) (R.Success $ S.Boolean True) 
    
    test "Boolean? runSExpression test 4" (runSExpression $ S.List[(S.Symbol "boolean?"), (S.List[S.Symbol "right", 
     (S.List[S.Symbol "pair", (S.List[S.Symbol "+", (S.Integer 2), (S.Integer 1)]), (S.Integer 4)])])])
     (R.Success $ S.Boolean False)

    --Pair_Pred tests

    test "Pair? runSExpression test 1" (runSExpression $ S.List[(S.Symbol "pair?"), (S.Integer 1)]) (R.Success $ S.Boolean False)

    test "Pair? runSExpression test 2" (runSExpression $ S.List[(S.Symbol "pair?"), (S.Real 1.0)]) (R.Success $ S.Boolean False)
    
    test "Pair? runSExpression test 3" (runSExpression $ S.List[(S.Symbol "pair?"), (S.Boolean True)]) (R.Success $ S.Boolean False)
    
    test "Pair? runSExpression test 4" (runSExpression $ S.List[(S.Symbol "pair?"), (S.List[S.Symbol "right", 
     (S.List[S.Symbol "pair", (S.List[S.Symbol "+", (S.Integer 2), (S.Integer 1)]), (S.Integer 4)])])])
     (R.Success $ S.Boolean False)

    test "Pair? runSExpression test 5" (runSExpression $ S.List[S.Symbol "pair?", S.List[S.Symbol "pair", (S.Integer 1), (S.Integer 2)]])
     (R.Success $ S.Boolean True)    

    -- Program tests 

    test "Program runSExpression test 2 one defun " (runSExpression sexpr_ex1) (R.Success $ S.Integer 4) 

    test "Program runSExpression test 3 two defuns" (runSExpression sexpr_ex1B) (R.Success $ S.Integer 6) 

    test "Program runSExpression test 4 one defun with Let " (runSExpression sexpr_ex3) (R.Success $ S.Integer 21) 

    test "Program runSExpression test 5 one define" (runSExpression sexpr_ex4) (R.Success $ S.Integer 9) 


-- =====================================================================

-- Function that takes in a list of SExprs in the form of a program and evaluates it. 
runProgram :: [S.Expr] -> R.Result S.Expr 
runProgram x = case (evalProgram (programFromSExpression (S.List [S.Symbol "Program", S.List x]))) of 
                     R.Success s -> return (valueToSExpression s)
                     R.Failure f -> fail f  

-- Helper function for getting rid of the result for the tests of runProgram
runProgramTestHelper :: (R.Result [S.Expr]) -> [S.Expr]
runProgramTestHelper (R.Success x)= x 
runProgramTestHelper (R.Failure f) = []

--tests runProgram
test_runProgram = do 
     test "runProgram 1" (runProgram (runProgramTestHelper (unsafePerformIO (P.fromFile "example1.pss")))) (R.Success (S.Dotted (S.Boolean False) (S.Boolean True)))   
     test "runProgram 2" (runProgram (runProgramTestHelper (unsafePerformIO (P.fromFile "example2.pss")))) (R.Success (S.Dotted (S.Integer 22) (S.Real (-5.0))))   
     test "runProgram 3" (runProgram (runProgramTestHelper (unsafePerformIO (P.fromFile "example3.pss")))) (R.Success (S.Integer 55)) 
     test "runProgram 4" (runProgram (runProgramTestHelper (unsafePerformIO (P.fromFile "example4.pss")))) (R.Success (S.Integer 11))               
     test "runProgram 5" (runProgram (runProgramTestHelper (unsafePerformIO (P.fromFile "example5.pss")))) (R.Success (S.Dotted (S.Integer (-24)) (S.Integer 24)))   
     test "runProgram 6" (runProgram (runProgramTestHelper (unsafePerformIO (P.fromFile "example6.pss")))) (R.Success (S.Dotted (S.Integer 87) (S.Integer 509)))   