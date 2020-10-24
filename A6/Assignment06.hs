{- |
Module : Assignment05
Description : Assignment 6 submission for CS 4400.
Copyright : (c) Michael Lanotte
                Rachel Johanek 
Maintainer : lanotte.m@northeastern.edu
             johanek.r@northeastern.edu 
-}
module Assignment06 where

import Maps 
import Syntax
import Eval
    ( test_checkFloatEquality,
      test_evalProgram,
      test_evalTupleListHelper,
      test_eval,
      test_substTupleListHelper,
      test_subst,
      test_runSExpression )
import Repl     


--the main function runs all tests associated witht the files Syntax.hs and Eval.hs
--this tests the functionality of all implemented methods involving converting between 
--SExpression and protoscheme, as well as Program and SExpression, as well as evaluating
--the values represented by protoscheme, Program, and SExpression data types
main_test :: IO () 
main_test = do 
    (print "Test fromSExpression and its helper")
    Syntax.test_fromSExpressionTupleListHelper
    Syntax.test_fromSExpression
    (print "Test toSExpression and its helper")
    Syntax.test_toSExpressionTupleListHelper
    Syntax.test_toSExpression
    (print "Test valueToSExpression")
    Syntax.test_valueToSExpression
    (print "Test programFromSExpression")
    Syntax.test_programFromSExpression
    (print "Test checkFloatEquality")
    Eval.test_checkFloatEquality
    (print "Test eval and its helper")
    Eval.test_evalTupleListHelper
    Eval.test_eval
    (print "Test subst and its helper")
    Eval.test_substTupleListHelper 
    Eval.test_subst 
    (print "Test runSExpression")
    Eval.test_runSExpression
    (print "Test evalProgram")
    Eval.test_evalProgram 
{-
-- Examples of input and output expected 
input_1 = (define x 10)
output_1 = Variable x defined.
Effect: x is saved in the enviroment with the definition 10

input_2 = (/ (* 100  14) (+ 10 1))
output_2 = 127

input_3 = (defun add-num (y) (+ x y))
output_3 = Function add-num defined
Effect: add-num is saved in the enviroment with the definition output = input + x

input_4 = (add-num (1))
input_4 = 11

input_5 = (defun add-num (x) (+ x x))
output_5 = Error: function add-num is already defined.

input_6 = (if (< 1 2) 1 2)
output_6 = 1

--Common errors users may run into from mistakes in their input
--lack of parentheses
input_err1 = / (* 100  14) (+ 10 1)
output_err1 = Parse error. Try again.

--missing space
input_err2 = (/ (*100 14) (+ 10 1))
output_err2 = Div (Call "*100" [Integer 14]) (Add (Integer 10) (Integer 1))
[("x",Define "x" (Integer 10))]
Evaluation error. Try again.

--operator not in prefix notation
input_err3 = ( (*100 14) / (+ 10 1))
output_err3 = Parse error. Try again.
-}

-- Main function for the assignment is to call the main repl function. The REPL function is
-- an interactive loop that "Reads", "Evaluates", and "Prints" to the interacting user in real
-- time. Our REPL evaluates mathematical expressions and stores variable and function definitions.
-- For further elaboration of the functionality of repl view the examples above and the repl 
-- purpose statement starting on line 17 of repl.hs
main :: IO ()
main = do
    putStrLn "Welcome to the ProtoScheme interactive REPL"
    repl Maps.empty
    return ()