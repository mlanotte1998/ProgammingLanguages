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

-- Main function for the assignment is to call the main repl function. 
main :: IO ()
main = do
    putStrLn "Welcome to the ProtoScheme interactive REPL"
    repl Maps.empty
    return ()