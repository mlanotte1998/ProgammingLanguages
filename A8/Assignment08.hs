{- |
Module : Assignment08
Description : Assignment 8 submission for CS 4400.
Copyright : (c) Michael Lanotte
                Rachel Johanek 
Maintainer : lanotte.m@northeastern.edu
             johanek.r@northeastern.edu 
-}

module Assignment08 where

import Maps

import Syntax     

import Eval 

import Repl 



allTests :: IO () 
allTests = do 
    Syntax.test_fromSExpression
    Syntax.test_fromSExpressionTupleListHelper
    Syntax.test_programFromSExpression
    Syntax.test_valueToSExpression
    Syntax.test_toSExpression
    Syntax.test_toSExpressionTupleListHelper
    Eval.test_checkFloatEquality
    Eval.test_evalProgram
    Eval.test_eval
    Eval.test_evalTupleListHelper
    Eval.test_runSExpression
    Eval.test_runProgram

main :: IO ()
main = do
    putStrLn "Welcome to the ProtoScheme interactive REPL"
    repl Syntax.builtins
    return ()
