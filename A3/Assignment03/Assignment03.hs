{- |
Module : Assignment03
Description : Assignment 3 submission for CS 4400.
Copyright : (c) Michael Lanotte
                Rachel Johanek 
Maintainer : lanotte.m@northeastern.edu
             johanek.r@northeastern.edu 
-}
module Assignment03 where


import Syntax
import Eval

main :: IO () 
main = do 
    Syntax.test_fromSExpression
    Syntax.test_toSExpression
    Syntax.test_valueToSExpression
    Eval.test_checkFloatEquality
    Eval.test_eval
    Eval.test_subst 
    Eval.test_runSExpression