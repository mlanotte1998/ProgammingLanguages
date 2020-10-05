{- |
Module : Assignment03
Description : Assignment 3 submission for CS 4400.
Copyright : (c) Michael Lanotte
                Rachel Johanek 
Maintainer : lanotte.m@northeastern.edu
             johanek.r@northeastern.edu 
-}
module Assignment04 where


import Syntax
import Eval

main :: IO () 
main = do 
    (print "Test fromSExpression")
    Syntax.test_fromSExpression
    (print "Test toSExpression")
    Syntax.test_toSExpression
    (print "Test valueToSExpression")
    Syntax.test_valueToSExpression
    (print "Test checkFloatEquality")
    Eval.test_checkFloatEquality
    (print "Test eval")
    Eval.test_eval
    (print "Test subst") 
    Eval.test_subst 
    (print "Test runSExpression")
    Eval.test_runSExpression