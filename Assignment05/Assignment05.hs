{- |
Module : Assignment04
Description : Assignment 5 submission for CS 4400.
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
    (print "Test fromSExpression and its helper")
    Syntax.test_fromSExpressionTupleListHelper
    Syntax.test_fromSExpression
    (print "Test toSExpression and its helper")
    Syntax.test_toSExpressionTupleListHelper
    Syntax.test_toSExpression
    (print "Test valueToSExpression")
    Syntax.test_valueToSExpression
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