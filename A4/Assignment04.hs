{- |
Module : Assignment04
Description : Assignment 4 submission for CS 4400.
Copyright : (c) Michael Lanotte
                Rachel Johanek 
Maintainer : lanotte.m@northeastern.edu
             johanek.r@northeastern.edu 
-}
module Assignment04 where


import Syntax
import Eval

    -- Examples of If and Cond being equal, also look at eval tests to see how these equate to the same thing. 
    -- ifexp1 = If (Boolean True) (Add (Integer 5) (Integer 2)) (Sub (Integer 5) (Integer 2))
    -- condexp1 = Cond [(Boolean True, (Add (Integer 5) (Integer 2))), (Else, (Sub (Integer 5) (Integer 2)))]
    -- ifexp2 = If (Boolean False) (Add (Integer 5) (Integer 2))) (If (Boolean True) (Sub (Integer 5) (Integer 2)) 
    --     (Mul (Integer 5) (Integer 2))))
    -- condexp2 = Cond [(Boolean False, (Add (Integer 5) (Integer 2))), (Boolean True, (Sub (Integer 5) (Integer 2))),
    --      (Else, (Mul (Integer 5) (Integer 2)))]

{- 
 5 Question A. 
    Any Cond could be expressed using if statements: 'if' with the first Expr of the current list tuple can be represented
    as e1 of the 'if', the second Expr is the e2 of the 'if'. Then, if there is another element in the list, another 'if' with this
    same pattern, it will be represented by the e3. If you are at the end of the list, then e3 is Nothing. If you give the 'if' a 
    completely empty list, then 'if' would just be 'if True Nothing Nothing'. If there is an Else at the end, then you would have 
    that expression as the final e3 if the chain of 'if's.       

    Question B. Any Place where you have an else in a Cond, you could instead have a Boolean True because that way the 
    final Expr will always be evaluated if the others in the Cond list are not. So, in that way it could be considered redundant 
    because it can be expressed with the syntax already available through Cond. 
-} 

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