{-|
Module      : Syntax
Description : Abstract syntax of protoScheme
Copyright   : (c) Ferd, 2020
                  Michael Lanotte, 2020
                  Rachel Johanek, 2020
Maintainer  : f.vesely@northeastern
              lanotte.m@northeastern.edu
              johanek.r@northeastern.edu

This module defines the abstract syntax of protoScheme and related functions.
-}
module Syntax where

import qualified SExpression as S

import SimpleTests (test)

--Data type respresenting an Integer, a Double, or a Boolean
--This is the return type of the eval function 
data ExprEval = Eval_Integer Integer 
              | Eval_Float Double
              | Eval_Boolean Bool 
              deriving(Eq, Show) 


-- |Variables are just strings
type Variable = String

{-
<Expr> ::= <Integer>
         | <Float>
         | <Boolean> 
         | <Variable>
         | (+ <Expr> <Expr>)
         | (- <Expr> <Expr>)
         | (* <Expr> <Expr>)
         | (/ <Expr> <Expr>)
         | (let (<Variable> <Expr>) <Expr>)
         | (if <Expr> <Expr> <Expr>)
         | (and <Expr> <Expr>)
         | (or <Expr> <Expr>)
         | (not <Expr>)  
         | (< <Expr> <Expr>)  
         | (> <Expr> <Expr>)
         | (= <Expr> <Expr>)
         | (cond (<Expr> <Expr>)* )
         | (cond (<Expr> <Expr>)* (else <Expr>))
-}

-- |protoScheme expressions
{- 
 Only need to add a Float pattern of type double into the protoScheme syntax. 
 But to make eval work, need eval to return either an Integer or a Double now. 
 To do this, need to use the Either term with Maybe Double and Maybe Integer
 And for that to work, subst needs to take in a Integer or Double now as well. 
 To do this, need to use the Either term with Double and Integer. 
 Considered making our own datatype to act as either a Integer or a Double but
 after researching more on Haskell and how Either worked, it made more sense
 to go with the data type that is already available. 
-}
{-
  For Assignment 4: 
  Added Boolean Bool line for part 1. 
  Added If line for part 2
  Added And, Or, and Not for part 3
  Added Less_Than, Greater_Than, and Equal for part 4
  Added Cond with Tuples and Else
-}
data Expr = Integer Integer
          | Float Double
          | Boolean Bool
          | Var Variable
          | Add Expr Expr
          | Sub Expr Expr
          | Mul Expr Expr
          | Div Expr Expr
          | Let Variable Expr Expr
          | If Expr Expr Expr 
          | And Expr Expr 
          | Or Expr Expr
          | Not Expr
          | Less_Than Expr Expr
          | Greater_Than Expr Expr
          | Equal_To Expr Expr
          | Cond [(Expr, Expr)]
          | Else 
          deriving (Eq, Show)
 

-- |Parse an s-expression and convert it into a protoScheme expression.
-- Need to have the S.Symbol x last to account for where there should be let because
-- pattern matching tells us that that symbol is not one of the four operation symbols. 
{-
  For Assignment 4:
  Added S.Boolean case for part 1
  Added If case for part 2
  Added And, Or, and Not cases for part 3
  Added Less_Than, Greater_Than, and Equal for part 4
  Added Cond and else case along with a helper for the tuple lists for part 5. 
-}
fromSExpression :: S.Expr -> Expr
fromSExpression (S.Integer i) = Integer i
fromSExpression (S.Boolean b) = Boolean b
fromSExpression (S.Real r) = Float r
fromSExpression (S.Symbol "Else") = Else
fromSExpression (S.Symbol s) = Var s
fromSExpression (S.List [S.Symbol "+", e1, e2]) =
    Add (fromSExpression e1) (fromSExpression e2)
fromSExpression (S.List [S.Symbol "-", e1, e2]) =
    Sub (fromSExpression e1) (fromSExpression e2)
fromSExpression (S.List [S.Symbol "*", e1, e2]) =
    Mul (fromSExpression e1) (fromSExpression e2)
fromSExpression (S.List [S.Symbol "/", e1, e2]) =
    Div (fromSExpression e1) (fromSExpression e2)
fromSExpression (S.List [S.Symbol "Let", S.Symbol x, e1, e2]) =
    Let x (fromSExpression e1) (fromSExpression e2)
fromSExpression (S.List [S.Symbol "If", e1, e2, e3]) =
    If (fromSExpression e1) (fromSExpression e2) (fromSExpression e3) 
fromSExpression (S.List [S.Symbol "And", e1, e2]) = 
    And (fromSExpression e1) (fromSExpression e2) 
fromSExpression (S.List [S.Symbol "Or", e1, e2]) = 
    Or (fromSExpression e1) (fromSExpression e2)   
fromSExpression (S.List [S.Symbol "Not", e]) = 
    Not (fromSExpression e)        
fromSExpression (S.List [S.Symbol "Less_Than", e1, e2]) = 
    Less_Than (fromSExpression e1) (fromSExpression e2)   
fromSExpression (S.List [S.Symbol "Greater_Than", e1, e2]) = 
    Greater_Than (fromSExpression e1) (fromSExpression e2)  
fromSExpression (S.List [S.Symbol "Equal_To", e1, e2]) = 
    Equal_To (fromSExpression e1) (fromSExpression e2)     
fromSExpression (S.List [S.Symbol "Cond", S.List x]) = 
    Cond (fromSExpressionTupleListHelper x)    

-- Function that assists the fromSExpression function by handling a list of 
-- the SExpr version of Expr tuples (Lists of two elements are the tuples)    
fromSExpressionTupleListHelper :: [S.Expr] -> [(Expr, Expr)] 
fromSExpressionTupleListHelper [] =  [] 
fromSExpressionTupleListHelper (S.List [t1, t2]:xs) = ((fromSExpression t1), (fromSExpression t2)) : fromSExpressionTupleListHelper xs       

-- Test that the helper function works correctly. 
test_fromSExpressionTupleListHelper = do 
    test "fromSExpressionTupleListHelper basic test" (fromSExpressionTupleListHelper []) [] 

    test "fromSExpressionTupleListHelper complex test 1" (fromSExpressionTupleListHelper [S.List [S.Integer 1, S.Integer 5]]) [(Integer 1, Integer 5)]

    test "fromSExpressionTupleListHelper complex test 2" 
     (fromSExpressionTupleListHelper [S.List [S.Integer 1, S.Integer 5], S.List [S.Boolean True, S.Real 5.5]]) 
     [(Integer 1, Integer 5), (Boolean True, Float 5.5)]

    test "fromSExpressionTupleHelper complex test 3" 
     (fromSExpressionTupleListHelper [S.List [S.Integer 1, S.Integer 5], S.List [S.Symbol "Else", S.Real 5.5]]) 
     [(Integer 1, Integer 5), (Else, Float 5.5)]   

test_fromSExpression = do
    
    test "fromSExpression Test Variable" (fromSExpression $ S.Symbol "v") (Var "v")

    -- Boolean tests
    
    test "Boolean fromSExpression t" (fromSExpression $ S.Boolean True) (Boolean True)

    test "Boolean fromSExpression f" (fromSExpression $ S.Boolean False ) (Boolean False)

    test "Boolean fromSExpression Test Add" (fromSExpression $ S.List [S.Symbol "+",
     S.Integer 4, S.Boolean True]) (Add (Integer 4) (Boolean True))

    test "Boolean fromSExpression Test Sub" (fromSExpression $ S.List [S.Symbol "-",
     S.Integer 4, S.Boolean False]) (Sub (Integer 4) (Boolean False))

    test "Boolean fromSExpression Test Mul" (fromSExpression $ S.List [S.Symbol "*",
     S.Integer 4, S.Boolean True]) (Mul (Integer 4) (Boolean True))

    test "Boolean fromSExpression Test Div" (fromSExpression $ S.List [S.Symbol "/",
     S.Integer 4, S.Boolean False]) (Div (Integer 4) (Boolean False))

    test "Boolean fromSExpression Test Nested Operations" (fromSExpression $ S.List [S.Symbol "/",
     S.List [S.Symbol "+", S.Integer 4, S.Boolean False], S.List [S.Symbol "-",
      S.Integer 4, S.Integer 10]]) (Div (Add (Integer 4) (Boolean False))
       (Sub (Integer 4) (Integer 10)))

    test "Boolean fromSExpression Test Let Simple" (fromSExpression $ S.List [S.Symbol "Let", S.Symbol "x",
     S.List [S.Symbol "+", S.Integer 10, S.Integer 4], S.List [S.Symbol "+", S.Symbol "x", S.Boolean True]])
     (Let "x" (Add (Integer 10) (Integer 4)) (Add (Var "x") (Boolean True)))

    test "Boolean fromSExpression Test Let Complex" (fromSExpression $ S.List [S.Symbol "Let", S.Symbol "y",
     S.List [S.Symbol "-", S.Integer 20, S.Boolean True], S.List [S.Symbol "Let", S.Symbol "x",
      S.List [S.Symbol "+", S.Symbol "y", S.Integer 4], S.List [S.Symbol "+",
       S.Symbol "x", S.Integer 1]]]) (Let "y" (Sub (Integer 20) (Boolean True))
       (Let "x" (Add (Var "y") (Integer 4)) (Add (Var "x") (Integer 1))))

    -- Integer tests   

    test "Integer fromSExpression 42" (fromSExpression $ S.Integer 42) (Integer 42)

    test "Integer fromSExpression Test Add" (fromSExpression $ S.List [S.Symbol "+",
     S.Integer 4, S.Integer 10]) (Add (Integer 4) (Integer 10))

    test "Integer fromSExpression Test Sub" (fromSExpression $ S.List [S.Symbol "-",
     S.Integer 4, S.Integer 10]) (Sub (Integer 4) (Integer 10))

    test "Integer fromSExpression Test Mul" (fromSExpression $ S.List [S.Symbol "*",
     S.Integer 4, S.Integer 10]) (Mul (Integer 4) (Integer 10))

    test "Integer fromSExpression Test Div" (fromSExpression $ S.List [S.Symbol "/",
     S.Integer 4, S.Integer 10]) (Div (Integer 4) (Integer 10))

    test "Integer fromSExpression Test Nested Operations" (fromSExpression $ S.List [S.Symbol "/",
     S.List [S.Symbol "+", S.Integer 4, S.Integer 10], S.List [S.Symbol "-",
      S.Integer 4, S.Integer 10]]) (Div (Add (Integer 4) (Integer 10))
       (Sub (Integer 4) (Integer 10)))

    test "Integer fromSExpression Test Let  Simple" (fromSExpression $ S.List [S.Symbol "Let", S.Symbol "x",
     S.List [S.Symbol "+", S.Integer 10, S.Integer 4], S.List [S.Symbol "+", S.Symbol "x", S.Integer 1]])
     (Let "x" (Add (Integer 10) (Integer 4)) (Add (Var "x") (Integer 1)))

    test "Integer fromSExpression Test Let Complex" (fromSExpression $ S.List [S.Symbol "Let", S.Symbol "y",
     S.List [S.Symbol "-", S.Integer 20, S.Integer 8], S.List [S.Symbol "Let", S.Symbol "x",
      S.List [S.Symbol "+", S.Symbol "y", S.Integer 4], S.List [S.Symbol "+",
       S.Symbol "x", S.Integer 1]]]) (Let "y" (Sub (Integer 20) (Integer 8))
       (Let "x" (Add (Var "y") (Integer 4)) (Add (Var "x") (Integer 1))))

    -- Real tests   

    test "Real fromSExpression 42" (fromSExpression $ S.Real 42.0) (Float 42.0)

    test "Real fromSExpression Test Add" (fromSExpression $ S.List [S.Symbol "+",
     S.Real 4.1, S.Real 10.1]) (Add (Float 4.1) (Float 10.1))

    test "Real fromSExpression Test Sub" (fromSExpression $ S.List [S.Symbol "-",
     S.Real 4.1, S.Real 10.1]) (Sub (Float 4.1) (Float 10.1))

    test "Real fromSExpression Test Mul" (fromSExpression $ S.List [S.Symbol "*",
     S.Real 4.1, S.Real 10.1]) (Mul (Float 4.1) (Float 10.1))

    test "Real fromSExpression Test Div" (fromSExpression $ S.List [S.Symbol "/",
     S.Real 4.1, S.Real 10.1]) (Div (Float 4.1) (Float 10.1))

    test "Real fromSExpression Test Nested Operations" (fromSExpression $ S.List [S.Symbol "/",
     S.List [S.Symbol "+", S.Real 4.1, S.Real 10.1], S.List [S.Symbol "-",
      S.Real 4.1, S.Real 10.1]]) (Div (Add (Float 4.1) (Float 10.1))
       (Sub (Float 4.1) (Float 10.1)))

    test "Real fromSExpression Test Let  Simple" (fromSExpression $ S.List [S.Symbol "Let", S.Symbol "x",
     S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]])
     (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1)))

    test "Real fromSExpression Test Let Complex" (fromSExpression $ S.List [S.Symbol "Let", S.Symbol "y",
     S.List [S.Symbol "-", S.Real 20.1, S.Real 8.1], S.List [S.Symbol "Let", S.Symbol "x",
      S.List [S.Symbol "+", S.Symbol "y", S.Real 4.1], S.List [S.Symbol "+",
       S.Symbol "x", S.Real 1.1]]]) 
       (Let "y" (Sub (Float 20.1) (Float 8.1))
       (Let "x" (Add (Var "y") (Float 4.1)) (Add (Var "x") (Float 1.1))))

    -- Mixed integer and real tests   

    test "Mixed fromSExpression 42" (fromSExpression $ S.Real 42.0) (Float 42.0)

    test "Mixed fromSExpression Test Add" (fromSExpression $ S.List [S.Symbol "+",
     S.Real 4.1, S.Real 10.1]) (Add (Float 4.1) (Float 10.1))

    test "Mixed fromSExpression Test Sub" (fromSExpression $ S.List [S.Symbol "-",
     S.Real 4.1, S.Real 10.1]) (Sub (Float 4.1) (Float 10.1))

    test "Mixed fromSExpression Test Mul" (fromSExpression $ S.List [S.Symbol "*",
     S.Real 4.1, S.Real 10.1]) (Mul (Float 4.1) (Float 10.1))

    test "Mixed fromSExpression Test Div" (fromSExpression $ S.List [S.Symbol "/",
     S.Real 4.1, S.Real 10.1]) (Div (Float 4.1) (Float 10.1))

    test "Mixed fromSExpression Test Nested Operations" (fromSExpression $ S.List [S.Symbol "/",
     S.List [S.Symbol "+", S.Real 4.1, S.Real 10.1], S.List [S.Symbol "-",
      S.Real 4.1, S.Real 10.1]]) (Div (Add (Float 4.1) (Float 10.1))
       (Sub (Float 4.1) (Float 10.1)))

    test "Mixed fromSExpression Test Let  Simple" (fromSExpression $ S.List [S.Symbol "Let", S.Symbol "x",
     S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]])
     (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1)))

    test "Mixed fromSExpression Test Let Complex" (fromSExpression $ S.List [S.Symbol "Let", S.Symbol "y",
     S.List [S.Symbol "-", S.Real 20.1, S.Real 8.1], S.List [S.Symbol "Let", S.Symbol "x",
      S.List [S.Symbol "+", S.Symbol "y", S.Real 4.1], S.List [S.Symbol "+",
       S.Symbol "x", S.Real 1.1]]]) (Let "y" (Sub (Float 20.1) (Float 8.1))
       (Let "x" (Add (Var "y") (Float 4.1)) (Add (Var "x") (Float 1.1))))   

   -- If tests
    test "If fromSExpression Test 1" (fromSExpression $ S.List [
        S.Symbol "If" , S.Boolean True, S.Integer 10, S.Real 15.1]) 
          (If (Boolean True) (Integer 10) (Float 15.1))   

    test "If fromSExpression Test 2" (fromSExpression $ S.List [
        S.Symbol "If" , S.Boolean False, S.Integer 10, S.List [S.Symbol "Let", S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
            (If (Boolean False) (Integer 10) (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1))))       

    test "If fromSExpression Test 3" (fromSExpression $ S.List [
        S.Symbol "If" , S.Boolean False, S.List [S.Symbol "If" , S.Boolean True, S.Integer 10, S.Real 15.1], 
         S.List [S.Symbol "Let", S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
            (If (Boolean False) (If (Boolean True) (Integer 10) (Float 15.1))
             (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1))))   

    -- And tests
    test "And fromSExpression Test 1" (fromSExpression $ S.List [
        S.Symbol "And" , S.Boolean True, S.Integer 10]) 
          (And (Boolean True) (Integer 10))   

    test "And fromSExpression Test 2" (fromSExpression $ S.List [
        S.Symbol "And" , S.Boolean False, S.List [S.Symbol "Let", S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
            (And (Boolean False) (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1))))       

    test "And fromSExpression Test 3" (fromSExpression $ S.List [
        S.Symbol "And" , S.List [S.Symbol "And" , S.Integer 10, S.Real 15.1], 
         S.List [S.Symbol "Let", S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
            (And (And (Integer 10) (Float 15.1))
             (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1))))    

    -- Or tests
    test "Or fromSExpression Test 1" (fromSExpression $ S.List [
        S.Symbol "Or" , S.Boolean True, S.Integer 10]) 
          (Or (Boolean True) (Integer 10))   

    test "Or fromSExpression Test 2" (fromSExpression $ S.List [
        S.Symbol "Or" , S.Boolean False, S.List [S.Symbol "Let", S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
            (Or (Boolean False) (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1))))       

    test "Or fromSExpression Test 3" (fromSExpression $ S.List [
        S.Symbol "Or" , S.List [S.Symbol "Or" , S.Integer 10, S.Real 15.1], 
         S.List [S.Symbol "Let", S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
            (Or (Or (Integer 10) (Float 15.1))
             (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1))))    

    -- Not tests
    test "Not fromSExpression Test 1" (fromSExpression $ S.List [
        S.Symbol "Not" , S.Boolean True]) 
          (Not (Boolean True))   

    test "Not fromSExpression Test 2" (fromSExpression $ S.List [
        S.Symbol "Not" , S.List [S.Symbol "Let", S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
            (Not (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1))))       

    test "Not fromSExpression Test 3" (fromSExpression $ S.List [
        S.Symbol "Not" , S.List [S.Symbol "Or" , S.Integer 10, 
         S.List [S.Symbol "Let", S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]]) 
            (Not (Or (Integer 10)
             (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1)))))    

    -- Less_Than tests
    test "fromSExpression Less_Than Test 1" (fromSExpression $ S.List [S.Symbol "Less_Than", S.Integer 7, S.Integer 6])
      (Less_Than (Integer 7) (Integer 6)) 

    test "fromSExpression Less_Than Test 2" (fromSExpression $ S.List [S.Symbol "Less_Than", S.Integer 6, S.Integer 7])
     (Less_Than (Integer 6) (Integer 7))
    
    test "fromSExpression Less_Than Test 3" (fromSExpression $ S.List [S.Symbol "Less_Than", S.Real 6.8, S.Real 6.3])
     (Less_Than (Float 6.8) (Float 6.3)) 
    
    test "fromSExpression Less_Than Test 4" (fromSExpression $ S.List [S.Symbol "Less_Than", S.Boolean True, S.Real 6.3])
     (Less_Than (Boolean True) (Float 6.3))
    
    test "fromSExpression Less_Than Test 5" (fromSExpression $ S.List [S.Symbol "Less_Than", S.List [S.Symbol "+", S.Integer 7, 
       S.Integer 6], S.Symbol "x"])
      (Less_Than (Add (Integer 7) (Integer 6)) (Var "x"))
        
    test "fromSExpression Less_Than Test 6" (fromSExpression $ S.List [S.Symbol "Less_Than", S.List [S.Symbol "If", S.Boolean True, 
       S.Boolean True, S.Boolean False], S.List [S.Symbol "Let", S.Symbol "v", S.Real 6.3, S.Real 6.3]])   
      (Less_Than (If (Boolean True) (Boolean True) (Boolean False)) (Let "v" (Float 6.3) (Float 6.3))) 

     -- Greater_Than tests
    test "fromSExpression Greater_Than Test 1" (fromSExpression $ S.List [S.Symbol "Greater_Than", S.Integer 7, S.Integer 6])
      (Greater_Than (Integer 7) (Integer 6)) 

    test "fromSExpression Greater_Than Test 2" (fromSExpression $ S.List [S.Symbol "Greater_Than", S.Integer 6, S.Integer 7])
     (Greater_Than (Integer 6) (Integer 7))
    
    test "fromSExpression Greater_Than Test 3" (fromSExpression $ S.List [S.Symbol "Greater_Than", S.Real 6.8, S.Real 6.3])
     (Greater_Than (Float 6.8) (Float 6.3)) 
    
    test "fromSExpression Greater_Than Test 4" (fromSExpression $ S.List [S.Symbol "Greater_Than", S.Boolean True, S.Real 6.3])
     (Greater_Than (Boolean True) (Float 6.3))
    
    test "fromSExpression Greater_Than Test 5" (fromSExpression $ S.List [S.Symbol "Greater_Than", S.List[S.Symbol "+", S.Integer 7, 
       S.Integer 6], S.Symbol "x"])
      (Greater_Than (Add (Integer 7) (Integer 6)) (Var "x"))
        
    test "fromSExpression Greater_Than Test 6" (fromSExpression $ S.List [S.Symbol "Greater_Than", S.List [S.Symbol "If", S.Boolean True, 
       S.Boolean True, S.Boolean False], S.List[S.Symbol "Let", S.Symbol "v", S.Real 6.3, S.Real 6.3]])   
     (Greater_Than (If (Boolean True) (Boolean True) (Boolean False)) (Let "v" (Float 6.3) (Float 6.3)))                                   

    -- Equal_To tests
    test "fromSExpression Equal_To Test 1" (fromSExpression $ S.List [S.Symbol "Equal_To", S.Integer 7, S.Integer 6])
      (Equal_To (Integer 7) (Integer 6)) 

    test "fromSExpression Equal_To Test 2" (fromSExpression $ S.List [S.Symbol "Equal_To", S.Integer 6, S.Integer 7])
     (Equal_To (Integer 6) (Integer 7))
    
    test "fromSExpression Equal_To Test 3" (fromSExpression $ S.List [S.Symbol "Equal_To", S.Real 6.8, S.Real 6.3])
     (Equal_To (Float 6.8) (Float 6.3)) 
    
    test "fromSExpression Equal_To Test 4" (fromSExpression $ S.List [S.Symbol "Equal_To", S.Boolean True, S.Real 6.3])
     (Equal_To (Boolean True) (Float 6.3))
    
    test "fromSExpression Equal_To Test 5" (fromSExpression $ S.List [S.Symbol "Equal_To", S.List[S.Symbol "+", S.Integer 7, 
       S.Integer 6], S.Symbol "x"])
      (Equal_To (Add (Integer 7) (Integer 6)) (Var "x"))
        
    test "fromSExpression Equal_To Test 6" (fromSExpression $ S.List [S.Symbol "Equal_To", S.List [S.Symbol "If", S.Boolean True, 
       S.Boolean True, S.Boolean False], S.List[S.Symbol "Let", S.Symbol "v", S.Real 6.3, S.Real 6.3]])   
     (Equal_To (If (Boolean True) (Boolean True) (Boolean False)) (Let "v" (Float 6.3) (Float 6.3)))    
     
    -- Cond tests 
    test "fromSExpression Cond  basic test" (fromSExpression $ S.List [S.Symbol "Cond", S.List []]) (Cond []) 

    test "fromSExpression Cond complex test 1" (fromSExpression $ S.List [S.Symbol "Cond", S.List [S.List [S.Integer 1, S.Integer 5]]]) 
     (Cond [(Integer 1, Integer 5)]) 

    test "fromSExpression Cond complex test 2" (fromSExpression $ S.List [S.Symbol "Cond", S.List [
     S.List [S.Integer 1, S.Integer 5], S.List [S.Boolean True, S.Real 5.5]]]) 
       (Cond [(Integer 1, Integer 5), (Boolean True, Float 5.5)])

    test "fromSExpression Cond with an else" (fromSExpression $ S.List [S.Symbol "Cond", S.List [
     S.List [S.Integer 1, S.Integer 5], S.List [S.Symbol "Else", S.Real 5.5]]]) 
       (Cond [(Integer 1, Integer 5), (Else, Float 5.5)])                                   

-- ================================================================================================

{-
  For Assignment 4:
  Added S.Boolean case for part 1
  Added If case for part 2
  Added And, Or, and Not cases for part 3
  Added Less_Than, Greater_Than, and Equal for part 4
  Added Cond and else case along with a helper for the tuple lists for part 5. 
-}

-- |Convert a protoScheme expression into its s-expression representation
toSExpression :: Expr -> S.Expr
toSExpression (Integer i) = S.Integer i 
toSExpression (Boolean b) = S.Boolean b
toSExpression (Float f) = S.Real f 
toSExpression (Var v) = S.Symbol v 
toSExpression (Add x y) = S.List [S.Symbol "+", toSExpression x, toSExpression y]
toSExpression (Sub x y) = S.List [S.Symbol "-", toSExpression x, toSExpression y]
toSExpression (Mul x y) = S.List [S.Symbol "*", toSExpression x, toSExpression y]
toSExpression (Div x y) = S.List [S.Symbol "/", toSExpression x, toSExpression y]
toSExpression (Let v x y) = S.List [S.Symbol "Let", S.Symbol v, toSExpression x, toSExpression y]
toSExpression (If x y z) = S.List [S.Symbol "If", toSExpression x, toSExpression y, toSExpression z]
toSExpression (And x y) = S.List [S.Symbol "And", toSExpression x, toSExpression y]
toSExpression (Or x y) = S.List [S.Symbol "Or", toSExpression x, toSExpression y]
toSExpression (Not x) = S.List [S.Symbol "Not", toSExpression x]
toSExpression (Less_Than x y) = S.List [S.Symbol "Less_Than", toSExpression x, toSExpression y]
toSExpression (Greater_Than x y) = S.List [S.Symbol "Greater_Than", toSExpression x, toSExpression y]
toSExpression (Equal_To x y) = S.List [S.Symbol "Equal_To", toSExpression x, toSExpression y]
toSExpression (Cond x) = S.List [S.Symbol "Cond", S.List (toSExpressionTupleListHelper x)]
toSExpression (Else) = S.Symbol "Else"

-- Function that assists the toSExpression function by handling a list of 
-- the Expr tuples and converting them to a list of S.Expr where a S.List [t1, t1] is how to represent a tuple.  
toSExpressionTupleListHelper :: [(Expr, Expr)] -> [S.Expr]
toSExpressionTupleListHelper [] = []
toSExpressionTupleListHelper ((t1, t2):ts) = S.List [toSExpression t1, toSExpression t2] : toSExpressionTupleListHelper ts

test_toSExpressionTupleListHelper = do 
    test "toSExpressionTupleListHelper basic test" (toSExpressionTupleListHelper []) [] 

    test "toSExpressionTupleListHelper complex test 1" (toSExpressionTupleListHelper [(Integer 1, Float 5.6)]) 
     [S.List [S.Integer 1, S.Real 5.6]]

    test "toSExpressionTupleListHelper complex test 2" (toSExpressionTupleListHelper 
     [(Integer 1, Float 5.6), (Boolean False, Boolean True)]) 
      [S.List [S.Integer 1, S.Real 5.6], S.List [S.Boolean False, S.Boolean True]] 

    test "toSExpressionTupleListHelper complex test 3" (toSExpressionTupleListHelper 
     [(Integer 1, Float 5.6), (Else , Boolean True)]) 
      [S.List [S.Integer 1, S.Real 5.6], S.List [S.Symbol "Else", S.Boolean True]]   

test_toSExpression = do

    test "toSExpression true" (toSExpression (Boolean True)) (S.Boolean True)
    test "toSExpression false" (toSExpression (Boolean False)) (S.Boolean False)
    test "toSExpression (Var x)" (toSExpression (Var "x")) (S.Symbol "x")

    --Base cases
    test "toSExpression (10)" (toSExpression (Integer 10)) (S.Integer 10)
    test "toSExpression (10.1)" (toSExpression (Float 10.1)) (S.Real 10.1)
    test "toSExpression (Var x)" (toSExpression (Var "x")) (S.Symbol "x")

    -- Basic Boolean tests
    test "toSExpression (+ True 14)"
        (toSExpression $ Add (Boolean True) (Integer 14))
        (S.List [S.Symbol "+", (S.Boolean True), (S.Integer 14)])
    test "toSExpression (- 32.1 False)"
        (toSExpression $ Sub (Float 32.1) (Boolean False))
        (S.List [S.Symbol "-", S.Real 32.1, S.Boolean False])
    test "toSExpression (* 10.2 True)"
        (toSExpression $ Mul (Float 10.2) (Boolean True))
        (S.List [S.Symbol "*", S.Real 10.2, S.Boolean True])
    test "toSExpression (/ False 5.6)"
        (toSExpression $ Div (Boolean False) (Float 5.6))
        (S.List [S.Symbol "/", S.Boolean False, S.Real 5.6])
    test "toSExpression (+ (* 10.2 False) (- True 2.1)"
        (toSExpression $ Add (Mul (Float 10.2) (Boolean False)) (Sub (Boolean True) (Float 2.1)))
        (S.List [S.Symbol "+", (S.List [S.Symbol "*", S.Real 10.2, S.Boolean False]),
          (S.List [S.Symbol "-", S.Boolean True, S.Real 2.1])])

    --Addition with Integers and Reals
    test "toSExpression (+ 32 14)"
        (toSExpression $ Add (Integer 32) (Integer 14))
        (S.List [S.Symbol "+", S.Integer 32, S.Integer 14])
    test "toSExpression (+ 32.1 14)"
        (toSExpression $ Add (Float 32.1) (Integer 14))
        (S.List [S.Symbol "+", S.Real 32.1, S.Integer 14])
    test "toSExpression (+ 32.1 14.5)"
        (toSExpression $ Add (Float 32.1) (Float 14.5))
        (S.List [S.Symbol "+", S.Real 32.1, S.Real 14.5])

    --Subtraction with Integers and Reals
    test "toSExpression (- 32 14)"
        (toSExpression $ Sub (Integer 32) (Integer 14))
        (S.List [S.Symbol "-", S.Integer 32, S.Integer 14])
    test "toSExpression (- 32.1 14)"
        (toSExpression $ Sub (Float 32.1) (Integer 14))
        (S.List [S.Symbol "-", S.Real 32.1, S.Integer 14])
    test "toSExpression (- 32.1 14.5)"
        (toSExpression $ Sub (Float 32.1) (Float 14.5))
        (S.List [S.Symbol "-", S.Real 32.1, S.Real 14.5])
    
    --Multiplication with Integers and Reals
    test "toSExpression (* 10 5)"
        (toSExpression $ Mul (Integer 10) (Integer 5))
        (S.List [S.Symbol "*", S.Integer 10, S.Integer 5])
    test "toSExpression (* 10.2 5)"
        (toSExpression $ Mul (Float 10.2) (Integer 5))
        (S.List [S.Symbol "*", S.Real 10.2, S.Integer 5])
    test "toSExpression (* 10.2 5.6)"
        (toSExpression $ Mul (Float 10.2) (Float 5.6))
        (S.List [S.Symbol "*", S.Real 10.2, S.Real 5.6])
    test "toSExpression (/ 10.2 5.6)"
        (toSExpression $ Div (Float 10.2) (Float 5.6))
        (S.List [S.Symbol "/", S.Real 10.2, S.Real 5.6])

    --Division with Integers and Reals
    test "toSExpression (/ 10 5)"
        (toSExpression $ Div (Integer 10) (Integer 5))
        (S.List [S.Symbol "/", S.Integer 10, S.Integer 5])
    test "toSExpression (/ 10.2 5)"
        (toSExpression $ Div (Float 10.2) (Integer 5))
        (S.List [S.Symbol "/", S.Real 10.2, S.Integer 5])
    test "toSExpression (/ 10.2 5.6)"
        (toSExpression $ Div (Float 10.2) (Float 5.6))
        (S.List [S.Symbol "/", S.Real 10.2, S.Real 5.6])

    --Nested functions with Integers and Reals
    test "toSExpression (/ (+ 10 10) (* 5 2)"
        (toSExpression (Div (Add (Integer 10) (Integer 10)) (Mul (Integer 5) (Integer 2))))
        (S.List [S.Symbol "/", (S.List [S.Symbol "+", S.Integer 10, S.Integer 10]),
          (S.List [S.Symbol "*", S.Integer 5, S.Integer 2])])
    test "toSExpression (/ (+ 10.2 10) (- 5 2.1)"
        (toSExpression $ Div (Add (Float 10.2) (Integer 10)) (Sub (Integer 5) (Float 2.1)))
        (S.List [S.Symbol "/", (S.List [S.Symbol "+", S.Real 10.2, S.Integer 10]),
          (S.List [S.Symbol "-", S.Integer 5, S.Real 2.1])])
    test "toSExpression (+ (* 10.2 10.8) (- 5.7 2.1)"
        (toSExpression $ Add (Mul (Float 10.2) (Float 10.8)) (Sub (Float 5.7) (Float 2.1)))
        (S.List [S.Symbol "+", (S.List [S.Symbol "*", S.Real 10.2, S.Real 10.8]),
          (S.List [S.Symbol "-", S.Real 5.7, S.Real 2.1])])

    -- Let tests
    test "toSExpression let x 0, 1 + x" (toSExpression (Let "x" (Integer 0) (Add (Integer 1) (Var "x")))) 
        (S.List[S.Symbol "Let", S.Symbol "x", S.Integer 0, (S.List[S.Symbol "+", S.Integer 1, S.Symbol "x"])])
        
    test "toSExpression let x 2, 1 + 3" (toSExpression (Let "x" (Integer 2) (Add (Integer 1) (Integer 3)))) 
        (S.List[S.Symbol "Let", S.Symbol "x", S.Integer 2, (S.List[S.Symbol "+", S.Integer 1, S.Integer 3])])
        
    test "toSExpression let y 1.5, 1 * y" (toSExpression (Let "y" (Float 1.5) (Mul (Integer 1) (Var "y")))) 
        (S.List[S.Symbol "Let", S.Symbol "y", S.Real 1.5, (S.List[S.Symbol "*", S.Integer 1, S.Symbol "y"])])
        
    test "toSExpression let y 3.2, 1 / y" (toSExpression (Let "y" (Float 3.2) (Div (Integer 1) (Var "y")))) 
        (S.List[S.Symbol "Let", S.Symbol "y", S.Real 3.2, (S.List[S.Symbol "/", S.Integer 1, S.Symbol "y"])])

    -- If tests 
    test "toSExpression if simple" 
        (toSExpression (If (Boolean True) (Integer 1) (Float 2.0)))
        (S.List [S.Symbol "If", S.Boolean True, S.Integer 1, S.Real 2.0])      
    test "toSExpression if complex 1" 
        (toSExpression (If (Boolean True) (Add (Integer 1) (Float 2.0)) (Var "x")))
        (S.List [S.Symbol "If", S.Boolean True, S.List [S.Symbol "+", S.Integer 1, S.Real 2.0], S.Symbol "x"])    
    test "toSExpression if complex 2" 
        (toSExpression (If (Boolean False) (Let "y" (Integer 1) (Var "y")) (Div (Integer 10) (Integer 2))))
        (S.List [S.Symbol "If", S.Boolean False, S.List [S.Symbol "Let", S.Symbol "y" , S.Integer 1, S.Symbol "y"], S.List [S.Symbol "/", S.Integer 10, S.Integer 2]])   

    -- And tests
    test "toSExpression And Test 1" (toSExpression $ (And (Boolean True) (Integer 10)))
      (S.List [S.Symbol "And" , S.Boolean True, S.Integer 10]) 
          
    test "toSExpression And Test 2" (toSExpression $ And (Boolean False) 
      (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1))))
        (S.List [S.Symbol "And" , S.Boolean False, S.List [S.Symbol "Let", S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]])
                 
    test "toSExpression And Test 3" (toSExpression $ (And (And (Integer 10) (Float 15.1))
      (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1))))) 
         (S.List [S.Symbol "And" , S.List [S.Symbol "And" , S.Integer 10, S.Real 15.1], 
          S.List [S.Symbol "Let", S.Symbol "x", S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], 
           S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
            

    -- Or tests
    test "toSExpression Or Test 1" (toSExpression $ (Or (Boolean True) (Integer 10)))
      (S.List [S.Symbol "Or" , S.Boolean True, S.Integer 10]) 
          
    test "toSExpression Or Test 2" (toSExpression $ Or (Boolean False) 
      (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1))))
        (S.List [S.Symbol "Or" , S.Boolean False, S.List [S.Symbol "Let", S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]])
                 
    test "toSExpression Or Test 3" (toSExpression $ (Or (Or (Integer 10) (Float 15.1))
      (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1))))) 
         (S.List [S.Symbol "Or" , S.List [S.Symbol "Or" , S.Integer 10, S.Real 15.1], 
          S.List [S.Symbol "Let", S.Symbol "x", S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], 
           S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]])    

    -- Not tests
    test "toSExpression Not Test 1" (toSExpression $ (Not (Boolean True))) 
      (S.List [S.Symbol "Not" , S.Boolean True]) 

    test "toSExpression Not Test 2" (toSExpression $  (Not (Let "x" (Add (Float 10.1) (Float 4.1)) 
      (Add (Var "x") (Float 1.1))))) (S.List [S.Symbol "Not" , S.List [S.Symbol "Let", S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]])  

    test "toSExpression Not Test 3" (toSExpression $ (Not (Or (Integer 10)
       (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1))))))     
         (S.List [S.Symbol "Not" , S.List [S.Symbol "Or" , S.Integer 10, S.List [S.Symbol "Let", S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]]) 

    -- Less_Than Tests
    test "toSExpression Less_Than Test 1" (toSExpression $ (Less_Than (Integer 7) (Integer 6))) 
        (S.List [S.Symbol "Less_Than", S.Integer 7, S.Integer 6]) 

    test "toSExpression Less_Than Test 2" (toSExpression $ (Less_Than (Integer 6) (Integer 7))) 
        (S.List [S.Symbol "Less_Than", S.Integer 6, S.Integer 7]) 
    
    test "toSExpression Less_Than Test 3" (toSExpression $ (Less_Than (Float 6.8) (Float 6.3))) 
        (S.List [S.Symbol "Less_Than", S.Real 6.8, S.Real 6.3])
    
    test "toSExpression Less_Than Test 4" (toSExpression $ (Less_Than (Boolean True) (Float 6.3))) 
        (S.List [S.Symbol "Less_Than", S.Boolean True, S.Real 6.3])
    
    test "toSExpression Less_Than Test 5" (toSExpression $ (Less_Than (Add (Integer 7) (Integer 6)) (Var "x"))) 
        (S.List [S.Symbol "Less_Than", S.List[S.Symbol "+", S.Integer 7, S.Integer 6], S.Symbol "x"])

    test "toSExpression Less_Than Test 6" (toSExpression $ (Less_Than (If (Boolean True) (Boolean True) (Boolean False))
        (Let "v" (Float 6.3) (Float 6.3)))) 
        (S.List [S.Symbol "Less_Than", S.List [S.Symbol "If", S.Boolean True, S.Boolean True, S.Boolean False],
          S.List[S.Symbol "Let", S.Symbol "v", S.Real 6.3, S.Real 6.3]])

  -- Greater_Than Tests
    test "toSExpression Greater_Than Test 1" (toSExpression $ (Greater_Than (Integer 7) (Integer 6))) 
        (S.List [S.Symbol "Greater_Than", S.Integer 7, S.Integer 6]) 

    test "toSExpression Greater_Than Test 2" (toSExpression $ (Greater_Than (Integer 6) (Integer 7))) 
        (S.List [S.Symbol "Greater_Than", S.Integer 6, S.Integer 7]) 
    
    test "toSExpression Greater_Than Test 3" (toSExpression $ (Greater_Than (Float 6.8) (Float 6.3))) 
        (S.List [S.Symbol "Greater_Than", S.Real 6.8, S.Real 6.3])
    
    test "toSExpression Greater_Than Test 4" (toSExpression $ (Greater_Than (Boolean True) (Float 6.3))) 
        (S.List [S.Symbol "Greater_Than", S.Boolean True, S.Real 6.3])
    
    test "toSExpression Greater_Than Test 5" (toSExpression $ (Greater_Than (Add (Integer 7) (Integer 6)) (Var "x"))) 
        (S.List [S.Symbol "Greater_Than", S.List[S.Symbol "+", S.Integer 7, S.Integer 6], S.Symbol "x"])

    test "toSExpression Greater_Than Test 6" (toSExpression $ (Greater_Than (If (Boolean True) (Boolean True) (Boolean False))
        (Let "v" (Float 6.3) (Float 6.3)))) 
        (S.List [S.Symbol "Greater_Than", S.List [S.Symbol "If", S.Boolean True, S.Boolean True, S.Boolean False],
          S.List[S.Symbol "Let", S.Symbol "v", S.Real 6.3, S.Real 6.3]])

 -- Equal To Tests
    test "toSExpression Equal_To Test 1" (toSExpression $ (Equal_To (Integer 7) (Integer 6))) 
        (S.List [S.Symbol "Equal_To", S.Integer 7, S.Integer 6]) 

    test "toSExpression Equal_To Test 2" (toSExpression $ (Equal_To (Integer 6) (Integer 7))) 
        (S.List [S.Symbol "Equal_To", S.Integer 6, S.Integer 7]) 
    
    test "toSExpression Equal_To Test 3" (toSExpression $ (Equal_To (Float 6.8) (Float 6.3))) 
        (S.List [S.Symbol "Equal_To", S.Real 6.8, S.Real 6.3])
    
    test "toSExpression Equal_To Test 4" (toSExpression $ (Equal_To (Boolean True) (Float 6.3))) 
        (S.List [S.Symbol "Equal_To", S.Boolean True, S.Real 6.3])
    
    test "toSExpression Equal_To Test 5" (toSExpression $ (Equal_To (Add (Integer 7) (Integer 6)) (Var "x"))) 
        (S.List [S.Symbol "Equal_To", S.List[S.Symbol "+", S.Integer 7, S.Integer 6], S.Symbol "x"])

    test "toSExpression Equal_To Test 6" (toSExpression $ (Equal_To (If (Boolean True) (Boolean True) (Boolean False))
        (Let "v" (Float 6.3) (Float 6.3)))) 
        (S.List [S.Symbol "Equal_To", S.List [S.Symbol "If", S.Boolean True, S.Boolean True, S.Boolean False],
          S.List[S.Symbol "Let", S.Symbol "v", S.Real 6.3, S.Real 6.3]])

  -- Cond Tests 
  
    test "toSExpression Cond basic test" (toSExpression (Cond [])) (S.List [S.Symbol "Cond", S.List []])

    test "toSExpression Cond complex test 1" (toSExpression (Cond [(Integer 1, Float 5.6)])) 
     (S.List [S.Symbol "Cond", S.List [S.List [S.Integer 1, S.Real 5.6]]])

    test "toSExpression Cond complex test 2" (toSExpression (Cond [(Integer 1, Float 5.6), (Boolean True, Integer 20)])) 
     (S.List [S.Symbol "Cond", S.List [S.List [S.Integer 1, S.Real 5.6], S.List [S.Boolean True, S.Integer 20]]]) 

    test "toSExpression Cond with an else" (toSExpression (Cond [(Integer 1, Float 5.6), (Else, Integer 20)])) 
     (S.List [S.Symbol "Cond", S.List [S.List [S.Integer 1, S.Real 5.6], S.List [S.Symbol "Else", S.Integer 20]]])          


-- |Convert an evaluation result into s-expression
valueToSExpression :: ExprEval -> S.Expr
valueToSExpression (Eval_Integer i) = S.Integer i
valueToSExpression (Eval_Float r) = S.Real r
valueToSExpression (Eval_Boolean b) = S.Boolean b

test_valueToSExpression = do
    test "toSExpression 42"
        (valueToSExpression (Eval_Integer 42))
        (S.Integer 42)
    test "toSExpression 42.3"
        (valueToSExpression (Eval_Float 42.3))
        (S.Real 42.3)
    test "toSExpression 20"
        (valueToSExpression (Eval_Integer 20))
        (S.Integer 20)
    test "toSExpression 51.9"
        (valueToSExpression (Eval_Float 51.9))
        (S.Real 51.9)
    test "toSExpression True"
        (valueToSExpression (Eval_Boolean True))
        (S.Boolean True)
    test "toSExpression False"
        (valueToSExpression (Eval_Boolean False))
        (S.Boolean False)

