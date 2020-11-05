{-|
Module     : Syntax
Description: Abstract syntax of protoScheme
Copyright  : (c) Ferd, 2020
                  Michael Lanotte, 2020
                  Rachel Johanek, 2020
Maintainer: f.vesely@northeastern
              lanotte.m@northeastern.edu
              johanek.r@northeastern.edu

This module defines the abstract syntax of protoScheme and related functions.
-}


module Syntax where

import qualified SExpression as S

import Maps (Map, get, set, empty)

import Prelude hiding (Left, Right)

import SimpleTestsColor (test)

--  ==========================================================================================================

--Data type respresenting an Integer, a Double, or a Boolean
--This is the return type of the eval function 
data ExprEval = Eval_Integer Integer
              | Eval_Float Double
              | Eval_Boolean Bool 
              | Eval_Pair ExprEval ExprEval
              deriving(Eq, Show) 


-- |Variables are just strings
type Variable = String

{-
--BNF Notation
<Expr> :: = <Integer>
         | <Float>
         | <Boolean> 
         | <Variable>
         | (<Pair> <Expr> <Expr>)
         | (left <Expr>)
         | (right <Expr>)
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
         | (real? <Expr>)
         | (integer? <Expr>)
         | (number? <Expr>)
         | (boolean? <Expr>)
         | (pair? <Expr>)
         | (<Variable> <Expr> <Expr>*)


<GlobalDef> ::= (defun <Variable> (<Variable> <Variable>*) <Expr>)
              | (define <Variable> <Expr>)

<Program> ::= <GlobalDef>* <Expr>

-}

 -- protoScheme expressions
 -- data type representing the expressions used by the syntax 
 -- in protoscheme 
data Expr = Integer Integer
          | Float Double
          | Boolean Bool
          | Var Variable
          | Pair Expr Expr
          | Left Expr
          | Right Expr
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
          | Cond [(Expr, Expr)] (Maybe Expr)
          | Real_Pred Expr 
          | Integer_Pred Expr
          | Number_Pred Expr
          | Boolean_Pred Expr
          | Pair_Pred Expr
          | Call Variable [Expr]
          deriving (Eq, Show)

-- | Program data type which is a sequence of global definitions
--   followed by a single expression
data Program = Program [GlobalDef] Expr
             deriving (Eq, Show)
-- | GlobalDef data type which can be either a function definiti  on, introduced
--    using defun, or a global variable definition, introduced using define
data GlobalDef = Defun Variable (Variable, [Variable]) Expr
               | Define Variable Expr
               deriving (Eq, Show)


-- |Environments are maps from Variables to values (Integers)
type Env = Map Variable ExprEval

-- |Outside of the environment, at a larger scope, is the global environment
--  values saved here are used if there is no value at the environment level
type GlobalEnv = Map Variable GlobalDef               
 
--  ================================================================================================

--Creates a Program representing the given SExpression
--Parses SExpression and converts it to the data type Program
programFromSExpression :: S.Expr -> Program 
programFromSExpression (S.List[S.Symbol "Program", S.List [], e]) = Program [] (fromSExpression e)
programFromSExpression (S.List[S.Symbol "Program", S.List[S.Symbol "define", S.Symbol var1, e1], e2]) =
  (Program [Define var1 (fromSExpression e1)] (fromSExpression e2))
programFromSExpression (S.List[S.Symbol "Program", S.List x, e]) = 
  (Program (listOfDefunToProgram x) (fromSExpression e))
programFromSExpression (S.List [S.List [S.Symbol "defun", s, list, f] , S.List (x:xs)]) = 
  (Program (listOfDefunToProgram [S.List [S.Symbol "defun", s, list, f]]) (fromSExpression (S.List [(S.Symbol "call"), x, S.List xs])))
    
-- fuck = programFromSExpression ((SExpression.List [List [Symbol "defun", Symbol "down", List [Symbol "n"],
--        List [Symbol "if", List [Symbol "=",Symbol "n",SExpression.Integer 1],Symbol "n", List [Symbol "down", 
--            List [Symbol "-",Symbol "n",SExpression.Integer 1]]]], List [Symbol "down", SExpression.Integer 5]]))


-- First go through the list defuns
listOfDefunToProgram :: [S.Expr] -> [GlobalDef]
listOfDefunToProgram [] = []
listOfDefunToProgram ((S.List[S.Symbol "defun", S.Symbol name, S.List args, e]):xs) = 
    Defun name (sExpressionArgsToProgramArgs args) (fromSExpression e) : listOfDefunToProgram xs
        -- then within those defuns, need to go through list of variables
        where 
             sExpressionArgsToProgramArgs :: [S.Expr] -> (Variable, [Variable])
             sExpressionArgsToProgramArgs ((S.Symbol x):xs) = (x, variableListFromSExprList xs)
            -- lastly need this helper to make the list part of the variable tuple
                 where 
                      variableListFromSExprList :: [S.Expr] -> [Variable] 
                      variableListFromSExprList [] = []
                      variableListFromSExprList ((S.Symbol x):xs) = x : variableListFromSExprList xs  

-- Examples of S-Expressions representing a variety of Programs, including simple and nested Programs
-- and programs including Defun and Define
sexpr_empty = S.List[S.Symbol "Program", S.List[], (S.Integer 5)]

sexpr_ex1 = S.List[S.Symbol "Program", S.List [S.List[S.Symbol "defun", S.Symbol "incr", S.List [S.Symbol "x"], 
  S.List[S.Symbol "+", S.Symbol "x", S.Integer 1]]], S.List[S.Symbol "call", S.Symbol "incr", 
    S.List [S.List [S.Symbol "call", S.Symbol "incr", S.List [
    S.List [S.Symbol "call", S.Symbol "incr", S.List [S.Integer 1]]]]]]]

sexpr_ex1B = S.List[S.Symbol "Program", S.List[S.List[S.Symbol "defun", S.Symbol "incr", S.List [S.Symbol "x"], 
  S.List[S.Symbol "+", S.Symbol "x", S.Integer 1]], 
   S.List [S.Symbol "Defun", S.Symbol "Plus", S.List [S.Symbol "x", S.Symbol "y"], 
    S.List [S.Symbol "+", S.Symbol "x", S.Symbol "y"]]], S.List[S.Symbol "call", S.Symbol "incr", 
    S.List [S.List [S.Symbol "call", S.Symbol "incr", S.List [
    S.List [S.Symbol "call", S.Symbol "Plus", S.List [S.Integer 1, S.Integer 3]]]]]]]    

sexpr_ex2 = S.List[S.Symbol "Program", S.List[S.List[S.Symbol "defun", S.Symbol "f", S.List[S.Symbol "x"], 
  S.List[S.Symbol "+", S.Symbol "x", S.Symbol "y"]]], S.List[S.Symbol "let", S.List [S.Symbol "y", S.Integer 10],
  S.List[S.Symbol "call", S.Symbol "f", S.List[S.Integer 10]]]]

sexpr_ex3 = S.List[S.Symbol "Program", S.List[S.List[S.Symbol "defun", S.Symbol "incr", S.List[S.Symbol "x"],
  S.List[S.Symbol "+", S.Symbol "x", S.Integer 1]]], S.List[S.Symbol "let", S.List [S.Symbol "z", S.Integer 20],
  S.List[S.Symbol "call", S.Symbol "incr", S.List[S.Symbol "z"]]]]

sexpr_ex4 = S.List[S.Symbol "Program", S.List[S.Symbol "define", S.Symbol "f", S.Integer 10], 
  S.List[S.Symbol "-", S.Symbol "f", S.Integer 1]]

sexpr_ex5 = S.List[S.Symbol "Program", S.List[S.Symbol "define", S.Symbol "Double", S.List[S.Symbol "pair", S.Integer 10, S.Integer 2]], 
  S.List[S.Symbol "pair", S.List[S.Symbol "*", S.Integer 2, S.List[S.Symbol "left", S.Symbol "Double"]],
  S.List[S.Symbol "*", S.Integer 2, S.List[S.Symbol "right", S.Symbol "Double"]]]] 

sexpr_ex6 = S.List[S.Symbol "Program", S.List[S.Symbol "define", S.Symbol "f", S.Integer 10], 
  S.List[S.Symbol "-", S.Symbol "f", S.Integer 1]]

sexpr_ex7 = S.List[S.Symbol "Program", S.List[S.Symbol "define", S.Symbol "p", S.List[S.Symbol "pair",
  S.Real 1.01, S.Boolean False]], S.List[S.Symbol "right", S.Symbol "p"]]

--Examples of the same Programs represented above but as their original Program data type
ex_program_mt = Program [] (Integer 5)

ex_program_1 = Program [Defun "incr" ("x", []) (Add (Var "x") (Integer 1))] 
                 (Call "incr" [(Call "incr" [(Call "incr" [(Integer 1)])])])

ex_program_1B = Program [Defun "incr" ("x", []) (Add (Var "x") (Integer 1)),
                         Defun "Plus" ("x", ["y"]) (Add (Var "x") (Var "y"))] 
                 (Call "incr" [(Call "incr" [(Call "Plus" [Integer 1, Integer 3])])])

ex_program_2 = Program [Defun "f" ("x", []) (Add (Var "x") (Var "y"))]
                 (Let "y" (Integer 10) (Call "f" [(Integer 10)]))

ex_program_3 = Program [Defun "incr" ("x", []) (Add (Var "x") (Integer 1))] 
                 (Let "z" (Integer 20) (Call "incr" [(Var "z")]))

ex_program_4 = Program [Define "f" (Integer 10)] (Sub (Var "f") (Integer 1))


--tests of programFromSExpression Defun
test_programFromSExpression = do
    test "programFromSExpression ex_empty test 1" (programFromSExpression sexpr_empty) (ex_program_mt)

    test "programFromSExpression ex1 test 2" (programFromSExpression sexpr_ex1) (ex_program_1)

    test "programFromSExpression ex1B test 3" (programFromSExpression sexpr_ex1B) (ex_program_1B)

    test "programFromSExpression ex2 test 4" (programFromSExpression sexpr_ex2) (ex_program_2)

    test "programFromSExpression ex3 test 5" (programFromSExpression sexpr_ex3) (ex_program_3)

    test "programFromSExpression ex4 test 6" (programFromSExpression sexpr_ex4) (ex_program_4)

--  =========================================================================================================

-- |Parse an s-expression and convert it into a protoScheme expression.
-- Need to have the S.Symbol x last to account for where there should be let because
-- pattern matching tells us that that symbol is not one of the four operation symbols. 
fromSExpression :: S.Expr -> Expr
fromSExpression (S.Integer i) = Integer i
fromSExpression (S.Boolean b) = Boolean b
fromSExpression (S.Real r) = Float r
fromSExpression (S.Symbol s) = Var s
fromSExpression (S.List[S.Symbol "left", e1]) = Left (fromSExpression e1)
fromSExpression (S.List[S.Symbol "right", e1]) = Right (fromSExpression e1)
fromSExpression (S.List[S.Symbol "pair", e1, e2]) = Pair (fromSExpression e1) (fromSExpression e2)
fromSExpression (S.List[S.Symbol "real?", e]) = Real_Pred (fromSExpression e)
fromSExpression (S.List[S.Symbol "integer?", e]) = Integer_Pred (fromSExpression e)
fromSExpression (S.List[S.Symbol "number?", e]) = Number_Pred (fromSExpression e)
fromSExpression (S.List[S.Symbol "boolean?", e]) = Boolean_Pred (fromSExpression e)
fromSExpression (S.List[S.Symbol "pair?", e]) = Pair_Pred (fromSExpression e)
fromSExpression (S.List[S.Symbol "call", S.Symbol x, S.List e]) = Call x (listFromSExpressionList e)
  where 
    -- Function for converting a list of S.Expr to a list of Expr. 
    listFromSExpressionList :: [S.Expr] -> [Expr]
    listFromSExpressionList [] = [] 
    listFromSExpressionList (x:xs) = (fromSExpression x) : (listFromSExpressionList xs)  
fromSExpression (S.List [S.Symbol "+", e1, e2]) =
    Add (fromSExpression e1) (fromSExpression e2)
fromSExpression (S.List [S.Symbol "-", e1, e2]) =
    Sub (fromSExpression e1) (fromSExpression e2)
fromSExpression (S.List [S.Symbol "*", e1, e2]) =
    Mul (fromSExpression e1) (fromSExpression e2)
fromSExpression (S.List [S.Symbol "/", e1, e2]) =
    Div (fromSExpression e1) (fromSExpression e2)
fromSExpression (S.List [S.Symbol "let", S.List [S.Symbol x, e1], e2]) =
    Let x (fromSExpression e1) (fromSExpression e2)
fromSExpression (S.List [S.Symbol "if", e1, e2, e3]) =
    If (fromSExpression e1) (fromSExpression e2) (fromSExpression e3) 
fromSExpression (S.List [S.Symbol "and", e1, e2]) = 
    And (fromSExpression e1) (fromSExpression e2) 
fromSExpression (S.List [S.Symbol "or", e1, e2]) = 
    Or (fromSExpression e1) (fromSExpression e2)   
fromSExpression (S.List [S.Symbol "not", e]) = 
    Not (fromSExpression e)        
fromSExpression (S.List [S.Symbol "<", e1, e2]) = 
    Less_Than (fromSExpression e1) (fromSExpression e2)   
fromSExpression (S.List [S.Symbol ">", e1, e2]) = 
    Greater_Than (fromSExpression e1) (fromSExpression e2)  
fromSExpression (S.List [S.Symbol "=", e1, e2]) = 
    Equal_To (fromSExpression e1) (fromSExpression e2)     
fromSExpression (S.List [S.Symbol "cond", S.List x, e]) = 
    Cond (fromSExpressionTupleListHelper x)  (handleElse e) 
        where 
            handleElse :: S.Expr -> Maybe Expr 
            handleElse (S.Symbol "Nothing") = Nothing 
            handleElse e = Just (fromSExpression e)
-- Added this in for the repl to handle the specific parsed calling of functions
-- example (g 10) turns into a list of g and 10 and so that needs to be a call of g with 10 as the argument.             
fromSExpression (S.List x)  = handleFunctionWithoutCall x 
       where 
             handleFunctionWithoutCall :: [S.Expr] -> Expr 
             handleFunctionWithoutCall ((S.Symbol s):y) = Call s (handleArgumentList y) 
                   where 
                     handleArgumentList :: [S.Expr] -> [Expr]
                     handleArgumentList [] = [] 
                     handleArgumentList (x:xs) = fromSExpression x : handleArgumentList xs
          


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
     (fromSExpressionTupleListHelper [S.List [S.Integer 1, S.Integer 5]]) 
     [(Integer 1, Integer 5)]   

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

    test "Boolean fromSExpression Test Let Simple" (fromSExpression $ S.List [S.Symbol "let", S.List [S.Symbol "x",
     S.List [S.Symbol "+", S.Integer 10, S.Integer 4]], S.List [S.Symbol "+", S.Symbol "x", S.Boolean True]])
     (Let "x" (Add (Integer 10) (Integer 4)) (Add (Var "x") (Boolean True)))

    test "Boolean fromSExpression Test Let Complex" (fromSExpression $ S.List [S.Symbol "let", S.List [S.Symbol "y",
     S.List [S.Symbol "-", S.Integer 20, S.Boolean True]], S.List [S.Symbol "let", S.List [S.Symbol "x",
      S.List [S.Symbol "+", S.Symbol "y", S.Integer 4]], S.List [S.Symbol "+",
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

    test "Integer fromSExpression Test Let  Simple" (fromSExpression $ S.List [S.Symbol "let", S.List [S.Symbol "x",
     S.List [S.Symbol "+", S.Integer 10, S.Integer 4]], S.List [S.Symbol "+", S.Symbol "x", S.Integer 1]])
     (Let "x" (Add (Integer 10) (Integer 4)) (Add (Var "x") (Integer 1)))

    test "Integer fromSExpression Test Let Complex" (fromSExpression $ S.List [S.Symbol "let", S.List [S.Symbol "y",
     S.List [S.Symbol "-", S.Integer 20, S.Integer 8]], S.List [S.Symbol "let", S.List [S.Symbol "x",
      S.List [S.Symbol "+", S.Symbol "y", S.Integer 4]], S.List [S.Symbol "+",
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

    test "Real fromSExpression Test Let  Simple" (fromSExpression $ S.List [S.Symbol "let", S.List [S.Symbol "x",
     S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]])
     (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1)))

    test "Real fromSExpression Test Let Complex" (fromSExpression $ S.List [S.Symbol "let", S.List [S.Symbol "y",
     S.List [S.Symbol "-", S.Real 20.1, S.Real 8.1]], S.List [S.Symbol "let", S.List [S.Symbol "x",
      S.List [S.Symbol "+", S.Symbol "y", S.Real 4.1]], S.List [S.Symbol "+",
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

    test "Mixed fromSExpression Test Let  Simple" (fromSExpression $ S.List [S.Symbol "let", S.List [S.Symbol "x",
     S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]])
     (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1)))

    test "Mixed fromSExpression Test Let Complex" (fromSExpression $ S.List [S.Symbol "let", S.List [S.Symbol "y",
     S.List [S.Symbol "-", S.Real 20.1, S.Real 8.1]], S.List [S.Symbol "let", S.List [S.Symbol "x",
      S.List [S.Symbol "+", S.Symbol "y", S.Real 4.1]], S.List [S.Symbol "+",
       S.Symbol "x", S.Real 1.1]]]) (Let "y" (Sub (Float 20.1) (Float 8.1))
       (Let "x" (Add (Var "y") (Float 4.1)) (Add (Var "x") (Float 1.1))))   

   -- If tests
    test "If fromSExpression Test 1" (fromSExpression $ S.List [
        S.Symbol "if" , S.Boolean True, S.Integer 10, S.Real 15.1]) 
          (If (Boolean True) (Integer 10) (Float 15.1))   

    test "If fromSExpression Test 2" (fromSExpression $ S.List [
        S.Symbol "if" , S.Boolean False, S.Integer 10, S.List [S.Symbol "let", S.List [S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
            (If (Boolean False) (Integer 10) (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1))))       

    test "If fromSExpression Test 3" (fromSExpression $ S.List [
        S.Symbol "if" , S.Boolean False, S.List [S.Symbol "if" , S.Boolean True, S.Integer 10, S.Real 15.1], 
         S.List [S.Symbol "let", S.List [S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
            (If (Boolean False) (If (Boolean True) (Integer 10) (Float 15.1))
             (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1))))   

    -- And tests
    test "And fromSExpression Test 1" (fromSExpression $ S.List [
        S.Symbol "and" , S.Boolean True, S.Integer 10]) 
          (And (Boolean True) (Integer 10))   

    test "And fromSExpression Test 2" (fromSExpression $ S.List [
        S.Symbol "and" , S.Boolean False, S.List [S.Symbol "let", S.List [S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
            (And (Boolean False) (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1))))       

    test "And fromSExpression Test 3" (fromSExpression $ S.List [
        S.Symbol "and" , S.List [S.Symbol "and" , S.Integer 10, S.Real 15.1], 
         S.List [S.Symbol "let", S.List [S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
            (And (And (Integer 10) (Float 15.1))
             (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1))))    

    -- Or tests
    test "Or fromSExpression Test 1" (fromSExpression $ S.List [
        S.Symbol "or" , S.Boolean True, S.Integer 10]) 
          (Or (Boolean True) (Integer 10))   

    test "Or fromSExpression Test 2" (fromSExpression $ S.List [
        S.Symbol "or" , S.Boolean False, S.List [S.Symbol "let", S.List [S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
            (Or (Boolean False) (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1))))       

    test "Or fromSExpression Test 3" (fromSExpression $ S.List [
        S.Symbol "or" , S.List [S.Symbol "or" , S.Integer 10, S.Real 15.1], 
         S.List [S.Symbol "let", S.List [S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
            (Or (Or (Integer 10) (Float 15.1))
             (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1))))    

    -- Not tests
    test "Not fromSExpression Test 1" (fromSExpression $ S.List [
        S.Symbol "not" , S.Boolean True]) 
          (Not (Boolean True))   

    test "Not fromSExpression Test 2" (fromSExpression $ S.List [
        S.Symbol "not" , S.List [S.Symbol "let", S.List [S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
            (Not (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1))))       

    test "Not fromSExpression Test 3" (fromSExpression $ S.List [
        S.Symbol "not" , S.List [S.Symbol "or" , S.Integer 10, 
         S.List [S.Symbol "let", S.List [S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]]) 
            (Not (Or (Integer 10)
             (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1)))))    

    -- Less_Than tests
    test "fromSExpression Less_Than Test 1" (fromSExpression $ S.List [S.Symbol "<", S.Integer 7, S.Integer 6])
      (Less_Than (Integer 7) (Integer 6)) 

    test "fromSExpression Less_Than Test 2" (fromSExpression $ S.List [S.Symbol "<", S.Integer 6, S.Integer 7])
     (Less_Than (Integer 6) (Integer 7))
    
    test "fromSExpression Less_Than Test 3" (fromSExpression $ S.List [S.Symbol "<", S.Real 6.8, S.Real 6.3])
     (Less_Than (Float 6.8) (Float 6.3)) 
    
    test "fromSExpression Less_Than Test 4" (fromSExpression $ S.List [S.Symbol "<", S.Boolean True, S.Real 6.3])
     (Less_Than (Boolean True) (Float 6.3))
    
    test "fromSExpression Less_Than Test 5" (fromSExpression $ S.List [S.Symbol "<", S.List [S.Symbol "+", S.Integer 7, 
       S.Integer 6], S.Symbol "x"])
      (Less_Than (Add (Integer 7) (Integer 6)) (Var "x"))
        
    test "fromSExpression Less_Than Test 6" (fromSExpression $ S.List [S.Symbol "<", S.List [S.Symbol "if", S.Boolean True, 
       S.Boolean True, S.Boolean False], S.List [S.Symbol "let", S.List [ S.Symbol "v", S.Real 6.3], S.Real 6.3]])   
      (Less_Than (If (Boolean True) (Boolean True) (Boolean False)) (Let "v" (Float 6.3) (Float 6.3))) 

     -- Greater_Than tests
    test "fromSExpression Greater_Than Test 1" (fromSExpression $ S.List [S.Symbol ">", S.Integer 7, S.Integer 6])
      (Greater_Than (Integer 7) (Integer 6)) 

    test "fromSExpression Greater_Than Test 2" (fromSExpression $ S.List [S.Symbol ">", S.Integer 6, S.Integer 7])
     (Greater_Than (Integer 6) (Integer 7))
    
    test "fromSExpression Greater_Than Test 3" (fromSExpression $ S.List [S.Symbol ">", S.Real 6.8, S.Real 6.3])
     (Greater_Than (Float 6.8) (Float 6.3)) 
    
    test "fromSExpression Greater_Than Test 4" (fromSExpression $ S.List [S.Symbol ">", S.Boolean True, S.Real 6.3])
     (Greater_Than (Boolean True) (Float 6.3))
    
    test "fromSExpression Greater_Than Test 5" (fromSExpression $ S.List [S.Symbol ">", S.List[S.Symbol "+", S.Integer 7, 
       S.Integer 6], S.Symbol "x"])
      (Greater_Than (Add (Integer 7) (Integer 6)) (Var "x"))
        
    test "fromSExpression Greater_Than Test 6" (fromSExpression $ S.List [S.Symbol ">", S.List [S.Symbol "if", S.Boolean True, 
       S.Boolean True, S.Boolean False], S.List[S.Symbol "let", S.List [S.Symbol "v", S.Real 6.3], S.Real 6.3]])   
     (Greater_Than (If (Boolean True) (Boolean True) (Boolean False)) (Let "v" (Float 6.3) (Float 6.3)))                                   

    -- Equal_To tests
    test "fromSExpression Equal_To Test 1" (fromSExpression $ S.List [S.Symbol "=", S.Integer 7, S.Integer 6])
      (Equal_To (Integer 7) (Integer 6)) 

    test "fromSExpression Equal_To Test 2" (fromSExpression $ S.List [S.Symbol "=", S.Integer 6, S.Integer 7])
     (Equal_To (Integer 6) (Integer 7))
    
    test "fromSExpression Equal_To Test 3" (fromSExpression $ S.List [S.Symbol "=", S.Real 6.8, S.Real 6.3])
     (Equal_To (Float 6.8) (Float 6.3)) 
    
    test "fromSExpression Equal_To Test 4" (fromSExpression $ S.List [S.Symbol "=", S.Boolean True, S.Real 6.3])
     (Equal_To (Boolean True) (Float 6.3))
    
    test "fromSExpression Equal_To Test 5" (fromSExpression $ S.List [S.Symbol "=", S.List[S.Symbol "+", S.Integer 7, 
       S.Integer 6], S.Symbol "x"])
      (Equal_To (Add (Integer 7) (Integer 6)) (Var "x"))
        
    test "fromSExpression Equal_To Test 6" (fromSExpression $ S.List [S.Symbol "=", S.List [S.Symbol "if", S.Boolean True, 
       S.Boolean True, S.Boolean False], S.List[S.Symbol "let", S.List [S.Symbol "v", S.Real 6.3], S.Real 6.3]])   
     (Equal_To (If (Boolean True) (Boolean True) (Boolean False)) (Let "v" (Float 6.3) (Float 6.3)))    
     
    -- Cond tests 
    test "fromSExpression Cond  basic test" (fromSExpression $ S.List [S.Symbol "cond", S.List [], S.Symbol "Nothing"]) (Cond [] Nothing) 

    test "fromSExpression Cond complex test 1" (fromSExpression $ S.List 
     [S.Symbol "cond", S.List [S.List [S.Integer 1, S.Integer 5]], S.Symbol "Nothing"]) 
     (Cond [(Integer 1, Integer 5)] Nothing) 

    test "fromSExpression Cond complex test 2" (fromSExpression $ S.List [S.Symbol "cond", S.List [
     S.List [S.Integer 1, S.Integer 5], S.List [S.Boolean True, S.Real 5.5]], S.Symbol "Nothing"]) 
       (Cond [(Integer 1, Integer 5), (Boolean True, Float 5.5)] Nothing)

    test "fromSExpression Cond with an else" (fromSExpression $ S.List [S.Symbol "cond", S.List [
     S.List [S.Integer 1, S.Integer 5]], (S.Real 5.5)]) 
       (Cond [(Integer 1, Integer 5)] (Just (Float 5.5)))    
    

    -- Pair tests

    test "fromSExpression Pair test 1" (fromSExpression $ S.List[S.Symbol "pair", (S.Integer 5), (S.Real 5.5)]) (Pair (Integer 5) (Float 5.5))                       

    test "fromSExpression Pair test 2" (fromSExpression $S.List[S.Symbol "pair", (S.Boolean True), (S.Real 5.5)]) (Pair (Boolean True) (Float 5.5))  

    test "fromSExpression Pair test 3" (fromSExpression (S.List[(S.Symbol "if"), (S.Boolean True), (S.List[(S.Symbol "pair"),
      (S.List[(S.Symbol "+"), (S.Integer 2), (S.Integer 1)]), (S.Integer 4)]), (S.List[(S.Symbol "pair"), (S.Real 3.2), (S.Boolean False)])]))
      (If (Boolean True) (Pair (Add (Integer 2)(Integer 1)) (Integer 4)) (Pair (Float 3.2) (Boolean False)))

    -- Left tests

    test "fromSExpression Left test 1" (fromSExpression $S.List[S.Symbol "left", (S.List[S.Symbol "pair", (S.Integer 5), (S.Real 5.5)])])
     (Left (Pair (Integer 5) (Float 5.5)))                       

    test "fromSExpression Left test 2" (fromSExpression $S.List[S.Symbol "left", (S.List[S.Symbol "pair", (S.Boolean True), (S.Real 5.5)])])
     (Left (Pair (Boolean True) (Float 5.5)))  

    test "fromSExpression Left test 3" (fromSExpression $S.List[S.Symbol "left", (S.List[(S.Symbol "pair"),  (S.Integer 4), (S.List[(S.Symbol "+"), (S.Integer 2), (S.Integer 1)])])])
      (Left (Pair (Integer 4) (Add (Integer 2) (Integer 1))))

    test "fromSExpression Left test 4" (fromSExpression $S.List[(S.Symbol "left"), (S.Integer 1)]) (Left (Integer 1))

    
    -- Right tests

    test "fromSExpression Right test 1" (fromSExpression $S.List[S.Symbol "right", (S.List[S.Symbol "pair", (S.Integer 5), (S.Real 5.5)])])
     (Right (Pair (Integer 5) (Float 5.5)))                       

    test "fromSExpression Right test 2" (fromSExpression $S.List[S.Symbol "right", (S.List[S.Symbol "pair", (S.Boolean True), (S.Real 5.5)])])
     (Right (Pair (Boolean True) (Float 5.5)))  

    test "fromSExpression Right test 3" (fromSExpression $S.List[S.Symbol "right", (S.List[(S.Symbol "pair"),  (S.Integer 4), (S.List[(S.Symbol "+"), (S.Integer 2), (S.Integer 1)])])])
      (Right (Pair (Integer 4) (Add (Integer 2) (Integer 1))))

    test "fromSExpression Right test 4" (fromSExpression $S.List[(S.Symbol "right"), (S.Integer 1)]) (Right (Integer 1))

    --Real_Pred tests

    test "fromSExpression Real? test 1" (fromSExpression $ S.List[(S.Symbol "real?"), (S.Integer 1)]) (Real_Pred (Integer 1))

    test "fromSExpression Real? test 2" (fromSExpression $ S.List[(S.Symbol "real?"), (S.Real 1.0)]) (Real_Pred (Float 1.0))
    
    test "fromSExpression Real? test 3" (fromSExpression $ S.List[(S.Symbol "real?"), (S.Boolean True)]) (Real_Pred (Boolean True))
    
    test "fromSExpression Real? test 4" (fromSExpression $ S.List[(S.Symbol "real?"), (S.List[S.Symbol "right", 
     (S.List[S.Symbol "pair", (S.List[S.Symbol "+", (S.Integer 2), (S.Integer 1)]), (S.Integer 4)])])])
     (Real_Pred (Right (Pair (Add (Integer 2) (Integer 1)) (Integer 4))))
    
     --Integer_Pred tests

    test "fromSExpression Integer? test 1" (fromSExpression $ S.List[(S.Symbol "integer?"), (S.Integer 1)]) (Integer_Pred (Integer 1))

    test "fromSExpression Integer? test 2" (fromSExpression $ S.List[(S.Symbol "integer?"), (S.Real 1.0)]) (Integer_Pred (Float 1.0))
    
    test "fromSExpression Integer? test 3" (fromSExpression $ S.List[(S.Symbol "integer?"), (S.Boolean True)]) (Integer_Pred (Boolean True))
  
    test "fromSExpression Integer? test 4" (fromSExpression $ S.List[(S.Symbol "integer?"), (S.List[S.Symbol "right", 
     (S.List[S.Symbol "pair", (S.List[S.Symbol "+", (S.Integer 2), (S.Integer 1)]), (S.Integer 4)])])])
     (Integer_Pred (Right (Pair (Add (Integer 2) (Integer 1)) (Integer 4))))

    --Number_Pred tests

    test "fromSExpression Number? test 1" (fromSExpression $ S.List[(S.Symbol "number?"), (S.Integer 1)]) (Number_Pred (Integer 1))

    test "fromSExpression Number? test 2" (fromSExpression $ S.List[(S.Symbol "number?"), (S.Real 1.0)]) (Number_Pred (Float 1.0))
    
    test "fromSExpression Number? test 3" (fromSExpression $ S.List[(S.Symbol "number?"), (S.Boolean True)]) (Number_Pred (Boolean True))
    
    test "fromSExpression Number? test 4" (fromSExpression $ S.List[(S.Symbol "number?"), (S.List[S.Symbol "right", 
     (S.List[S.Symbol "pair", (S.List[S.Symbol "+", (S.Integer 2), (S.Integer 1)]), (S.Integer 4)])])])
     (Number_Pred (Right (Pair (Add (Integer 2) (Integer 1)) (Integer 4))))

    --Boolean_Pred tests

    test "fromSExpression Boolean? test 1" (fromSExpression $ S.List[(S.Symbol "boolean?"), (S.Integer 1)]) (Boolean_Pred (Integer 1))

    test "fromSExpression Boolean? test 2" (fromSExpression $ S.List[(S.Symbol "boolean?"), (S.Real 1.0)]) (Boolean_Pred (Float 1.0))
    
    test "fromSExpression Boolean? test 3" (fromSExpression $ S.List[(S.Symbol "boolean?"), (S.Boolean True)]) (Boolean_Pred (Boolean True))
    
    test "fromSExpression Boolean? test 4" (fromSExpression $ S.List[(S.Symbol "boolean?"), (S.List[S.Symbol "right", 
     (S.List[S.Symbol "pair", (S.List[S.Symbol "+", (S.Integer 2), (S.Integer 1)]), (S.Integer 4)])])])
     (Boolean_Pred (Right (Pair (Add (Integer 2) (Integer 1)) (Integer 4))))

    --Pair_Pred tests

    test "fromSExpression Pair? test 1" (fromSExpression $ S.List[(S.Symbol "pair?"), (S.Integer 1)]) (Pair_Pred (Integer 1))

    test "fromSExpression Pair? test 2" (fromSExpression $ S.List[(S.Symbol "pair?"), (S.Real 1.0)]) (Pair_Pred (Float 1.0))
    
    test "fromSExpression Pair? test 3" (fromSExpression $ S.List[(S.Symbol "pair?"), (S.Boolean True)]) (Pair_Pred (Boolean True))
    
    test "fromSExpression Pair? test 4" (fromSExpression $ S.List[(S.Symbol "pair?"), (S.List[S.Symbol "right", 
     (S.List[S.Symbol "pair", (S.List[S.Symbol "+", (S.Integer 2), (S.Integer 1)]), (S.Integer 4)])])])
     (Pair_Pred (Right (Pair (Add (Integer 2) (Integer 1)) (Integer 4))))

    test "fromSExpression Pair? test 5" (fromSExpression $ S.List[S.Symbol "pair?", S.List[S.Symbol "pair", (S.Integer 1), (S.Integer 2)]])
     (Pair_Pred (Pair (Integer 1) (Integer 2)))

    --Call Tests
    test "fromSExpression Call test 1" (fromSExpression (S.List[S.Symbol "call", S.Symbol "f", S.List[S.List[S.Symbol "call", 
      S.Symbol "f", S.List[S.Integer 1]]]])) (Call "f" [Call "f" [Integer 1]])

    test "fromSExpression Call test 2" (fromSExpression (S.List[S.Symbol "let", S.List [S.Symbol "y", S.Integer 10], S.List[
      S.Symbol "call", S.Symbol "f", S.List[S.Integer 10]]])) (Let "y" (Integer 10) (Call "f"[Integer 10]))
    
    test "fromSExpression Call test 3" (fromSExpression (S.List[S.Symbol "call", S.Symbol "incr", S.List[S.List[S.Symbol "call", S.Symbol "incr", S.List[S.List[S.Symbol "call", 
      S.Symbol "Plus", S.List[S.Integer 1, S.Integer 3]]]]]]))
      (Call "incr" [Call "incr"[Call "Plus"[Integer 1, Integer 3]]])

    test "fromSExpression Call test 4" (fromSExpression $ S.List[S.Symbol "+", S.List[S.Symbol "let", S.List [S.Symbol "y", S.Integer 10], 
      S.List[S.Symbol "call", S.Symbol "f", S.List[S.Integer 10]]], S.List[S.Symbol "call", S.Symbol "f", S.List[
      S.List[S.Symbol "call", S.Symbol "f", S.List[S.Integer 1]]]]]) 
      (Add (Let "y" (Integer 10) (Call "f"[Integer 10])) (Call "f" [Call "f" [Integer 1]]))

-- ==========================================================================================================


-- |Convert a protoScheme expression into its s-expression representation
toSExpression :: Expr -> S.Expr
toSExpression (Integer i) = S.Integer i 
toSExpression (Boolean b) = S.Boolean b
toSExpression (Float f) = S.Real f 
toSExpression (Var v) = S.Symbol v 
toSExpression (Left x) = S.List[S.Symbol "left", toSExpression x]
toSExpression (Right x) = S.List[S.Symbol "right", toSExpression x]
toSExpression (Pair x y) = S.List[S.Symbol "pair", (toSExpression x), (toSExpression y)]
toSExpression (Boolean_Pred x) = S.List[S.Symbol "boolean?", (toSExpression x)]
toSExpression (Integer_Pred x) = S.List[S.Symbol "integer?", (toSExpression x)]
toSExpression (Real_Pred x) = S.List[S.Symbol "real?", (toSExpression x)]
toSExpression (Number_Pred x) = S.List[S.Symbol "number?", (toSExpression x)]
toSExpression (Pair_Pred x) = S.List[S.Symbol "pair?", (toSExpression x)]
toSExpression (Call x e) = S.List[S.Symbol "call", S.Symbol x, S.List (listToSExpressionList e)]
  where 
    -- Function for converting each S.Expr argument for the Call
    listToSExpressionList :: [Expr] -> [S.Expr]
    listToSExpressionList [] = [] 
    listToSExpressionList (x:xs) = (toSExpression x) : (listToSExpressionList xs)
toSExpression (Add x y) = S.List [S.Symbol "+", toSExpression x, toSExpression y]
toSExpression (Sub x y) = S.List [S.Symbol "-", toSExpression x, toSExpression y]
toSExpression (Mul x y) = S.List [S.Symbol "*", toSExpression x, toSExpression y]
toSExpression (Div x y) = S.List [S.Symbol "/", toSExpression x, toSExpression y]
toSExpression (Let v x y) = S.List [S.Symbol "let", S.List [S.Symbol v, toSExpression x], toSExpression y]
toSExpression (If x y z) = S.List [S.Symbol "if", toSExpression x, toSExpression y, toSExpression z]
toSExpression (And x y) = S.List [S.Symbol "and", toSExpression x, toSExpression y]
toSExpression (Or x y) = S.List [S.Symbol "or", toSExpression x, toSExpression y]
toSExpression (Not x) = S.List [S.Symbol "not", toSExpression x]
toSExpression (Less_Than x y) = S.List [S.Symbol "<", toSExpression x, toSExpression y]
toSExpression (Greater_Than x y) = S.List [S.Symbol ">", toSExpression x, toSExpression y]
toSExpression (Equal_To x y) = S.List [S.Symbol "=", toSExpression x, toSExpression y]
toSExpression (Cond x Nothing) = S.List [S.Symbol "cond", S.List (toSExpressionTupleListHelper x), S.Symbol "Nothing"]
toSExpression (Cond x (Just e)) = S.List [S.Symbol "cond", 
 S.List (toSExpressionTupleListHelper x), (toSExpression e)]

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
     [(Integer 1, Float 5.6)]) 
      [S.List [S.Integer 1, S.Real 5.6]]   

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
        (S.List[S.Symbol "let", S.List [S.Symbol "x", S.Integer 0], (S.List[S.Symbol "+", S.Integer 1, S.Symbol "x"])])
        
    test "toSExpression let x 2, 1 + 3" (toSExpression (Let "x" (Integer 2) (Add (Integer 1) (Integer 3)))) 
        (S.List[S.Symbol "let", S.List [S.Symbol "x", S.Integer 2], (S.List[S.Symbol "+", S.Integer 1, S.Integer 3])])
        
    test "toSExpression let y 1.5, 1 * y" (toSExpression (Let "y" (Float 1.5) (Mul (Integer 1) (Var "y")))) 
        (S.List[S.Symbol "let", S.List [S.Symbol "y", S.Real 1.5], (S.List[S.Symbol "*", S.Integer 1, S.Symbol "y"])])
        
    test "toSExpression let y 3.2, 1 / y" (toSExpression (Let "y" (Float 3.2) (Div (Integer 1) (Var "y")))) 
        (S.List[S.Symbol "let", S.List [S.Symbol "y", S.Real 3.2], (S.List[S.Symbol "/", S.Integer 1, S.Symbol "y"])])

    -- If tests 
    test "toSExpression if simple" 
        (toSExpression (If (Boolean True) (Integer 1) (Float 2.0)))
        (S.List [S.Symbol "if", S.Boolean True, S.Integer 1, S.Real 2.0])      
    test "toSExpression if complex 1" 
        (toSExpression (If (Boolean True) (Add (Integer 1) (Float 2.0)) (Var "x")))
        (S.List [S.Symbol "if", S.Boolean True, S.List [S.Symbol "+", S.Integer 1, S.Real 2.0], S.Symbol "x"])    
    test "toSExpression if complex 2" 
        (toSExpression (If (Boolean False) (Let "y" (Integer 1) (Var "y")) (Div (Integer 10) (Integer 2))))
        (S.List [S.Symbol "if", S.Boolean False, S.List [S.Symbol "let", S.List [S.Symbol "y" , S.Integer 1], S.Symbol "y"], S.List [S.Symbol "/", S.Integer 10, S.Integer 2]])   

    -- And tests
    test "toSExpression And Test 1" (toSExpression $ (And (Boolean True) (Integer 10)))
      (S.List [S.Symbol "and" , S.Boolean True, S.Integer 10]) 
          
    test "toSExpression And Test 2" (toSExpression $ And (Boolean False) 
      (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1))))
        (S.List [S.Symbol "and" , S.Boolean False, S.List [S.Symbol "let", S.List [S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]])
                 
    test "toSExpression And Test 3" (toSExpression $ (And (And (Integer 10) (Float 15.1))
      (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1))))) 
         (S.List [S.Symbol "and" , S.List [S.Symbol "and" , S.Integer 10, S.Real 15.1], 
          S.List [S.Symbol "let", S.List [S.Symbol "x", S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], 
           S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
            

    -- Or tests
    test "toSExpression Or Test 1" (toSExpression $ (Or (Boolean True) (Integer 10)))
      (S.List [S.Symbol "or" , S.Boolean True, S.Integer 10]) 
          
    test "toSExpression Or Test 2" (toSExpression $ Or (Boolean False) 
      (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1))))
        (S.List [S.Symbol "or" , S.Boolean False, S.List [S.Symbol "let", S.List [S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]])
                 
    test "toSExpression Or Test 3" (toSExpression $ (Or (Or (Integer 10) (Float 15.1))
      (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1))))) 
         (S.List [S.Symbol "or" , S.List [S.Symbol "or" , S.Integer 10, S.Real 15.1], 
          S.List [S.Symbol "let", S.List [S.Symbol "x", S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], 
           S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]])    

    -- Not tests
    test "toSExpression Not Test 1" (toSExpression $ (Not (Boolean True))) 
      (S.List [S.Symbol "not" , S.Boolean True]) 

    test "toSExpression Not Test 2" (toSExpression $  (Not (Let "x" (Add (Float 10.1) (Float 4.1)) 
      (Add (Var "x") (Float 1.1))))) (S.List [S.Symbol "not" , S.List [S.Symbol "let", S.List [S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]])  

    test "toSExpression Not Test 3" (toSExpression $ (Not (Or (Integer 10)
       (Let "x" (Add (Float 10.1) (Float 4.1)) (Add (Var "x") (Float 1.1))))))     
         (S.List [S.Symbol "not" , S.List [S.Symbol "or" , S.Integer 10, S.List [S.Symbol "let", S.List [S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]]) 

    -- Less_Than Tests
    test "toSExpression Less_Than Test 1" (toSExpression $ (Less_Than (Integer 7) (Integer 6))) 
        (S.List [S.Symbol "<", S.Integer 7, S.Integer 6]) 

    test "toSExpression Less_Than Test 2" (toSExpression $ (Less_Than (Integer 6) (Integer 7))) 
        (S.List [S.Symbol "<", S.Integer 6, S.Integer 7]) 
    
    test "toSExpression Less_Than Test 3" (toSExpression $ (Less_Than (Float 6.8) (Float 6.3))) 
        (S.List [S.Symbol "<", S.Real 6.8, S.Real 6.3])
    
    test "toSExpression Less_Than Test 4" (toSExpression $ (Less_Than (Boolean True) (Float 6.3))) 
        (S.List [S.Symbol "<", S.Boolean True, S.Real 6.3])
    
    test "toSExpression Less_Than Test 5" (toSExpression $ (Less_Than (Add (Integer 7) (Integer 6)) (Var "x"))) 
        (S.List [S.Symbol "<", S.List[S.Symbol "+", S.Integer 7, S.Integer 6], S.Symbol "x"])

    test "toSExpression Less_Than Test 6" (toSExpression $ (Less_Than (If (Boolean True) (Boolean True) (Boolean False))
        (Let "v" (Float 6.3) (Float 6.3)))) 
        (S.List [S.Symbol "<", S.List [S.Symbol "if", S.Boolean True, S.Boolean True, S.Boolean False],
          S.List[S.Symbol "let", S.List [S.Symbol "v", S.Real 6.3], S.Real 6.3]])

  -- Greater_Than Tests
    test "toSExpression Greater_Than Test 1" (toSExpression $ (Greater_Than (Integer 7) (Integer 6))) 
        (S.List [S.Symbol ">", S.Integer 7, S.Integer 6]) 

    test "toSExpression Greater_Than Test 2" (toSExpression $ (Greater_Than (Integer 6) (Integer 7))) 
        (S.List [S.Symbol ">", S.Integer 6, S.Integer 7]) 
    
    test "toSExpression Greater_Than Test 3" (toSExpression $ (Greater_Than (Float 6.8) (Float 6.3))) 
        (S.List [S.Symbol ">", S.Real 6.8, S.Real 6.3])
    
    test "toSExpression Greater_Than Test 4" (toSExpression $ (Greater_Than (Boolean True) (Float 6.3))) 
        (S.List [S.Symbol ">", S.Boolean True, S.Real 6.3])
    
    test "toSExpression Greater_Than Test 5" (toSExpression $ (Greater_Than (Add (Integer 7) (Integer 6)) (Var "x"))) 
        (S.List [S.Symbol ">", S.List[S.Symbol "+", S.Integer 7, S.Integer 6], S.Symbol "x"])

    test "toSExpression Greater_Than Test 6" (toSExpression $ (Greater_Than (If (Boolean True) (Boolean True) (Boolean False))
        (Let "v" (Float 6.3) (Float 6.3)))) 
        (S.List [S.Symbol ">", S.List [S.Symbol "if", S.Boolean True, S.Boolean True, S.Boolean False],
          S.List[S.Symbol "let", S.List [S.Symbol "v", S.Real 6.3], S.Real 6.3]])

 -- Equal To Tests
    test "toSExpression Equal_To Test 1" (toSExpression $ (Equal_To (Integer 7) (Integer 6))) 
        (S.List [S.Symbol "=", S.Integer 7, S.Integer 6]) 

    test "toSExpression Equal_To Test 2" (toSExpression $ (Equal_To (Integer 6) (Integer 7))) 
        (S.List [S.Symbol "=", S.Integer 6, S.Integer 7]) 
    
    test "toSExpression Equal_To Test 3" (toSExpression $ (Equal_To (Float 6.8) (Float 6.3))) 
        (S.List [S.Symbol "=", S.Real 6.8, S.Real 6.3])
    
    test "toSExpression Equal_To Test 4" (toSExpression $ (Equal_To (Boolean True) (Float 6.3))) 
        (S.List [S.Symbol "=", S.Boolean True, S.Real 6.3])
    
    test "toSExpression Equal_To Test 5" (toSExpression $ (Equal_To (Add (Integer 7) (Integer 6)) (Var "x"))) 
        (S.List [S.Symbol "=", S.List[S.Symbol "+", S.Integer 7, S.Integer 6], S.Symbol "x"])

    test "toSExpression Equal_To Test 6" (toSExpression $ (Equal_To (If (Boolean True) (Boolean True) (Boolean False))
        (Let "v" (Float 6.3) (Float 6.3)))) 
        (S.List [S.Symbol "=", S.List [S.Symbol "if", S.Boolean True, S.Boolean True, S.Boolean False],
          S.List[S.Symbol "let", S.List [S.Symbol "v", S.Real 6.3], S.Real 6.3]])

  -- Cond Tests 
  
    test "toSExpression Cond basic test" (toSExpression (Cond [] Nothing)) (S.List [S.Symbol "cond", S.List [], S.Symbol "Nothing"])

    test "toSExpression Cond complex test 1" (toSExpression (Cond [(Integer 1, Float 5.6)] Nothing)) 
     (S.List [S.Symbol "cond", S.List [S.List [S.Integer 1, S.Real 5.6]], S.Symbol "Nothing"])

    test "toSExpression Cond complex test 2" (toSExpression (Cond [(Integer 1, Float 5.6), (Boolean True, Integer 20)] Nothing)) 
     (S.List [S.Symbol "cond", S.List [S.List [S.Integer 1, S.Real 5.6], S.List [S.Boolean True, S.Integer 20]], 
       S.Symbol "Nothing"]) 

    test "toSExpression Cond with an else" (toSExpression (Cond [(Integer 1, Float 5.6)] (Just (Integer 20)))) 
     (S.List [S.Symbol "cond", S.List [S.List [S.Integer 1, S.Real 5.6]], S.Integer 20])          

    -- Pair tests

    test "toSExpression Pair test 1" (toSExpression (Pair (Integer 5) (Float 5.5))) (S.List[S.Symbol "pair", (S.Integer 5), (S.Real 5.5)])                       

    test "toSExpression Pair test 2" (toSExpression (Pair (Boolean True) (Float 5.5))) (S.List[S.Symbol "pair", (S.Boolean True), (S.Real 5.5)])  

    test "toSExpression Pair test 3" (toSExpression (If (Boolean True) (Pair (Add (Integer 2)(Integer 1)) (Integer 4)) (Pair (Float 3.2) (Boolean False))))
      (S.List[(S.Symbol "if"), (S.Boolean True), (S.List[(S.Symbol "pair"),
      (S.List[(S.Symbol "+"), (S.Integer 2), (S.Integer 1)]), (S.Integer 4)]), (S.List[(S.Symbol "pair"), (S.Real 3.2), (S.Boolean False)])])
     

    -- Left tests

    test "toSExpression Left test 1" (toSExpression (Left (Pair (Integer 5) (Float 5.5))))                       
      (S.List[S.Symbol "left", (S.List[S.Symbol "pair", (S.Integer 5), (S.Real 5.5)])])

    test "toSExpression Left test 2" (toSExpression (Left (Pair (Boolean True) (Float 5.5)))) 
      (S.List[S.Symbol "left", (S.List[S.Symbol "pair", (S.Boolean True), (S.Real 5.5)])]) 

    test "toSExpression Left test 3" (toSExpression (Left (Pair (Integer 4) (Add (Integer 2) (Integer 1)))))
      (S.List[S.Symbol "left", (S.List[(S.Symbol "pair"),  (S.Integer 4), (S.List[(S.Symbol "+"), (S.Integer 2), (S.Integer 1)])])])

    test "toSExpression Left test 4" (toSExpression (Left (Integer 1))) (S.List[(S.Symbol "left"), (S.Integer 1)])

    
    -- Right tests

    test "toSExpression Right test 1" (toSExpression (Right (Pair (Integer 5) (Float 5.5))))        
      (S.List[S.Symbol "right", (S.List[S.Symbol "pair", (S.Integer 5), (S.Real 5.5)])])               

    test "toSExpression Right test 2" (toSExpression (Right (Pair (Boolean True) (Float 5.5))))
      (S.List[S.Symbol "right", (S.List[S.Symbol "pair", (S.Boolean True), (S.Real 5.5)])])  

    test "toSExpression Right test 3" (toSExpression (Right (Pair (Integer 4) (Add (Integer 2) (Integer 1)))))
      (S.List[S.Symbol "right", (S.List[(S.Symbol "pair"),  (S.Integer 4), (S.List[(S.Symbol "+"), (S.Integer 2), (S.Integer 1)])])])
    
    test "toSExpression Right test 4" (toSExpression (Right (Integer 1))) (S.List[(S.Symbol "right"), (S.Integer 1)])

    --Real_Pred tests

    test "toSExpression Real? test 1" (toSExpression  (Real_Pred (Integer 1))) (S.List[(S.Symbol "real?"), (S.Integer 1)])

    test "toSExpression Real? test 2" (toSExpression (Real_Pred (Float 1.0))) (S.List[(S.Symbol "real?"), (S.Real 1.0)])
    
    test "toSExpression Real? test 3" (toSExpression (Real_Pred (Boolean True))) (S.List[(S.Symbol "real?"), (S.Boolean True)])
    
    test "toSExpression Real? test 4" (toSExpression (Real_Pred (Right (Pair (Add (Integer 2) (Integer 1)) (Integer 4)))))
      (S.List[(S.Symbol "real?"), (S.List[S.Symbol "right", 
      (S.List[S.Symbol "pair", (S.List[S.Symbol "+", (S.Integer 2), (S.Integer 1)]), (S.Integer 4)])])])
    
     --Integer_Pred tests

    test "toSExpression Integer? test 1" (toSExpression (Integer_Pred (Integer 1))) (S.List[(S.Symbol "integer?"), (S.Integer 1)])

    test "toSExpression Integer? test 2" (toSExpression (Integer_Pred (Float 1.0))) (S.List[(S.Symbol "integer?"), (S.Real 1.0)])
    
    test "toSExpression Integer? test 3" (toSExpression (Integer_Pred (Boolean True))) (S.List[(S.Symbol "integer?"), (S.Boolean True)])
    
    test "toSExpression Integer? test 4" (toSExpression (Integer_Pred (Right (Pair (Add (Integer 2) (Integer 1)) (Integer 4)))))
      (S.List[(S.Symbol "integer?"), (S.List[S.Symbol "right", 
     (S.List[S.Symbol "pair", (S.List[S.Symbol "+", (S.Integer 2), (S.Integer 1)]), (S.Integer 4)])])])

    --Number_Pred tests

    test "toSExpression Number? test 1" (toSExpression (Number_Pred (Integer 1))) (S.List[(S.Symbol "number?"), (S.Integer 1)])

    test "toSExpression Number? test 2" (toSExpression (Number_Pred (Float 1.0))) (S.List[(S.Symbol "number?"), (S.Real 1.0)])
    
    test "toSExpression Number? test 3" (toSExpression (Number_Pred (Boolean True))) (S.List[(S.Symbol "number?"), (S.Boolean True)])
    
    test "toSExpression Number? test 4" (toSExpression (Number_Pred (Right (Pair (Add (Integer 2) (Integer 1)) (Integer 4)))))
      (S.List[(S.Symbol "number?"), (S.List[S.Symbol "right", 
      (S.List[S.Symbol "pair", (S.List[S.Symbol "+", (S.Integer 2), (S.Integer 1)]), (S.Integer 4)])])])

    --Boolean_Pred tests

    test "toSExpression Boolean? test 1" (toSExpression (Boolean_Pred (Integer 1))) (S.List[(S.Symbol "boolean?"), (S.Integer 1)])

    test "toSExpression Boolean? test 2" (toSExpression (Boolean_Pred (Float 1.0))) (S.List[(S.Symbol "boolean?"), (S.Real 1.0)])
    
    test "toSExpression Boolean? test 3" (toSExpression (Boolean_Pred (Boolean True))) (S.List[(S.Symbol "boolean?"), (S.Boolean True)])
    
    test "toSExpression Boolean? test 4" (toSExpression (Boolean_Pred (Right (Pair (Add (Integer 2) (Integer 1)) (Integer 4)))))
      (S.List[(S.Symbol "boolean?"), (S.List[S.Symbol "right", 
      (S.List[S.Symbol "pair", (S.List[S.Symbol "+", (S.Integer 2), (S.Integer 1)]), (S.Integer 4)])])])

    --Pair_Pred tests

    test "toSExpression Pair? test 1" (toSExpression (Pair_Pred (Integer 1))) (S.List[(S.Symbol "pair?"), (S.Integer 1)])

    test "toSExpression Pair? test 2" (toSExpression (Pair_Pred (Float 1.0))) (S.List[(S.Symbol "pair?"), (S.Real 1.0)])
    
    test "toSExpression Pair? test 3" (toSExpression (Pair_Pred (Boolean True))) (S.List[(S.Symbol "pair?"), (S.Boolean True)])
    
    test "toSExpression Pair? test 4" (toSExpression (Pair_Pred (Right (Pair (Add (Integer 2) (Integer 1)) (Integer 4)))))
      (S.List[(S.Symbol "pair?"), (S.List[S.Symbol "right", 
      (S.List[S.Symbol "pair", (S.List[S.Symbol "+", (S.Integer 2), (S.Integer 1)]), (S.Integer 4)])])])

    test "toSExpression Pair? test 5" (toSExpression (Pair_Pred (Pair (Integer 1) (Integer 2))))
      (S.List[S.Symbol "pair?", S.List[S.Symbol "pair", (S.Integer 1), (S.Integer 2)]])

    --Call Tests
    test "toSExpression Call test 1" (toSExpression (Call "f" [Call "f" [Integer 1]])) 
      (S.List[S.Symbol "call", S.Symbol "f", S.List[S.List[S.Symbol "call", S.Symbol "f", S.List[S.Integer 1]]]])

    test "toSExpression Call test 2" (toSExpression (Let "y" (Integer 10) (Call "f"[Integer 10])))
      (S.List[S.Symbol "let", S.List [S.Symbol "y", S.Integer 10], S.List[S.Symbol "call", S.Symbol "f", S.List[S.Integer 10]]])
    
    test "toSExpression Call test 3" (toSExpression (Call "incr" [Call "incr" [Call "Plus" [Integer 1, Integer 3]]]))
      (S.List[S.Symbol "call", S.Symbol "incr", S.List[S.List[S.Symbol "call", S.Symbol "incr", S.List[S.List[S.Symbol "call", 
        S.Symbol "Plus", S.List[S.Integer 1, S.Integer 3]]]]]])

    test "toSExpression Call test 4" (toSExpression (Add (Let "y" (Integer 10) (Call "f"[Integer 10])) 
      (Call "f" [Call "f" [Integer 1]]))) (S.List[S.Symbol "+", S.List[S.Symbol "let", S.List [S.Symbol "y", S.Integer 10], 
      S.List[S.Symbol "call", S.Symbol "f", S.List[S.Integer 10]]], S.List[S.Symbol "call", S.Symbol "f", S.List[
      S.List[S.Symbol "call", S.Symbol "f", S.List[S.Integer 1]]]]]) 

--  ===========================================================================================================

-- |Convert the evaluation result into the corresponding S-expression representation
valueToSExpression :: ExprEval -> S.Expr
valueToSExpression (Eval_Integer i) = S.Integer i
valueToSExpression (Eval_Float r) = S.Real r
valueToSExpression (Eval_Boolean b) = S.Boolean b
valueToSExpression (Eval_Pair x y) = S.Dotted (valueToSExpression x) (valueToSExpression y)

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

