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

import Maps    

import qualified SExpression as S

import Prelude hiding (Left, Right)

import SimpleTestsColor (test)

import qualified Result as R



--  ==========================================================================================================

--Data type respresenting an Integer, a Double, or a Boolean
--This is the return type of the eval function 
data Value =  Closure [Variable] Expr Env
            | Integer Integer
            | Float Double
            | Boolean Bool 
            | PairVal Value Value
            | PrimOp Op [Value]
        deriving(Show, Eq) 

data Op = Op String ([Value] -> R.Result Value)  
            
instance Show Op where
    show (Op s _) = "Op " ++ s

instance Eq Op where
    _ == _ = False

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
         | (let (<Variable> <Expr>) <Expr>)
         | (if <Expr> <Expr> <Expr>)
         | (cond (<Expr> <Expr>)* )
         | (cond (<Expr> <Expr>)* (else <Expr>))
         | (real? <Expr>)
         | (integer? <Expr>)
         | (number? <Expr>)
         | (boolean? <Expr>)
         | (pair? <Expr>)
         | (lambda (<Variable>*) <Expr>) -- anonymous functions
         | (<Expr>+) -- function call/application


<GlobalDef> ::= (defun <Variable> (<Variable> <Variable>*) <Expr>)
              | (define <Variable> <Expr>)

<Program> ::= <GlobalDef>* <Expr>

-}

 -- protoScheme expressions
 -- data type representing the expressions used by the syntax 
 -- in protoscheme 
data Expr = Val Value
          | Var Variable
          | Left Expr
          | Right Expr
          | Let Variable Expr Expr
          | If Expr Expr Expr 
          | And Expr Expr
          | Or Expr Expr
          | Cond [(Expr, Expr)] (Maybe Expr)
          | Real_Pred Expr 
          | Integer_Pred Expr
          | Number_Pred Expr
          | Boolean_Pred Expr
          | Pair_Pred Expr
          | Lambda [Variable] Expr
          | App [Expr]
          | Pair Expr Expr
          deriving (Eq, Show)

-- | Program data type which is a sequence of global definitions
--   followed by a single expression
data Program = Program [GlobalDef] Expr
             deriving (Eq, Show)
-- | GlobalDef data type which can be either a function definiti  on, introduced
--    using defun, or a global variable definition, introduced using define
data GlobalDef = Define Variable Expr
               deriving (Eq, Show)


-- |Environments are maps from Variables to values (Integers)
type Env = Map Variable Value      


-- ===============================================================================

apply :: Op -> [Value] -> R.Result Value
apply (Op _ f) vs = f vs

addOp = PrimOp (Op "+" op) []
  where
    op [Integer i1, Integer i2] = return $ Integer $ i1 + i2
    op [Integer i, Float f] = return $ Float $ fromInteger i + f
    op [Float f, Integer i] = return $ Float $ f + fromInteger i
    op [Float f1, Float f2] = return $ Float $ f1 + f2
    op _ = fail "Wrong number or type of arguments for +."
subOp = PrimOp (Op "-" op) []
  where
    op [Integer i1, Integer i2] = return $ Integer $ i1 - i2
    op [Integer i, Float f] = return $ Float $ fromInteger i - f
    op [Float f, Integer i] = return $ Float $ f - fromInteger i
    op [Float f1, Float f2] = return $ Float $ f1 - f2
    op _ = fail "Wrong number or type of arguments for -."    
mulOp = PrimOp (Op "*" op) []
  where
    op [Integer i1, Integer i2] = return $ Integer $ i1 * i2
    op [Integer i, Float f] = return $ Float $ fromInteger i * f
    op [Float f, Integer i] = return $ Float $ f * fromInteger i
    op [Float f1, Float f2] = return $ Float $ f1 * f2
    op _ = fail "Wrong number or type of arguments for *."
divOp = PrimOp (Op "/" op) []
  where
    op [Integer i1, Integer i2] = return $ Integer $ i1 `div` i2
    op [Integer i, Float f] = return $ Float $ fromInteger i / f
    op [Float f, Integer i] = return $ Float $ f / fromInteger i
    op [Float f1, Float f2] = return $ Float $ f1 / f2
    op _ = fail "Wrong number or type of arguments for /."      
notOp = PrimOp (Op "not" op) []
  where
    op [Boolean True] = return $ Boolean False
    op [Boolean False] = return $ Boolean True
    op _ = fail "Wrong number or type of arguments for not."  
lessOp = PrimOp (Op "<" op) []
  where
    op [Integer i1, Integer i2] = return $ Boolean $ i1 < i2
    op [Integer i, Float f] = return $ Boolean $ fromInteger i < f
    op [Float f, Integer i] = return $ Boolean $ f < fromInteger i
    op [Float f1, Float f2] = return $ Boolean $ f1 < f2
    op _ = fail "Wrong number or type of arguments for <." 
greaterOp = PrimOp (Op ">" op) []
  where
    op [Integer i1, Integer i2] = return $ Boolean $ i1 > i2
    op [Integer i, Float f] = return $ Boolean $ fromInteger i > f
    op [Float f, Integer i] = return $ Boolean $ f > fromInteger i
    op [Float f1, Float f2] = return $ Boolean $ f1 > f2
    op _ = fail "Wrong number or type of arguments for >."    
equalOp = PrimOp (Op "=" op) []
  where
    op [Integer i1, Integer i2] = return $ Boolean $ i1 == i2
    op [Integer i, Float f] = return $ Boolean $ fromInteger i == f
    op [Float f, Integer i] = return $ Boolean $ f == fromInteger i
    op [Float f1, Float f2] = return $ Boolean $ f1 == f2
    op [Boolean f1, Boolean f2] = return $ Boolean $ f1 == f2
    op _ = fail "Wrong number or type of arguments for =."                     
leqOp = PrimOp (Op "<=" op) []
  where
    op [Integer i1, Integer i2] = return $ Boolean $ i1 <= i2
    op [Integer i, Float f] = return $ Boolean $ fromInteger i <= f
    op [Float f, Integer i] = return $ Boolean $ f <= fromInteger i
    op [Float f1, Float f2] = return $ Boolean $ f1 <= f2
    op _ = fail "Wrong number or type of arguments for <=."    
geqOp = PrimOp (Op ">=" op) []
  where
    op [Integer i1, Integer i2] = return $ Boolean $ i1 >= i2
    op [Integer i, Float f] = return $ Boolean $ fromInteger i >= f
    op [Float f, Integer i] = return $ Boolean $ f >= fromInteger i
    op [Float f1, Float f2] = return $ Boolean $ f1 >= f2
    op _ = fail "Wrong number or type of arguments for >=."


builtins :: Env 
builtins = fromList 
  [ ("+", addOp)
  , ("-", subOp)
  , ("*", mulOp)
  , ("/", divOp)
  , ("not", notOp)
  , ("<", lessOp)
  , (">", greaterOp)
  , ("=", equalOp)
  , ("<=", leqOp)
  , (">=", geqOp)
  ]

 
--  ================================================================================================

--Creates a Program representing the given SExpression
--Parses SExpression and converts it to the data type Program
programFromSExpression :: S.Expr -> Program 
programFromSExpression (S.List [S.Symbol "Program", S.List x]) = 
  Program (listOfGlobalDefsToProgram (init x)) (fromSExpression (last x))
     

-- Helper function for handling a listof S.Exprs that should be global defs. 
listOfGlobalDefsToProgram :: [S.Expr] -> [GlobalDef]
listOfGlobalDefsToProgram [] = []
listOfGlobalDefsToProgram ((S.List[S.Symbol "define", S.Symbol name, e]):xs) = 
    Define name (fromSExpression e) : listOfGlobalDefsToProgram xs
listOfGlobalDefsToProgram ((S.List[S.Symbol "defun", S.Symbol name, S.List args, e]):xs) = 
    Define name (Lambda (sExpressionArgsToVariableArgs args) (fromSExpression e)) : listOfGlobalDefsToProgram xs
        -- then within those defuns, need to go through list of variables
        where 
             sExpressionArgsToVariableArgs :: [S.Expr] -> [Variable]
             sExpressionArgsToVariableArgs [] = []
             sExpressionArgsToVariableArgs ((S.Symbol x):xs) = x : sExpressionArgsToVariableArgs xs

-- Examples of S-Expressions representing a variety of Programs, including simple and nested Programs
-- and programs including Defun and Define
sexpr_empty = S.List[S.Symbol "Program", S.List[(S.Integer 5)]]

sexpr_ex1 = S.List [S.Symbol "Program", S.List[S.List[S.Symbol "defun", S.Symbol "incr", S.List [S.Symbol "x"], 
  S.List[S.Symbol "+", S.Symbol "x", S.Integer 1]], S.List[S.Symbol "incr", 
    S.List [S.Symbol "incr", S.List [S.Symbol "incr", S.Integer 1]]]]]

sexpr_ex1B = S.List[S.Symbol "Program", S.List[S.List[S.Symbol "defun", S.Symbol "incr", S.List [S.Symbol "x"], 
  S.List[S.Symbol "+", S.Symbol "x", S.Integer 1]], 
   S.List [S.Symbol "defun", S.Symbol "Plus", S.List [S.Symbol "x", S.Symbol "y"], 
    S.List [S.Symbol "+", S.Symbol "x", S.Symbol "y"]], S.List[S.Symbol "incr", 
    S.List [S.Symbol "incr", S.List [ S.Symbol "Plus", S.Integer 1, S.Integer 3]]]]]  

sexpr_ex2 = S.List[S.Symbol "Program", S.List[S.List[S.Symbol "defun", S.Symbol "f", S.List[S.Symbol "x"], 
  S.List[S.Symbol "+", S.Symbol "x", S.Symbol "y"]], S.List[S.Symbol "let", S.List [S.Symbol "y", S.Integer 10],
  S.List[S.Symbol "f", S.Integer 10]]]]

sexpr_ex3 = S.List[S.Symbol "Program", S.List[S.List[S.Symbol "defun", S.Symbol "incr", S.List[S.Symbol "x"],
  S.List[S.Symbol "+", S.Symbol "x", S.Integer 1]], S.List[S.Symbol "let", S.List [S.Symbol "z", S.Integer 20],
  S.List[S.Symbol "incr", S.Symbol "z"]]]]

sexpr_ex4 = S.List[S.Symbol "Program", S.List [S.List[S.Symbol "define", S.Symbol "f", S.Integer 10], 
  S.List[S.Symbol "-", S.Symbol "f", S.Integer 1]]]

sexpr_ex5 = S.List[S.Symbol "Program", S.List [S.List[S.Symbol "define", S.Symbol "Double", S.List[S.Symbol "pair", S.Integer 10, S.Integer 2]], 
  S.List[S.Symbol "pair", S.List[S.Symbol "*", S.Integer 2, S.List[S.Symbol "left", S.Symbol "Double"]],
  S.List[S.Symbol "*", S.Integer 2, S.List[S.Symbol "right", S.Symbol "Double"]]]]] 

sexpr_ex6 = S.List[S.Symbol "Program", S.List [S.List[S.Symbol "define", S.Symbol "f", S.Integer 10],
                                      S.List[S.Symbol "defun", S.Symbol "incr", S.List[S.Symbol "x"],
                                            S.List[S.Symbol "+", S.Symbol "x", S.Integer 1]], 
   S.List[S.Symbol "incr", S.Symbol "f"]]]


sexpreexample = S.List [S.Symbol "Program", S.List [S.List [S.Symbol "defun",S.Symbol "compose", S.List [S.Symbol "f",S.Symbol "g"],
                              S.List [S.Symbol "lambda",S.List [S.Symbol "x"],S.List [S.Symbol "f",S.List [S.Symbol "g",S.Symbol "x"]]]],
                              S.List [S.Symbol "let",S.List [S.Symbol "double",S.List [S.Symbol "lambda",S.List [S.Symbol "x"],S.List [S.Symbol "*",S.Integer 2,S.Symbol "x"]]],S.List [S.Symbol "let",S.List [S.Symbol "negate",S.List [S.Symbol "lambda",S.List [S.Symbol "x"],S.List [S.Symbol "-",S.Integer 0,S.Symbol "x"]]],S.List [S.Symbol "let",S.List [S.Symbol "as-pair",S.List [S.Symbol "lambda",S.List [S.Symbol "x"],S.List [S.Symbol "pair",S.Symbol "x",S.List [S.Symbol "negate",S.Symbol "x"]]]],
                              S.List [S.List [S.Symbol "compose",S.Symbol "as-pair",S.List [S.Symbol "compose",S.Symbol "negate",S.Symbol "double"]],S.Integer 12]]]]]]


--Examples of the same Programs represented above but as their original Program data type
ex_program_mt = Program [] (Val (Integer 5))

ex_program_1 = Program [Define "incr" (Lambda ["x"] (App [Var "+", Var "x", Val (Integer 1)]))] 
                 (App [Var "incr" , App [Var "incr", App [Var "incr", Val (Integer 1)]]])

ex_program_1B = Program [Define "incr" (Lambda ["x"] (App [Var "+", Var "x", Val (Integer 1)])),
                         Define "Plus" (Lambda ["x", "y"] (App [Var "+", Var "x", Var "y"]))] 
                 (App [Var "incr", App [ Var "incr" , App  [ Var "Plus" , Val (Integer 1), Val (Integer 3)]]])

ex_program_2 = Program [Define "f" (Lambda ["x"] (App [Var "+", Var "x", Var "y"]))]
                 (Let "y" (Val (Integer 10)) (App [Var "f", Val (Integer 10)]))

ex_program_3 = Program [Define "incr" (Lambda ["x"] (App [Var "+", Var "x", Val (Integer 1)]))] 
                 (Let "z" (Val (Integer 20)) (App [Var "incr", Var "z"]))

ex_program_4 = Program [Define "f" (Val (Integer 10))] (App [Var "-", Var "f", Val (Integer 1)])

ex_program_6 = Program [Define "f" (Val (Integer 10)),
                        Define "incr" (Lambda ["x"] (App [Var "+",Var "x",Val (Integer 1)]))] 
                    (App [Var "incr",Var "f"])



--tests of programFromSExpression Defun
test_programFromSExpression = do
    test "programFromSExpression ex_empty test 1" (programFromSExpression sexpr_empty) ex_program_mt

    test "programFromSExpression ex1 test 2" (programFromSExpression sexpr_ex1) ex_program_1

    test "programFromSExpression ex1B test 3" (programFromSExpression sexpr_ex1B) ex_program_1B

    test "programFromSExpression ex2 test 4" (programFromSExpression sexpr_ex2) ex_program_2

    test "programFromSExpression ex3 test 5" (programFromSExpression sexpr_ex3) ex_program_3

    test "programFromSExpression ex4 test 6" (programFromSExpression sexpr_ex4) ex_program_4

    test "programFromSExpression ex6 test 7" (programFromSExpression sexpr_ex6) ex_program_6

--  =========================================================================================================

-- |Parse an s-expression and convert it into a protoScheme expression.
-- Need to have the S.Symbol x last to account for where there should be let because
-- pattern matching tells us that that symbol is not one of the four operation symbols. 
fromSExpression :: S.Expr -> Expr
fromSExpression (S.Integer i) = Val (Integer i)
fromSExpression (S.Boolean b) = Val (Boolean b)
fromSExpression (S.Real r) = Val (Float r)
fromSExpression (S.Symbol s) = Var s
fromSExpression (S.List[S.Symbol "left", e1]) = Left (fromSExpression e1)
fromSExpression (S.List[S.Symbol "right", e1]) = Right (fromSExpression e1)
fromSExpression (S.List[S.Symbol "pair", e1, e2]) = Pair (fromSExpression e1) (fromSExpression e2)
fromSExpression (S.List[S.Symbol "and", e1, e2]) = And (fromSExpression e1) (fromSExpression e2)
fromSExpression (S.List[S.Symbol "or", e1, e2]) = Or (fromSExpression e1) (fromSExpression e2)
fromSExpression (S.List[S.Symbol "real?", e]) = Real_Pred (fromSExpression e)
fromSExpression (S.List[S.Symbol "integer?", e]) = Integer_Pred (fromSExpression e)
fromSExpression (S.List[S.Symbol "number?", e]) = Number_Pred (fromSExpression e)
fromSExpression (S.List[S.Symbol "boolean?", e]) = Boolean_Pred (fromSExpression e)
fromSExpression (S.List[S.Symbol "pair?", e]) = Pair_Pred (fromSExpression e)
fromSExpression (S.List [S.Symbol "let", S.List [S.Symbol x, e1], e2]) =
    Let x (fromSExpression e1) (fromSExpression e2)
fromSExpression (S.List [S.Symbol "if", e1, e2, e3]) =
    If (fromSExpression e1) (fromSExpression e2) (fromSExpression e3) 
fromSExpression (S.List [S.Symbol "cond", S.List x, e]) = 
    Cond (fromSExpressionTupleListHelper x)  (handleElse e) 
        where 
            handleElse :: S.Expr -> Maybe Expr 
            handleElse (S.Symbol "Nothing") = Nothing 
            handleElse e = Just (fromSExpression e)
fromSExpression (S.List (S.Symbol "cond": xs)) = 
    Cond (fromSExpressionTupleListHelper (init xs))  (handleElse (last xs)) 
        where 
            handleElse :: S.Expr -> Maybe Expr 
            handleElse (S.Symbol "Nothing") = Nothing 
            handleElse (S.List [S.Symbol "else", x]) = Just (fromSExpression x)
            handleElse e = Just (fromSExpression e)            
fromSExpression (S.List [S.Symbol "lambda", S.List vars, body]) = 
  Lambda (listFromSExpressionSymbolList vars) (fromSExpression body)            
-- all other lists are assumed to be function apps, like +, -, etc            
fromSExpression (S.List (func:args)) = App (fromSExpression func : listFromSExpressionList args)

-- Helper function to turn a list of S.Expr to a list of Expr.           
listFromSExpressionList :: [S.Expr] -> [Expr]
listFromSExpressionList [] = [] 
listFromSExpressionList (x:xs) = (fromSExpression x) : (listFromSExpressionList xs)  

listFromSExpressionSymbolList :: [S.Expr] -> [Variable] 
listFromSExpressionSymbolList [] = [] 
listFromSExpressionSymbolList (S.Symbol x:xs) = x : (listFromSExpressionSymbolList xs) 

-- Function that assists the fromSExpression function by handling a list of 
-- the SExpr version of Expr tuples (Lists of two elements are the tuples)    
fromSExpressionTupleListHelper :: [S.Expr] -> [(Expr, Expr)] 
fromSExpressionTupleListHelper [] =  [] 
fromSExpressionTupleListHelper (S.List [t1, t2]:xs) = ((fromSExpression t1), (fromSExpression t2)) : fromSExpressionTupleListHelper xs     

-- Test that the helper function works correctly. 
test_fromSExpressionTupleListHelper = do 
    test "fromSExpressionTupleListHelper basic test" (fromSExpressionTupleListHelper []) [] 

    test "fromSExpressionTupleListHelper complex test 1" (fromSExpressionTupleListHelper [S.List [S.Integer 1, S.Integer 5]]) 
     [((Val (Integer 1)), (Val (Integer 5)))]

    test "fromSExpressionTupleListHelper complex test 2" 
     (fromSExpressionTupleListHelper [S.List [S.Integer 1, S.Integer 5], S.List [S.Boolean True, S.Real 5.5]]) 
     [(Val (Integer 1), Val (Integer 5)), (Val (Boolean True), Val (Float 5.5))]

    test "fromSExpressionTupleHelper complex test 3" 
     (fromSExpressionTupleListHelper [S.List [S.Integer 1, S.Integer 5]]) 
     [(Val (Integer 1), Val (Integer 5))]   

test_fromSExpression = do
    
    test "fromSExpression Test Variable" (fromSExpression $ S.Symbol "v") (Var "v")

    -- Boolean tests
    
    test "Boolean fromSExpression t" (fromSExpression $ S.Boolean True) (Val (Boolean True))

    test "Boolean fromSExpression f" (fromSExpression $ S.Boolean False ) (Val (Boolean False))

    test "Boolean fromSExpression Test Add" (fromSExpression $ S.List [S.Symbol "+",
     S.Integer 4, S.Boolean True]) (App [Var "+", (Val (Integer 4)), (Val (Boolean True))])

    test "Boolean fromSExpression Test Sub" (fromSExpression $ S.List [S.Symbol "-",
     S.Integer 4, S.Boolean False]) (App [Var "-", (Val (Integer 4)), (Val (Boolean False))])

    test "Boolean fromSExpression Test Mul" (fromSExpression $ S.List [S.Symbol "*",
     S.Integer 4, S.Boolean True]) (App [Var "*", (Val (Integer 4)), (Val (Boolean True))])

    test "Boolean fromSExpression Test Div" (fromSExpression $ S.List [S.Symbol "/",
     S.Integer 4, S.Boolean False]) (App [Var "/", (Val (Integer 4)), (Val (Boolean False))])

    test "Boolean fromSExpression Test Nested Operations" (fromSExpression $ S.List [S.Symbol "/",
     S.List [S.Symbol "+", S.Integer 4, S.Boolean False], S.List [S.Symbol "-",
      S.Integer 4, S.Integer 10]]) (App [Var "/", (App [Var "+", (Val (Integer 4)), (Val (Boolean False))]), 
       (App [Var "-", (Val (Integer 4)), (Val (Integer 10))])])

    -- Integer tests   

    test "Integer fromSExpression 42" (fromSExpression $ S.Integer 42) (Val (Integer 42))

    test "Integer fromSExpression Test Add" (fromSExpression $ S.List [S.Symbol "+",
     S.Integer 4, S.Integer 10]) (App [Var "+", (Val (Integer 4)), (Val (Integer 10))])

    test "Integer fromSExpression Test Sub" (fromSExpression $ S.List [S.Symbol "-",
     S.Integer 4, S.Integer 10]) (App [Var "-", (Val (Integer 4)), (Val (Integer 10))])

    test "Integer fromSExpression Test Mul" (fromSExpression $ S.List [S.Symbol "*",
     S.Integer 4, S.Integer 10]) (App [Var "*", (Val (Integer 4)), (Val (Integer 10))])

    test "Integer fromSExpression Test Div" (fromSExpression $ S.List [S.Symbol "/",
     S.Integer 4, S.Integer 10]) (App [Var "/", (Val (Integer 4)), (Val (Integer 10))])

    test "Integer fromSExpression Test Nested Operations" (fromSExpression $ S.List [S.Symbol "/",
     S.List [S.Symbol "+", S.Integer 4, S.Integer 10], S.List [S.Symbol "-",
      S.Integer 4, S.Integer 10]]) (App [Var "/", (App [Var "+", (Val (Integer 4)), (Val (Integer 10))]),
       (App [Var "-", (Val (Integer 4)), (Val (Integer 10))])])

    test "Integer fromSExpression Test Let  Simple" (fromSExpression $ S.List [S.Symbol "let", S.List [S.Symbol "x",
     S.List [S.Symbol "+", S.Integer 10, S.Integer 4]], S.List [S.Symbol "+", S.Symbol "x", S.Integer 1]])
     (Let "x" (App [Var "+", (Val (Integer 10)), (Val (Integer 4))]) (App [Var "+", (Var "x"), (Val (Integer 1))]))

    test "Integer fromSExpression Test Let Complex" (fromSExpression $ S.List [S.Symbol "let", S.List [S.Symbol "y",
     S.List [S.Symbol "-", S.Integer 20, S.Integer 8]], S.List [S.Symbol "let", S.List [S.Symbol "x",
      S.List [S.Symbol "+", S.Symbol "y", S.Integer 4]], S.List [S.Symbol "+",
       S.Symbol "x", S.Integer 1]]]) (Let "y" (App [Var "-", (Val (Integer 20)), (Val (Integer 8))])
       (Let "x" (App [Var "+", (Var "y"), (Val (Integer 4))]) (App [Var "+", (Var "x"), (Val (Integer 1))])))

    -- Real tests   

    test "Real fromSExpression 42" (fromSExpression $ S.Real 42.0) (Val (Float 42.0))

    test "Real fromSExpression Test Add" (fromSExpression $ S.List [S.Symbol "+",
     S.Real 4.1, S.Real 10.1]) (App [Var "+", (Val (Float 4.1)), (Val (Float 10.1))])

    test "Real fromSExpression Test Sub" (fromSExpression $ S.List [S.Symbol "-",
     S.Real 4.1, S.Real 10.1]) (App [Var "-", (Val (Float 4.1)), (Val (Float 10.1))])

    test "Real fromSExpression Test Mul" (fromSExpression $ S.List [S.Symbol "*",
     S.Real 4.1, S.Real 10.1]) (App [Var "*", (Val (Float 4.1)), (Val (Float 10.1))])

    test "Real fromSExpression Test Div" (fromSExpression $ S.List [S.Symbol "/",
     S.Real 4.1, S.Real 10.1]) (App [Var "/", (Val (Float 4.1)), (Val (Float 10.1))])

    test "Real fromSExpression Test Nested Operations" (fromSExpression $ S.List [S.Symbol "/",
     S.List [S.Symbol "+", S.Real 4.1, S.Real 10.1], S.List [S.Symbol "-",
      S.Real 4.1, S.Real 10.1]]) (App [Var "/", (App [Var "+", (Val (Float 4.1)), (Val (Float 10.1))]), 
       (App [Var "-", (Val (Float 4.1)), (Val (Float 10.1))])])

    test "Real fromSExpression Test Let  Simple" (fromSExpression $ S.List [S.Symbol "let", S.List [S.Symbol "x",
     S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]])
     (Let "x" (App [Var "+", (Val (Float 10.1)), (Val (Float 4.1))]) (App [Var "+", (Var "x"), (Val (Float 1.1))]))

    test "Real fromSExpression Test Let Complex" (fromSExpression $ S.List [S.Symbol "let", S.List [S.Symbol "y",
     S.List [S.Symbol "-", S.Real 20.1, S.Real 8.1]], S.List [S.Symbol "let", S.List [S.Symbol "x",
      S.List [S.Symbol "+", S.Symbol "y", S.Real 4.1]], S.List [S.Symbol "+",
       S.Symbol "x", S.Real 1.1]]]) 
       (Let "y" (App [Var "-", (Val (Float 20.1)), (Val (Float 8.1))])
       (Let "x" (App [Var "+", (Var "y"), (Val (Float 4.1))])  (App [Var "+", (Var "x"), (Val (Float 1.1))])))

   -- If tests
    test "If fromSExpression Test 1" (fromSExpression $ S.List [
        S.Symbol "if" , S.Boolean True, S.Integer 10, S.Real 15.1]) 
          (If (Val (Boolean True)) (Val (Integer 10)) (Val (Float 15.1)))  

    test "If fromSExpression Test 2" (fromSExpression $ S.List [
        S.Symbol "if" , S.Boolean False, S.Integer 10, S.List [S.Symbol "let", S.List [S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
            (If (Val (Boolean False)) (Val (Integer 10)) (Let "x" (App [Var "+", (Val (Float 10.1)), (Val (Float 4.1))]) 
              (App [Var "+", (Var "x"), (Val (Float 1.1))])))      

    test "If fromSExpression Test 3" (fromSExpression $ S.List [
        S.Symbol "if" , S.Boolean False, S.List [S.Symbol "if" , S.Boolean True, S.Integer 10, S.Real 15.1], 
         S.List [S.Symbol "let", S.List [S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
            (If (Val (Boolean False)) (If (Val (Boolean True)) (Val (Integer 10)) (Val (Float 15.1)))
             (Let "x" (App [Var "+", (Val (Float 10.1)), (Val (Float 4.1))]) (App [Var "+", (Var "x"), (Val (Float 1.1))])))

    -- And tests
    test "And fromSExpression Test 1" (fromSExpression $ S.List [
        S.Symbol "and" , S.Boolean True, S.Integer 10]) 
          (And (Val (Boolean True)) (Val (Integer 10)))

    test "And fromSExpression Test 2" (fromSExpression $ S.List [
        S.Symbol "and" , S.Boolean False, S.List [S.Symbol "let", S.List [S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
            (And (Val (Boolean False)) (Let "x"  (App [Var "+", (Val (Float 10.1)), (Val (Float 4.1))]) (App [Var "+", (Var "x"), (Val (Float 1.1))])))   

    -- Or tests
    test "Or fromSExpression Test 1" (fromSExpression $ S.List [
        S.Symbol "or" , S.Boolean True, S.Integer 10]) 
          (Or (Val (Boolean True)) (Val (Integer 10)))  

    test "Or fromSExpression Test 2" (fromSExpression $ S.List [
        S.Symbol "or" , S.Boolean False, S.List [S.Symbol "let", S.List [S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
            (Or (Val (Boolean False)) (Let "x" (App [Var "+",Val (Float 10.1),Val (Float 4.1)]) (App [Var "+",Var "x",Val (Float 1.1)])))

    test "Or fromSExpression Test 3" (fromSExpression $ S.List [
        S.Symbol "or" , S.List [S.Symbol "or" , S.Integer 10, S.Real 15.1], 
         S.List [S.Symbol "let", S.List [S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
            (Or (Or (Val (Integer 10)) (Val (Float 15.1))) (Let "x" (App [Var "+",Val (Float 10.1),Val (Float 4.1)]) (App [Var "+",Var "x",Val (Float 1.1)])))     

    -- Not tests
    test "Not fromSExpression Test 1" (fromSExpression $ S.List [
        S.Symbol "not" , S.Boolean True]) 
          (App [Var "not", (Val (Boolean True))])   

    test "Not fromSExpression Test 2" (fromSExpression $ S.List [
        S.Symbol "not" , S.List [S.Symbol "let", S.List [S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]) 
            (App [Var "not", (Let "x" (App [Var "+", (Val (Float 10.1)), (Val (Float 4.1))]) (App [Var "+", (Var "x"), (Val (Float 1.1))]))])        

    test "Not fromSExpression Test 3" (fromSExpression $ S.List [
        S.Symbol "not" , S.List [S.Symbol "or" , S.Integer 10, 
         S.List [S.Symbol "let", S.List [S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]]]) 
            (App [Var "not",Or (Val (Integer 10)) (Let "x" (App [Var "+",Val (Float 10.1),Val (Float 4.1)]) (App [Var "+",Var "x",Val (Float 1.1)]))])

    -- Less_Than tests
    test "fromSExpression Less_Than Test 1" (fromSExpression $ S.List [S.Symbol "<", S.Integer 7, S.Integer 6])
      (App [Var "<", (Val (Integer 7)), (Val (Integer 6))])

    test "fromSExpression Less_Than Test 2" (fromSExpression $ S.List [S.Symbol "<", S.Integer 6, S.Integer 7])
      (App [Var "<", (Val (Integer 6)), (Val (Integer 7))])
    
    test "fromSExpression Less_Than Test 3" (fromSExpression $ S.List [S.Symbol "<", S.Real 6.8, S.Real 6.3])
      (App [Var "<", (Val (Float 6.8)), (Val (Float 6.3))]) 
    
    test "fromSExpression Less_Than Test 4" (fromSExpression $ S.List [S.Symbol "<", S.Boolean True, S.Real 6.3])
      (App [Var "<", (Val (Boolean True)), (Val (Float 6.3))]) 
    
    test "fromSExpression Less_Than Test 5" (fromSExpression $ S.List [S.Symbol "<", S.List [S.Symbol "+", S.Integer 7, 
       S.Integer 6], S.Symbol "x"])
      (App [Var "<", (App [Var "+", (Val (Integer 7)), (Val (Integer 6))]), (Var "x")]) 
        
    test "fromSExpression Less_Than Test 6" (fromSExpression $ S.List [S.Symbol "<", S.List [S.Symbol "if", S.Boolean True, 
       S.Boolean True, S.Boolean False], S.List [S.Symbol "let", S.List [ S.Symbol "v", S.Real 6.3], S.Real 6.3]])   
      (App [Var "<", (If (Val (Boolean True)) (Val (Boolean True)) (Val (Boolean False))), (Let "v" (Val (Float 6.3)) (Val (Float 6.3)))])

     -- Greater_Than tests
    test "fromSExpression Greater_Than Test 1" (fromSExpression $ S.List [S.Symbol ">", S.Integer 7, S.Integer 6])
      (App [Var ">", (Val (Integer 7)), (Val (Integer 6))])

    test "fromSExpression Greater_Than Test 2" (fromSExpression $ S.List [S.Symbol ">", S.Integer 6, S.Integer 7])
      (App [Var ">", (Val (Integer 6)), (Val (Integer 7))])
    
    test "fromSExpression Greater_Than Test 3" (fromSExpression $ S.List [S.Symbol ">", S.Real 6.8, S.Real 6.3])
     (App [Var ">", (Val (Float 6.8)), (Val (Float 6.3))]) 
    
    test "fromSExpression Greater_Than Test 4" (fromSExpression $ S.List [S.Symbol ">", S.Boolean True, S.Real 6.3])
     (App [Var ">", (Val (Boolean True)), (Val (Float 6.3))]) 
    
    test "fromSExpression Greater_Than Test 5" (fromSExpression $ S.List [S.Symbol ">", S.List[S.Symbol "+", S.Integer 7, 
       S.Integer 6], S.Symbol "x"])
      (App [Var ">", (App [Var "+", (Val (Integer 7)), (Val (Integer 6))]), (Var "x")]) 
        
    test "fromSExpression Greater_Than Test 6" (fromSExpression $ S.List [S.Symbol ">", S.List [S.Symbol "if", S.Boolean True, 
       S.Boolean True, S.Boolean False], S.List[S.Symbol "let", S.List [S.Symbol "v", S.Real 6.3], S.Real 6.3]])   
     (App [Var ">", (If (Val (Boolean True)) (Val (Boolean True)) (Val (Boolean False))), (Let "v" (Val (Float 6.3)) (Val (Float 6.3)))])                                  

    -- Equal_To tests
    test "fromSExpression Equal_To Test 1" (fromSExpression $ S.List [S.Symbol "=", S.Integer 7, S.Integer 6])
      (App [Var "=", (Val (Integer 7)), (Val (Integer 6))]) 

    test "fromSExpression Equal_To Test 2" (fromSExpression $ S.List [S.Symbol "=", S.Integer 6, S.Integer 7])
      (App [Var "=", (Val (Integer 6)), (Val (Integer 7))]) 
    
    test "fromSExpression Equal_To Test 3" (fromSExpression $ S.List [S.Symbol "=", S.Real 6.8, S.Real 6.3])
      (App [Var "=", (Val (Float 6.8)), (Val (Float 6.3))]) 
    
    test "fromSExpression Equal_To Test 4" (fromSExpression $ S.List [S.Symbol "=", S.Boolean True, S.Real 6.3])
      (App [Var "=", (Val (Boolean True)), (Val (Float 6.3))]) 
    
    test "fromSExpression Equal_To Test 5" (fromSExpression $ S.List [S.Symbol "=", S.List[S.Symbol "+", S.Integer 7, 
       S.Integer 6], S.Symbol "x"])
      (App [Var "=", (App [Var "+", (Val (Integer 7)), (Val (Integer 6))]), (Var "x")]) 
        
    test "fromSExpression Equal_To Test 6" (fromSExpression $ S.List [S.Symbol "=", S.List [S.Symbol "if", S.Boolean True, 
       S.Boolean True, S.Boolean False], S.List[S.Symbol "let", S.List [S.Symbol "v", S.Real 6.3], S.Real 6.3]])   
     (App [Var "=", (If (Val (Boolean True)) (Val (Boolean True)) (Val (Boolean False))), (Let "v" (Val (Float 6.3)) (Val (Float 6.3)))])   

  -- <= tests
    test "fromSExpression <= Test 1" (fromSExpression $ S.List [S.Symbol "<=", S.Integer 7, S.Integer 6])
      (App [Var "<=", (Val (Integer 7)), (Val (Integer 6))]) 

    test "fromSExpression <= Test 2" (fromSExpression $ S.List [S.Symbol "<=", S.Integer 6, S.Integer 7])
      (App [Var "<=", (Val (Integer 6)), (Val (Integer 7))]) 
    
    test "fromSExpression <= Test 3" (fromSExpression $ S.List [S.Symbol "<=", S.Real 6.8, S.Real 6.3])
      (App [Var "<=", (Val (Float 6.8)), (Val (Float 6.3))]) 
    
    test "fromSExpression <= Test 4" (fromSExpression $ S.List [S.Symbol "<=", S.Boolean True, S.Real 6.3])
      (App [Var "<=", (Val (Boolean True)), (Val (Float 6.3))]) 
    
    test "fromSExpression <= Test 5" (fromSExpression $ S.List [S.Symbol "<=", S.List[S.Symbol "+", S.Integer 7, 
       S.Integer 6], S.Symbol "x"])
      (App [Var "<=", (App [Var "+", (Val (Integer 7)), (Val (Integer 6))]), (Var "x")]) 
        
    test "fromSExpression <= Test 6" (fromSExpression $ S.List [S.Symbol "<=", S.List [S.Symbol "if", S.Boolean True, 
       S.Boolean True, S.Boolean False], S.List[S.Symbol "let", S.List [S.Symbol "v", S.Real 6.3], S.Real 6.3]])   
     (App [Var "<=", (If (Val (Boolean True)) (Val (Boolean True)) (Val (Boolean False))), (Let "v" (Val (Float 6.3)) (Val (Float 6.3)))]) 

        -- >= tests
    test "fromSExpression >= Test 1" (fromSExpression $ S.List [S.Symbol ">=", S.Integer 7, S.Integer 6])
      (App [Var ">=", (Val (Integer 7)), (Val (Integer 6))]) 

    test "fromSExpression >=  Test 2" (fromSExpression $ S.List [S.Symbol ">=", S.Integer 6, S.Integer 7])
      (App [Var">=", (Val (Integer 6)), (Val (Integer 7))]) 
    
    test "fromSExpression >=  Test 3" (fromSExpression $ S.List [S.Symbol ">=", S.Real 6.8, S.Real 6.3])
      (App [Var ">=", (Val (Float 6.8)), (Val (Float 6.3))]) 
    
    test "fromSExpression >=  Test 4" (fromSExpression $ S.List [S.Symbol ">=", S.Boolean True, S.Real 6.3])
      (App [Var ">=", (Val (Boolean True)), (Val (Float 6.3))]) 
    
    test "fromSExpression >= Test 5" (fromSExpression $ S.List [S.Symbol ">=", S.List[S.Symbol "+", S.Integer 7, 
       S.Integer 6], S.Symbol "x"])
      (App [Var ">=", (App [Var "+", (Val (Integer 7)), (Val (Integer 6))]), (Var "x")]) 
        
    test "fromSExpression >= Test 6" (fromSExpression $ S.List [S.Symbol ">=", S.List [S.Symbol "if", S.Boolean True, 
       S.Boolean True, S.Boolean False], S.List[S.Symbol "let", S.List [S.Symbol "v", S.Real 6.3], S.Real 6.3]])   
     (App [Var ">=", (If (Val (Boolean True)) (Val (Boolean True)) (Val (Boolean False))), (Let "v" (Val (Float 6.3)) (Val (Float 6.3)))])   
     
    -- Cond tests 
    test "fromSExpression Cond  basic test" (fromSExpression $ S.List [S.Symbol "cond", S.List [], S.Symbol "Nothing"]) (Cond [] Nothing) 

    test "fromSExpression Cond complex test 1" (fromSExpression $ S.List 
     [S.Symbol "cond", S.List [S.List [S.Integer 1, S.Integer 5]], S.Symbol "Nothing"]) 
     (Cond [(Val (Integer 1), (Val (Integer 5)))] Nothing) 

    test "fromSExpression Cond complex test 2" (fromSExpression $ S.List [S.Symbol "cond", S.List [
     S.List [S.Integer 1, S.Integer 5], S.List [S.Boolean True, S.Real 5.5]], S.Symbol "Nothing"]) 
       (Cond [(Val (Integer 1), Val (Integer 5)), (Val (Boolean True), Val (Float 5.5))] Nothing)

    test "fromSExpression Cond with an else" (fromSExpression $ S.List [S.Symbol "cond", S.List [
     S.List [S.Integer 1, S.Integer 5]], (S.Real 5.5)]) 
       (Cond [(Val (Integer 1), Val (Integer 5))] (Just (Val (Float 5.5))))    
    

    -- Pair tests

    test "fromSExpression Pair test 1" (fromSExpression $ S.List[S.Symbol "pair", (S.Integer 5), (S.Real 5.5)]) 
     (Pair (Val (Integer 5)) (Val (Float 5.5)))                       

    test "fromSExpression Pair test 2" (fromSExpression $S.List[S.Symbol "pair", (S.Boolean True), (S.Real 5.5)]) 
     (Pair (Val (Boolean True)) (Val (Float 5.5))) 

    test "fromSExpression Pair test 3" (fromSExpression (S.List[(S.Symbol "if"), (S.Boolean True), (S.List[(S.Symbol "pair"),
      (S.List[(S.Symbol "+"), (S.Integer 2), (S.Integer 1)]), (S.Integer 4)]), (S.List[(S.Symbol "pair"), (S.Real 3.2), (S.Boolean False)])]))
      (If (Val (Boolean True)) (Pair (App [Var "+", (Val (Integer 2)), (Val (Integer 1))]) (Val (Integer 4)))
       (Pair (Val (Float 3.2)) (Val ((Boolean False)))))

    -- Left tests

    test "fromSExpression Left test 1" (fromSExpression $S.List[S.Symbol "left", (S.List[S.Symbol "pair", (S.Integer 5), (S.Real 5.5)])])
     (Left (Pair (Val (Integer 5)) (Val (Float 5.5))))                    

    test "fromSExpression Left test 2" (fromSExpression $S.List[S.Symbol "left", (S.List[S.Symbol "pair", (S.Boolean True), (S.Real 5.5)])])
     (Left (Pair (Val (Boolean True)) (Val (Float 5.5)))) 

    test "fromSExpression Left test 3" (fromSExpression $S.List[S.Symbol "left", (S.List[(S.Symbol "pair"),  (S.Integer 4), (S.List[(S.Symbol "+"), (S.Integer 2), (S.Integer 1)])])])
      (Left (Pair (Val (Integer 4)) (App [Var "+", (Val (Integer 2)), (Val (Integer 1))])))

    test "fromSExpression Left test 4" (fromSExpression $S.List[(S.Symbol "left"), (S.Integer 1)]) (Left (Val (Integer 1)))

    
    -- Right tests

    test "fromSExpression Right test 1" (fromSExpression $S.List[S.Symbol "right", (S.List[S.Symbol "pair", (S.Integer 5), (S.Real 5.5)])])
     (Right (Pair (Val (Integer 5)) (Val (Float 5.5))))                       

    test "fromSExpression Right test 2" (fromSExpression $S.List[S.Symbol "right", (S.List[S.Symbol "pair", (S.Boolean True), (S.Real 5.5)])])
     (Right (Pair (Val (Boolean True)) (Val (Float 5.5))))  

    test "fromSExpression Right test 3" (fromSExpression $S.List[S.Symbol "right", (S.List[(S.Symbol "pair"),  (S.Integer 4), (S.List[(S.Symbol "+"), (S.Integer 2), (S.Integer 1)])])])
      (Right (Pair (Val (Integer 4)) (App [Var "+", (Val (Integer 2)), (Val (Integer 1))])))

    test "fromSExpression Right test 4" (fromSExpression $S.List[(S.Symbol "right"), (S.Integer 1)]) (Right (Val (Integer 1)))

    --Real_Pred tests

    test "fromSExpression Real? test 1" (fromSExpression $ S.List[(S.Symbol "real?"), (S.Integer 1)]) (Real_Pred (Val (Integer 1)))

    test "fromSExpression Real? test 2" (fromSExpression $ S.List[(S.Symbol "real?"), (S.Real 1.0)]) (Real_Pred (Val (Float 1.0)))
    
    test "fromSExpression Real? test 3" (fromSExpression $ S.List[(S.Symbol "real?"), (S.Boolean True)]) (Real_Pred (Val (Boolean True)))
    
    test "fromSExpression Real? test 4" (fromSExpression $ S.List[(S.Symbol "real?"), (S.List[S.Symbol "right", 
     (S.List[S.Symbol "pair", (S.List[S.Symbol "+", (S.Integer 2), (S.Integer 1)]), (S.Integer 4)])])])
     (Real_Pred (Right (Pair (App [Var "+", (Val (Integer 2)), (Val (Integer 1))])  (Val (Integer 4)))))
    
     --Integer_Pred tests

    test "fromSExpression Integer? test 1" (fromSExpression $ S.List[(S.Symbol "integer?"), (S.Integer 1)]) (Integer_Pred (Val (Integer 1)))

    test "fromSExpression Integer? test 2" (fromSExpression $ S.List[(S.Symbol "integer?"), (S.Real 1.0)]) (Integer_Pred (Val (Float 1.0)))
    
    test "fromSExpression Integer? test 3" (fromSExpression $ S.List[(S.Symbol "integer?"), (S.Boolean True)]) (Integer_Pred (Val (Boolean True)))
  
    test "fromSExpression Integer? test 4" (fromSExpression $ S.List[(S.Symbol "integer?"), (S.List[S.Symbol "right", 
     (S.List[S.Symbol "pair", (S.List[S.Symbol "+", (S.Integer 2), (S.Integer 1)]), (S.Integer 4)])])])
     (Integer_Pred (Right (Pair (App [Var "+", (Val (Integer 2)), (Val (Integer 1))])  (Val (Integer 4)))))

    --Number_Pred tests

    test "fromSExpression Number? test 1" (fromSExpression $ S.List[(S.Symbol "number?"), (S.Integer 1)]) (Number_Pred (Val (Integer 1)))

    test "fromSExpression Number? test 2" (fromSExpression $ S.List[(S.Symbol "number?"), (S.Real 1.0)]) (Number_Pred (Val (Float 1.0)))
    
    test "fromSExpression Number? test 3" (fromSExpression $ S.List[(S.Symbol "number?"), (S.Boolean True)]) (Number_Pred (Val (Boolean True)))
    
    test "fromSExpression Number? test 4" (fromSExpression $ S.List[(S.Symbol "number?"), (S.List[S.Symbol "right", 
     (S.List[S.Symbol "pair", (S.List[S.Symbol "+", (S.Integer 2), (S.Integer 1)]), (S.Integer 4)])])])
     (Number_Pred (Right (Pair (App [Var "+", (Val (Integer 2)), (Val (Integer 1))])  (Val (Integer 4)))))

    --Boolean_Pred tests

    test "fromSExpression Boolean? test 1" (fromSExpression $ S.List[(S.Symbol "boolean?"), (S.Integer 1)]) (Boolean_Pred (Val (Integer 1)))

    test "fromSExpression Boolean? test 2" (fromSExpression $ S.List[(S.Symbol "boolean?"), (S.Real 1.0)]) (Boolean_Pred (Val (Float 1.0)))
    
    test "fromSExpression Boolean? test 3" (fromSExpression $ S.List[(S.Symbol "boolean?"), (S.Boolean True)]) (Boolean_Pred (Val (Boolean True)))
    
    test "fromSExpression Boolean? test 4" (fromSExpression $ S.List[(S.Symbol "boolean?"), (S.List[S.Symbol "right", 
     (S.List[S.Symbol "pair", (S.List[S.Symbol "+", (S.Integer 2), (S.Integer 1)]), (S.Integer 4)])])])
     (Boolean_Pred (Right (Pair (App [Var "+", (Val (Integer 2)), (Val (Integer 1))]) (Val (Integer 4)))))

    --Pair_Pred tests

    test "fromSExpression Pair? test 1" (fromSExpression $ S.List[(S.Symbol "pair?"), (S.Integer 1)]) (Pair_Pred (Val (Integer 1)))

    test "fromSExpression Pair? test 2" (fromSExpression $ S.List[(S.Symbol "pair?"), (S.Real 1.0)]) (Pair_Pred (Val (Float 1.0)))
    
    test "fromSExpression Pair? test 3" (fromSExpression $ S.List[(S.Symbol "pair?"), (S.Boolean True)]) (Pair_Pred (Val (Boolean True)))
    
    test "fromSExpression Pair? test 4" (fromSExpression $ S.List[(S.Symbol "pair?"), (S.List[S.Symbol "right", 
     (S.List[S.Symbol "pair", (S.List[S.Symbol "+", (S.Integer 2), (S.Integer 1)]), (S.Integer 4)])])])
     (Pair_Pred (Right (Pair (App [Var "+", (Val (Integer 2)), (Val (Integer 1))]) (Val (Integer 4)))))

    test "fromSExpression Pair? test 5" (fromSExpression $ S.List[S.Symbol "pair?", S.List[S.Symbol "pair", (S.Integer 1), (S.Integer 2)]])
     (Pair_Pred (Pair (Val (Integer 1)) (Val (Integer 2))))

    -- tests for Lambda
    test "fromSExpression Lambda 1" (fromSExpression (S.List[S.Symbol "lambda", S.List[S.Symbol "x"], S.Symbol "x"])) (Lambda ["x"] (Var "x"))
    test "fromSExpresssion Lambda 2" (fromSExpression (S.List[S.Symbol "lambda", S.List[S.Symbol "x", S.Symbol "y"], S.List[S.Symbol "+", S.Symbol "x", S.Symbol "y"]])) 
       (Lambda ["x", "y"] (App [Var "+", Var "x", Var "y"]))
    test "fromSExpression Lambda 3" (fromSExpression (S.List[S.Symbol "lambda", S.List[S.Symbol "vars"], S.List[S.Symbol "pair", S.Symbol "x", S.Boolean True]])) 
       (Lambda ["vars"] (Pair (Var "x") (Val (Boolean True))))

    -- tests for App 
    test "fromSExpression App 1" (fromSExpression (S.List[S.Symbol "double", S.Integer 2])) (App [Var "double", (Val (Integer 2))])
    test "fromSExpression App 2" (fromSExpression (S.List[S.Symbol "f", S.Symbol "x", S.Symbol "y", S.Symbol "z"]))  (App [Var "f", Var "x", Var "y", Var "z"])
    test "fromSExpression App 3" (fromSExpression (S.List[S.Symbol"constant"])) (App [Var "constant"])


-- |Convert a protoScheme expression into its s-expression representation
toSExpression :: Expr -> S.Expr
toSExpression (Val (Integer i)) = S.Integer i 
toSExpression (Val (Boolean b)) = S.Boolean b
toSExpression (Val (Float f)) = S.Real f 
toSExpression (Var v) = S.Symbol v 
toSExpression (Left x) = S.List[S.Symbol "left", toSExpression x]
toSExpression (Right x) = S.List[S.Symbol "right", toSExpression x]
toSExpression (Pair x y) = S.List[S.Symbol "pair", (toSExpression x), (toSExpression y)]
toSExpression (And x y) = S.List [S.Symbol "and", (toSExpression x), (toSExpression y)]
toSExpression (Or x y) = S.List [S.Symbol "or", (toSExpression x), (toSExpression y)]
toSExpression (Boolean_Pred x) = S.List[S.Symbol "boolean?", (toSExpression x)]
toSExpression (Integer_Pred x) = S.List[S.Symbol "integer?", (toSExpression x)]
toSExpression (Real_Pred x) = S.List[S.Symbol "real?", (toSExpression x)]
toSExpression (Number_Pred x) = S.List[S.Symbol "number?", (toSExpression x)]
toSExpression (Pair_Pred x) = S.List[S.Symbol "pair?", (toSExpression x)]
toSExpression (Let v x y) = S.List [S.Symbol "let", S.List [S.Symbol v, toSExpression x], toSExpression y]
toSExpression (If x y z) = S.List [S.Symbol "if", toSExpression x, toSExpression y, toSExpression z]
toSExpression (Cond x Nothing) = S.List [S.Symbol "cond", S.List (toSExpressionTupleListHelper x), S.Symbol "Nothing"]
toSExpression (Cond x (Just e)) = S.List [S.Symbol "cond", 
 S.List (toSExpressionTupleListHelper x), (toSExpression e)]
toSExpression (Lambda vars body) = S.List [S.Symbol "lambda", S.List (listOfVariablesToSExpressionList vars), toSExpression body]
toSExpression (App (func: args)) = S.List (toSExpression func : listToSExpressionList args)

-- Function for converting each S.Expr argument for the Call
listToSExpressionList :: [Expr] -> [S.Expr]
listToSExpressionList [] = [] 
listToSExpressionList (x:xs) = (toSExpression x) : (listToSExpressionList xs)

listOfVariablesToSExpressionList :: [Variable] -> [S.Expr]
listOfVariablesToSExpressionList [] = [] 
listOfVariablesToSExpressionList (x:xs) = (S.Symbol x) : (listOfVariablesToSExpressionList xs)

-- Function that assists the toSExpression function by handling a list of 
-- the Expr tuples and converting them to a list of S.Expr where a S.List [t1, t1] is how to represent a tuple.  
toSExpressionTupleListHelper :: [(Expr, Expr)] -> [S.Expr]
toSExpressionTupleListHelper [] = []
toSExpressionTupleListHelper ((t1, t2):ts) = S.List [toSExpression t1, toSExpression t2] : toSExpressionTupleListHelper ts

test_toSExpressionTupleListHelper = do 
    test "toSExpressionTupleListHelper basic test" (toSExpressionTupleListHelper []) [] 

    test "toSExpressionTupleListHelper complex test 1" (toSExpressionTupleListHelper [(Val (Integer 1), Val (Float 5.6))]) 
     [S.List [S.Integer 1, S.Real 5.6]]

    test "toSExpressionTupleListHelper complex test 2" (toSExpressionTupleListHelper 
     [(Val (Integer 1), Val (Float 5.6)), (Val (Boolean False), Val (Boolean True))]) 
      [S.List [S.Integer 1, S.Real 5.6], S.List [S.Boolean False, S.Boolean True]] 

    test "toSExpressionTupleListHelper complex test 3" (toSExpressionTupleListHelper 
     [(Val (Integer 1), Val (Float 5.6))]) 
      [S.List [S.Integer 1, S.Real 5.6]]   

test_toSExpression = do
  test "toSExpression true" (toSExpression (Val (Boolean True))) (S.Boolean True)
  test "toSExpression false" (toSExpression (Val (Boolean False))) (S.Boolean False)
  test "toSExpression (Var x)" (toSExpression (Var "x")) (S.Symbol "x")

  --Base cases
  test "toSExpression (10)" (toSExpression (Val (Integer 10))) (S.Integer 10)
  test "toSExpression (10.1)" (toSExpression (Val (Float 10.1))) (S.Real 10.1)
  test "toSExpression (Var x)" (toSExpression (Var "x")) (S.Symbol "x")

--     -- Basic Boolean tests
  test "toSExpression (+ True 14)"
        (toSExpression $ App [Var "+", (Val (Boolean True)), (Val (Integer 14))])
        (S.List [S.Symbol "+", (S.Boolean True), (S.Integer 14)])
  test "toSExpression (- 32.1 False)"
        (toSExpression $ App [Var "-", (Val (Float 32.1)), (Val (Boolean False))])
        (S.List [S.Symbol "-", S.Real 32.1, S.Boolean False])
  test "toSExpression (* 10.2 True)"
        (toSExpression $ App [Var "*", (Val (Float 10.2)), (Val (Boolean True))])
        (S.List [S.Symbol "*", S.Real 10.2, S.Boolean True])
  test "toSExpression (/ False 5.6)"
        (toSExpression $ App [Var "/", (Val (Boolean False)), (Val (Float 5.6))])
        (S.List [S.Symbol "/", S.Boolean False, S.Real 5.6])
  test "toSExpression (+ (* 10.2 False) (- True 2.1)"
        (toSExpression $ App [Var "+", (App [Var "*", (Val (Float 10.2)), (Val (Boolean False))]), (App [Var "-", (Val (Boolean True)), (Val (Float 2.1))])])
        (S.List [S.Symbol "+", (S.List [S.Symbol "*", S.Real 10.2, S.Boolean False]),
          (S.List [S.Symbol "-", S.Boolean True, S.Real 2.1])])

--     --Addition with Integers and Reals
  test "toSExpression (+ 32 14)"
        (toSExpression $ App [Var "+", (Val (Integer 32)), (Val (Integer 14))])
        (S.List [S.Symbol "+", S.Integer 32, S.Integer 14])
  test "toSExpression (+ 32.1 14)"
        (toSExpression $ App [Var "+", (Val (Float 32.1)), (Val (Integer 14))])
        (S.List [S.Symbol "+", S.Real 32.1, S.Integer 14])
  test "toSExpression (+ 32.1 14.5)"
        (toSExpression $ App [Var "+", (Val (Float 32.1)), (Val (Float 14.5))])
        (S.List [S.Symbol "+", S.Real 32.1, S.Real 14.5])

--     --Subtraction with Integers and Reals
  test "toSExpression (- 32 14)"
        (toSExpression $ App [Var "-", (Val (Integer 32)), (Val (Integer 14))])
        (S.List [S.Symbol "-", S.Integer 32, S.Integer 14])
  test "toSExpression (- 32.1 14)"
        (toSExpression $ App [Var "-", (Val (Float 32.1)), (Val (Integer 14))])
        (S.List [S.Symbol "-", S.Real 32.1, S.Integer 14])
  test "toSExpression (- 32.1 14.5)"
       (toSExpression $ App [Var "-", (Val (Float 32.1)), (Val (Float 14.5))])
        (S.List [S.Symbol "-", S.Real 32.1, S.Real 14.5])
    
--     --Multiplication with Integers and Reals
  test "toSExpression (* 10 5)"
        (toSExpression $ App [Var "*", (Val (Integer 10)), (Val (Integer 5))])
        (S.List [S.Symbol "*", S.Integer 10, S.Integer 5])
  test "toSExpression (* 10.2 5)"
        (toSExpression $ App [Var "*", (Val (Float 10.2)), (Val (Integer 5))])
        (S.List [S.Symbol "*", S.Real 10.2, S.Integer 5])
  test "toSExpression (* 10.2 5.6)"
        (toSExpression $ App [Var "*", (Val (Float 10.2)), (Val (Float 5.6))])
        (S.List [S.Symbol "*", S.Real 10.2, S.Real 5.6])

--     --Division with Integers and Reals
  test "toSExpression (/ 10 5)"
        (toSExpression $ App [Var "/", (Val (Integer 10)), (Val (Integer 5))])
        (S.List [S.Symbol "/", S.Integer 10, S.Integer 5])
  test "toSExpression (/ 10.2 5)"
        (toSExpression $ App [Var "/", (Val (Float 10.2)), (Val (Integer 5))])
        (S.List [S.Symbol "/", S.Real 10.2, S.Integer 5])
  test "toSExpression (/ 10.2 5.6)"
        (toSExpression $ App [Var "/", (Val (Float 10.2)), (Val (Float 5.6))])
        (S.List [S.Symbol "/", S.Real 10.2, S.Real 5.6])


--     -- Let tests
  test "toSExpression let x 0, 1 + x" (toSExpression (Let "x" (Val (Integer 0)) (App [Var "+", (Val (Integer 1)), (Var "x")]))) 
        (S.List[S.Symbol "let", S.List [S.Symbol "x", S.Integer 0], (S.List[S.Symbol "+", S.Integer 1, S.Symbol "x"])])
        
  test "toSExpression let x 2, 1 + 3" (toSExpression (Let "x" (Val (Integer 2)) (App [Var "+", (Val (Integer 1)), (Val (Integer 3))])))
        (S.List[S.Symbol "let", S.List [S.Symbol "x", S.Integer 2], (S.List[S.Symbol "+", S.Integer 1, S.Integer 3])])
        
  test "toSExpression let y 1.5, 1 * y" (toSExpression (Let "y" (Val (Float 1.5)) (App [Var "*", (Val (Integer 1)), (Var "y")])))
        (S.List[S.Symbol "let", S.List [S.Symbol "y", S.Real 1.5], (S.List[S.Symbol "*", S.Integer 1, S.Symbol "y"])])
        
  test "toSExpression let y 3.2, 1 / y" (toSExpression (Let "y" (Val (Float 3.2))  (App [Var "/", (Val (Integer 1)), (Var "y")])))
        (S.List[S.Symbol "let", S.List [S.Symbol "y", S.Real 3.2], (S.List[S.Symbol "/", S.Integer 1, S.Symbol "y"])])

--     -- If tests 
  test "toSExpression if simple" 
        (toSExpression (If (Val (Boolean True)) (Val (Integer 1)) (Val (Float 2.0))))
        (S.List [S.Symbol "if", S.Boolean True, S.Integer 1, S.Real 2.0])      
  test "toSExpression if complex 1" 
        (toSExpression (If (Val (Boolean True)) (App [Var "+", (Val (Integer 1)), (Val (Float 2.0))]) (Var "x")))
        (S.List [S.Symbol "if", S.Boolean True, S.List [S.Symbol "+", S.Integer 1, S.Real 2.0], S.Symbol "x"])    
  test "toSExpression if complex 2" 
        (toSExpression (If (Val (Boolean False)) (Let "y" (Val (Integer 1)) (Var "y")) (App [Var "/", (Val (Integer 10)), (Val (Integer 2))])))
        (S.List [S.Symbol "if", S.Boolean False, S.List [S.Symbol "let", S.List [S.Symbol "y" , S.Integer 1], S.Symbol "y"], S.List [S.Symbol "/", S.Integer 10, S.Integer 2]])   

--     -- And tests
  test "toSExpression And Test 1" (toSExpression $ And (Val (Boolean True)) (Val (Integer 10)))
      (S.List [S.Symbol "and" , S.Boolean True, S.Integer 10]) 
          
  test "toSExpression And Test 2" (toSExpression $ (And (Val (Boolean False))
      (Let "x" (App [Var "+", (Val (Float 10.1)), (Val (Float 4.1))]) (App [Var "+", (Var "x"), (Val (Float 1.1))]))))
        (S.List [S.Symbol "and" , S.Boolean False, S.List [S.Symbol "let", S.List [S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "+", S.Symbol "x", S.Real 1.1]]])
            

--     -- Or tests
  test "toSExpression Or Test 1" (toSExpression $ App [Var "or", (Val (Boolean True)), (Val (Integer 10))])
      (S.List [S.Symbol "or" , S.Boolean True, S.Integer 10]) 
                 
  test "toSExpression Or Test 2" (toSExpression $ App [Var "or", (App [Var "or", (Val (Integer 10)), (Val (Float 15.1))]),
      (Let "x" (App [Var "+", (Val (Float 10.1)), (Val (Float 4.1))]) (And (Var "x") (Val (Float 1.1))))])
         (S.List [S.Symbol "or" , S.List [S.Symbol "or" , S.Integer 10, S.Real 15.1], 
          S.List [S.Symbol "let", S.List [S.Symbol "x", S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], 
           S.List [S.Symbol "and", S.Symbol "x", S.Real 1.1]]])    

--     -- Not tests
  test "toSExpression Not Test 1" (toSExpression $ App [Var "not", (Val (Boolean True))])
      (S.List [S.Symbol "not" , S.Boolean True]) 

  test "toSExpression Not Test 2" (toSExpression $ App [Var "not", (App [Var "or", (Val (Integer 10)),
       (Let "x" (App [Var "+", (Val (Float 10.1)), (Val (Float 4.1))]) (And (Var "x") (Val (Float 1.1))))])])  
         (S.List [S.Symbol "not" , S.List [S.Symbol "or" , S.Integer 10, S.List [S.Symbol "let", S.List [S.Symbol "x",
          S.List [S.Symbol "+", S.Real 10.1, S.Real 4.1]], S.List [S.Symbol "and", S.Symbol "x", S.Real 1.1]]]]) 

--     -- Less_Than Tests
  test "toSExpression Less_Than Test 1" (toSExpression $ App [Var "<", (Val (Integer 7)), (Val (Integer 6))])
        (S.List [S.Symbol "<", S.Integer 7, S.Integer 6]) 

  test "toSExpression Less_Than Test 2" (toSExpression $ App [Var "<", (Val (Integer 6)), (Val (Integer 7))])
        (S.List [S.Symbol "<", S.Integer 6, S.Integer 7]) 
    
  test "toSExpression Less_Than Test 3" (toSExpression $ App [Var "<", (Val (Float 6.8)), (Val (Float 6.3))]) 
        (S.List [S.Symbol "<", S.Real 6.8, S.Real 6.3])
    
  test "toSExpression Less_Than Test 4" (toSExpression $ App [Var "<", (Val (Boolean True)), (Val (Float 6.3))]) 
        (S.List [S.Symbol "<", S.Boolean True, S.Real 6.3])
    
  test "toSExpression Less_Than Test 5" (toSExpression $ App [Var "<", (App [Var "+", (Val (Integer 7)), (Val (Integer 6))]), (Var "x")])
        (S.List [S.Symbol "<", S.List[S.Symbol "+", S.Integer 7, S.Integer 6], S.Symbol "x"])

  test "toSExpression Less_Than Test 6" (toSExpression $ App [Var "<", (If (Val (Boolean True)) (Val (Boolean True)) (Val (Boolean False))), (Let "v" (Val (Float 6.3)) (Val (Float 6.3)))])
        (S.List [S.Symbol "<", S.List [S.Symbol "if", S.Boolean True, S.Boolean True, S.Boolean False],
          S.List[S.Symbol "let", S.List [S.Symbol "v", S.Real 6.3], S.Real 6.3]])

--   -- Greater_Than Tests
  test "toSExpression Greater_Than Test 1" (toSExpression $ App [Var ">", (Val (Integer 7)), (Val (Integer 6))])
        (S.List [S.Symbol ">", S.Integer 7, S.Integer 6]) 

  test "toSExpression Greater_Than Test 2" (toSExpression $ App [Var ">", (Val (Integer 6)), (Val (Integer 7))]) 
        (S.List [S.Symbol ">", S.Integer 6, S.Integer 7]) 
    
  test "toSExpression Greater_Than Test 3" (toSExpression $  App [Var ">", (Val (Float 6.8)), (Val (Float 6.3))]) 
        (S.List [S.Symbol ">", S.Real 6.8, S.Real 6.3])
    
  test "toSExpression Greater_Than Test 4" (toSExpression $ App [Var ">", (Val (Boolean True)), (Val (Float 6.3))])
        (S.List [S.Symbol ">", S.Boolean True, S.Real 6.3])
    
  test "toSExpression Greater_Than Test 5" (toSExpression $ App [Var ">", (App [Var "+", (Val (Integer 7)), (Val (Integer 6))]), (Var "x")])
        (S.List [S.Symbol ">", S.List[S.Symbol "+", S.Integer 7, S.Integer 6], S.Symbol "x"])

  test "toSExpression Greater_Than Test 6" (toSExpression $ App [Var ">", (If (Val (Boolean True)) (Val (Boolean True)) (Val (Boolean False))), (Let "v" (Val (Float 6.3)) (Val (Float 6.3)))])
        (S.List [S.Symbol ">", S.List [S.Symbol "if", S.Boolean True, S.Boolean True, S.Boolean False],
          S.List[S.Symbol "let", S.List [S.Symbol "v", S.Real 6.3], S.Real 6.3]])

--  -- Equal To Tests
  test "toSExpression Equal_To Test 1" (toSExpression $ App [Var "=", (Val (Integer 7)), (Val (Integer 6))])
        (S.List [S.Symbol "=", S.Integer 7, S.Integer 6]) 

  test "toSExpression Equal_To Test 2" (toSExpression $ App [Var "=", (Val (Integer 6)), (Val (Integer 7))])
        (S.List [S.Symbol "=", S.Integer 6, S.Integer 7]) 
    
  test "toSExpression Equal_To Test 3" (toSExpression $ App [Var "=", (Val (Float 6.8)), (Val (Float 6.3))])  
        (S.List [S.Symbol "=", S.Real 6.8, S.Real 6.3])
    
  test "toSExpression Equal_To Test 4" (toSExpression $  App [Var "=", (Val (Boolean True)), (Val (Float 6.3))])
        (S.List [S.Symbol "=", S.Boolean True, S.Real 6.3])
    
  test "toSExpression Equal_To Test 5" (toSExpression $ App [Var "=", (App [Var "+", (Val (Integer 7)), (Val (Integer 6))]), (Var "x")])
        (S.List [S.Symbol "=", S.List[S.Symbol "+", S.Integer 7, S.Integer 6], S.Symbol "x"])

  test "toSExpression Equal_To Test 6" (toSExpression $ App [Var "=", (If (Val (Boolean True)) (Val (Boolean True)) (Val (Boolean False))), (Let "v" (Val (Float 6.3)) (Val (Float 6.3)))])
        (S.List [S.Symbol "=", S.List [S.Symbol "if", S.Boolean True, S.Boolean True, S.Boolean False],
          S.List[S.Symbol "let", S.List [S.Symbol "v", S.Real 6.3], S.Real 6.3]])

--   -- <= Tests
  test "toSExpression <= Test 1" (toSExpression $ App [Var "<=", (Val (Integer 7)), (Val (Integer 6))])
        (S.List [S.Symbol "<=", S.Integer 7, S.Integer 6]) 

  test "toSExpression <=  Test 2" (toSExpression $ App [Var "<=", (Val (Integer 6)), (Val (Integer 7))])
        (S.List [S.Symbol "<=", S.Integer 6, S.Integer 7]) 
    
  test "toSExpression <= Test 3" (toSExpression $ App [Var "<=", (Val (Float 6.8)), (Val (Float 6.3))])  
        (S.List [S.Symbol "<=", S.Real 6.8, S.Real 6.3])
    
  test "toSExpression <=  Test 4" (toSExpression $  App [Var "<=", (Val (Boolean True)), (Val (Float 6.3))])
        (S.List [S.Symbol "<=", S.Boolean True, S.Real 6.3])
    
  test "toSExpression <=  Test 5" (toSExpression $ App [Var "<=", (App [Var "+", (Val (Integer 7)), (Val (Integer 6))]), (Var "x")])
        (S.List [S.Symbol "<=", S.List[S.Symbol "+", S.Integer 7, S.Integer 6], S.Symbol "x"])

  test "toSExpression <=  Test 6" (toSExpression $ App [Var "<=", (If (Val (Boolean True)) (Val (Boolean True)) (Val (Boolean False))), (Let "v" (Val (Float 6.3)) (Val (Float 6.3)))])
        (S.List [S.Symbol "<=", S.List [S.Symbol "if", S.Boolean True, S.Boolean True, S.Boolean False],
          S.List[S.Symbol "let", S.List [S.Symbol "v", S.Real 6.3], S.Real 6.3]])

--    -- >= Tests
  test "toSExpression >= Test 1" (toSExpression $ App [Var ">=", (Val (Integer 7)), (Val (Integer 6))])
        (S.List [S.Symbol ">=", S.Integer 7, S.Integer 6]) 

  test "toSExpression >= Test 2" (toSExpression $ App [Var ">=", (Val (Integer 6)), (Val (Integer 7))])
        (S.List [S.Symbol ">=", S.Integer 6, S.Integer 7]) 
    
  test "toSExpression >= Test 3" (toSExpression $ App [Var ">=", (Val (Float 6.8)), (Val (Float 6.3))])  
        (S.List [S.Symbol ">=", S.Real 6.8, S.Real 6.3])
    
  test "toSExpression >= Test 4" (toSExpression $  App [Var ">=", (Val (Boolean True)), (Val (Float 6.3))])
        (S.List [S.Symbol ">=", S.Boolean True, S.Real 6.3])
    
  test "toSExpression >= Test 5" (toSExpression $ App [Var ">=", (App [Var "+", (Val (Integer 7)), (Val (Integer 6))]), (Var "x")])
        (S.List [S.Symbol ">=", S.List[S.Symbol "+", S.Integer 7, S.Integer 6], S.Symbol "x"])

  test "toSExpression >= Test 6" (toSExpression $ App [Var ">=", (If (Val (Boolean True)) (Val (Boolean True)) (Val (Boolean False))), (Let "v" (Val (Float 6.3)) (Val (Float 6.3)))])
        (S.List [S.Symbol ">=", S.List [S.Symbol "if", S.Boolean True, S.Boolean True, S.Boolean False],
          S.List[S.Symbol "let", S.List [S.Symbol "v", S.Real 6.3], S.Real 6.3]])

--   -- Cond Tests 
  
  test "toSExpression Cond basic test" (toSExpression (Cond [] Nothing)) (S.List [S.Symbol "cond", S.List [], S.Symbol "Nothing"])

  test "toSExpression Cond complex test 1" (toSExpression (Cond [((Val (Integer 1)), (Val (Float 5.6)))] Nothing)) 
     (S.List [S.Symbol "cond", S.List [S.List [S.Integer 1, S.Real 5.6]], S.Symbol "Nothing"])

  test "toSExpression Cond complex test 2" (toSExpression (Cond [((Val (Integer 1)), (Val (Float 5.6))), ((Val (Boolean True)), (Val (Integer 20)))] Nothing)) 
     (S.List [S.Symbol "cond", S.List [S.List [S.Integer 1, S.Real 5.6], S.List [S.Boolean True, S.Integer 20]], 
       S.Symbol "Nothing"]) 

  test "toSExpression Cond with an else" (toSExpression (Cond [(Val (Integer 1), Val (Float 5.6))] (Just (Val (Integer 20))))) 
     (S.List [S.Symbol "cond", S.List [S.List [S.Integer 1, S.Real 5.6]], S.Integer 20])          

--     -- Pair tests

  test "toSExpression Pair test 1" (toSExpression (Pair (Val (Integer 5)) (Val (Float 5.5)))) (S.List[S.Symbol "pair", (S.Integer 5), (S.Real 5.5)])                       

  test "toSExpression Pair test 2" (toSExpression (Pair (Val (Boolean True)) (Val (Float 5.5)))) (S.List[S.Symbol "pair", (S.Boolean True), (S.Real 5.5)])  

  test "toSExpression Pair test 3" (toSExpression (If (Val (Boolean True)) (Pair (App [Var "+", (Val (Integer 2)), (Val (Integer 1))]) (Val (Integer 4))) 
     (Pair (Val (Float 3.2)) (Val (Boolean False)))))
      (S.List[(S.Symbol "if"), (S.Boolean True), (S.List[(S.Symbol "pair"),
      (S.List[(S.Symbol "+"), (S.Integer 2), (S.Integer 1)]), (S.Integer 4)]), (S.List[(S.Symbol "pair"), (S.Real 3.2), (S.Boolean False)])])
     

--     -- Left tests

  test "toSExpression Left test 1" (toSExpression (Left (Pair (Val (Integer 5)) (Val (Float 5.5)))))                       
      (S.List[S.Symbol "left", (S.List[S.Symbol "pair", (S.Integer 5), (S.Real 5.5)])])

  test "toSExpression Left test 2" (toSExpression (Left (Pair (Val (Boolean True)) (Val (Float 5.5)))))
      (S.List[S.Symbol "left", (S.List[S.Symbol "pair", (S.Boolean True), (S.Real 5.5)])]) 

  test "toSExpression Left test 3" (toSExpression (Left (Pair (Val (Integer 4)) (App [Var "+", (Val (Integer 2)), (Val (Integer 1))]))))
      (S.List[S.Symbol "left", (S.List[(S.Symbol "pair"),  (S.Integer 4), (S.List[(S.Symbol "+"), (S.Integer 2), (S.Integer 1)])])])

  test "toSExpression Left test 4" (toSExpression (Left (Val (Integer 1)))) (S.List[(S.Symbol "left"), (S.Integer 1)])

    
--     -- Right tests

  test "toSExpression Right test 1" (toSExpression (Right (Pair (Val (Integer 5)) (Val (Float 5.5)))))     
      (S.List[S.Symbol "right", (S.List[S.Symbol "pair", (S.Integer 5), (S.Real 5.5)])])               

  test "toSExpression Right test 2" (toSExpression (Right (Pair (Val (Boolean True)) (Val (Float 5.5)))))
      (S.List[S.Symbol "right", (S.List[S.Symbol "pair", (S.Boolean True), (S.Real 5.5)])])  

  test "toSExpression Right test 3" (toSExpression (Right (Pair (Val (Integer 4)) (App [Var "+", (Val (Integer 2)), (Val (Integer 1))]))))
      (S.List[S.Symbol "right", (S.List[(S.Symbol "pair"),  (S.Integer 4), (S.List[(S.Symbol "+"), (S.Integer 2), (S.Integer 1)])])])
    
  test "toSExpression Right test 4" (toSExpression (Right (Val (Integer 1)))) (S.List[(S.Symbol "right"), (S.Integer 1)])

    --Real_Pred tests

  test "toSExpression Real? test 1" (toSExpression  (Real_Pred (Val (Integer 1)))) (S.List[(S.Symbol "real?"), (S.Integer 1)])

  test "toSExpression Real? test 2" (toSExpression (Real_Pred (Val (Float 1.0)))) (S.List[(S.Symbol "real?"), (S.Real 1.0)])
    
  test "toSExpression Real? test 3" (toSExpression (Real_Pred (Val (Boolean True)))) (S.List[(S.Symbol "real?"), (S.Boolean True)])
    
  test "toSExpression Real? test 4" (toSExpression (Real_Pred (Right (Pair (App [Var "+", (Val (Integer 2)), (Val (Integer 1))]) (Val (Integer 4))))))
      (S.List[(S.Symbol "real?"), (S.List[S.Symbol "right", 
      (S.List[S.Symbol "pair", (S.List[S.Symbol "+", (S.Integer 2), (S.Integer 1)]), (S.Integer 4)])])])
    
--      --Integer_Pred tests

  test "toSExpression Integer? test 1" (toSExpression (Integer_Pred (Val (Integer 1)))) (S.List[(S.Symbol "integer?"), (S.Integer 1)])

  test "toSExpression Integer? test 2" (toSExpression (Integer_Pred (Val (Float 1.0)))) (S.List[(S.Symbol "integer?"), (S.Real 1.0)])
    
  test "toSExpression Integer? test 3" (toSExpression (Integer_Pred (Val (Boolean True)))) (S.List[(S.Symbol "integer?"), (S.Boolean True)])
    
  test "toSExpression Integer? test 4" (toSExpression (Integer_Pred (Right (Pair (App [Var "+", (Val (Integer 2)), (Val (Integer 1))]) (Val (Integer 4))))))
      (S.List[(S.Symbol "integer?"), (S.List[S.Symbol "right", 
     (S.List[S.Symbol "pair", (S.List[S.Symbol "+", (S.Integer 2), (S.Integer 1)]), (S.Integer 4)])])])

--     --Number_Pred tests

  test "toSExpression Number? test 1" (toSExpression (Number_Pred (Val (Integer 1)))) (S.List[(S.Symbol "number?"), (S.Integer 1)])

  test "toSExpression Number? test 2" (toSExpression (Number_Pred (Val (Float 1.0)))) (S.List[(S.Symbol "number?"), (S.Real 1.0)])
    
  test "toSExpression Number? test 3" (toSExpression (Number_Pred (Val (Boolean True)))) (S.List[(S.Symbol "number?"), (S.Boolean True)])
    
  test "toSExpression Number? test 4" (toSExpression (Number_Pred (Right (Pair (App [Var "+", (Val (Integer 2)), (Val (Integer 1))]) (Val (Integer 4))))))
      (S.List[(S.Symbol "number?"), (S.List[S.Symbol "right", 
      (S.List[S.Symbol "pair", (S.List[S.Symbol "+", (S.Integer 2), (S.Integer 1)]), (S.Integer 4)])])])

--     --Boolean_Pred tests

  test "toSExpression Boolean? test 1" (toSExpression (Boolean_Pred (Val (Integer 1)))) (S.List[(S.Symbol "boolean?"), (S.Integer 1)])

  test "toSExpression Boolean? test 2" (toSExpression (Boolean_Pred (Val (Float 1.0)))) (S.List[(S.Symbol "boolean?"), (S.Real 1.0)])
    
  test "toSExpression Boolean? test 3" (toSExpression (Boolean_Pred (Val (Boolean True)))) (S.List[(S.Symbol "boolean?"), (S.Boolean True)])
    
  test "toSExpression Boolean? test 4" (toSExpression (Boolean_Pred (Right (Pair (App [Var "+", (Val (Integer 2)), (Val (Integer 1))]) (Val (Integer 4))))))
      (S.List[(S.Symbol "boolean?"), (S.List[S.Symbol "right", 
      (S.List[S.Symbol "pair", (S.List[S.Symbol "+", (S.Integer 2), (S.Integer 1)]), (S.Integer 4)])])])

--     --Pair_Pred tests

  test "toSExpression Pair? test 1" (toSExpression (Pair_Pred (Val (Integer 1)))) (S.List[(S.Symbol "pair?"), (S.Integer 1)])

  test "toSExpression Pair? test 2" (toSExpression (Pair_Pred (Val (Float 1.0)))) (S.List[(S.Symbol "pair?"), (S.Real 1.0)])
    
  test "toSExpression Pair? test 3" (toSExpression (Pair_Pred (Val (Boolean True)))) (S.List[(S.Symbol "pair?"), (S.Boolean True)])
    
  test "toSExpression Pair? test 4" (toSExpression (Pair_Pred (Right (Pair (App [Var "+", (Val (Integer 2)), (Val (Integer 1))]) (Val (Integer 4))))))
      (S.List[(S.Symbol "pair?"), (S.List[S.Symbol "right", 
      (S.List[S.Symbol "pair", (S.List[S.Symbol "+", (S.Integer 2), (S.Integer 1)]), (S.Integer 4)])])])
 
  test "toSExpression Pair? test 5" (toSExpression (Pair_Pred (Pair (Val (Integer 1)) (Val (Integer 2)))))
      (S.List[S.Symbol "pair?", S.List[S.Symbol "pair", (S.Integer 1), (S.Integer 2)]])


-- tests for Lambda
  test "toSExpression Lambda 1" (toSExpression (Lambda ["x"] (Var "x"))) (S.List[S.Symbol "lambda", S.List[S.Symbol "x"], S.Symbol "x"])
  test "toSExpresssion Lambda 2" (toSExpression (Lambda ["x", "y"] (App [Var "+", Var "x", Var "y"])))
    (S.List[S.Symbol "lambda", S.List [S.Symbol "x", S.Symbol "y"], S.List[S.Symbol "+", S.Symbol "x", S.Symbol "y"]])
  test "toSExpression Lambda 3" (toSExpression (Lambda ["vars"] (Pair (Var "Var") (Val (Boolean True))))) 
    (S.List[S.Symbol "lambda", S.List[S.Symbol "vars"], S.List[S.Symbol "pair", S.Symbol "Var", S.Boolean True]])

-- tests for App 
  test "toSExpression App 1" (toSExpression (App [Var "double", (Val (Integer 2))])) (S.List[S.Symbol "double", S.Integer 2])
  test "toSExpression App 2" (toSExpression (App [Var "f", Var "x", Var "y", Var "z"])) (S.List[S.Symbol "f", S.Symbol "x", S.Symbol "y", S.Symbol "z"])
  test "toSExpression App 3" (toSExpression (App [Var "constant", Val (Boolean True)])) (S.List[S.Symbol"constant", S.Boolean True])

--  ===========================================================================================================

-- |Convert the evaluation result into the corresponding S-expression representation
valueToSExpression :: Value -> S.Expr
valueToSExpression (Integer i) = S.Integer i
valueToSExpression (Float r) = S.Real r
valueToSExpression (Boolean b) = S.Boolean b
valueToSExpression (PairVal x y) = S.Dotted (valueToSExpression x) (valueToSExpression y)
-- For closure, just get the variables, dont care about the body, dont care about env
valueToSExpression (Closure x _ _) = S.List (S.Symbol "Lambda" : listOfVariablesToSExpression x)
 where 
   listOfVariablesToSExpression :: [Variable] -> [S.Expr]
   listOfVariablesToSExpression [] = [] 
   listOfVariablesToSExpression (x:xs) = S.Symbol x : listOfVariablesToSExpression xs
valueToSExpression (PrimOp (Op x _) _) =  S.List [S.Symbol "Op", S.Symbol x]

test_valueToSExpression = do
    test "toSExpression 42"
        (valueToSExpression (Integer 42))
        (S.Integer 42)
    test "toSExpression 42.3"
        (valueToSExpression (Float 42.3))
        (S.Real 42.3)
    test "toSExpression 20"
        (valueToSExpression (Integer 20))
        (S.Integer 20)
    test "toSExpression 51.9"
        (valueToSExpression (Float 51.9))
        (S.Real 51.9)
    test "toSExpression True"
        (valueToSExpression (Boolean True))
        (S.Boolean True)
    test "toSExpression False"
        (valueToSExpression (Boolean False))
        (S.Boolean False)
    test "toSExpression Pair"
         (valueToSExpression (PairVal (Integer 5) (Boolean False)))
         (S.Dotted (S.Integer 5) (S.Boolean False))    
    test "toSExpression Closure"
        (valueToSExpression (Closure ["x"] (Val (Integer 5)) empty))
        (S.List [S.Symbol "Lambda",S.Symbol "x"])    
    test "toSExpression PrimOp"
        (valueToSExpression addOp)
        (S.List [S.Symbol "Op",S.Symbol "+"])                