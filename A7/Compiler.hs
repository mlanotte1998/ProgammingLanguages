{- |
Module      :  Compiler
Description :  Compiler from protoScheme into Pure Lambda Calculus (PLC).
Copyright   :  (c) <your names>

Maintainer  : <your emails>
-}

module Compiler 
    ( compile
    , compileProgram
    , factorialProgram
    , Compiler.allTests
    ) where

import Syntax
import Church
import qualified Lambda as L
import Reduce (normalize)

import SimpleTestsColor (test, testSection)

-- |Compile a protoScheme expression into PLC
compile :: Expr -> Maybe L.Lambda
compile = undefined                               -- TODO: replace with your definition

-- |Compile the given protoScheme program into PLC
compileProgram :: Program -> Maybe L.Lambda
compileProgram = undefined                        -- TODO: replace with your definition


-- |Generate the source code of a program calculating the factorial of the
-- given number
factorialProgram :: Integer -> String
factorialProgram number =                         -- TODO: complete the code below
  "... (defun fact (n) (...)) ... (fact " ++ show number ++ ") ... " 

test_factorial = undefined                        -- TODO: complete tests

countdownTo1Program = 
    "((defun down (n)\
    \   (if (= n 1)\
    \       n\
    \       (down (- n 1))))\
    \ (down 5))"

allTests = do
    test_factorial

