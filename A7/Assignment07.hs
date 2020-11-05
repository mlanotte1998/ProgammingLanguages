{- |
Module : Assignment07
Description : Assignment 7 submission for CS 4400.
Copyright : (c) Michael Lanotte
                Rachel Johanek 
Maintainer : lanotte.m@northeastern.edu
             johanek.r@northeastern.edu 
-}

module Assignment07 where
    import Church 
    import Compiler

-- Solutions to question 7, our counts returned by normalizeWithCount
-- when run on the compiled factorial program with input 4 in Compiler.test_Program
--  fact4stepsBefore = 5938;
-- fact4stepsAfter = 3822;

--the main function runs all tests we wrote for the functionality of Church.hs and Compiler.hs
--including all implemented conversions and methods in Church and compile, compileProgram, and
--factorialProgram in Compiler
main :: IO () 
main = do 
    Church.allTests
    Compiler.allTests

