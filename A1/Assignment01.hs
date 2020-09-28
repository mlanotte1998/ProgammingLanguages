{- |
Module      :  Assignment01
Description :  Assignment 1 submission for CS 4400.
Copyright   :  (c) Michael Lanotte

Maintainer  :  lanotte.m@northeastern.edu
-}

module Assignment1 where

-- ====================================================================
-- Task 3 

-- Function that returns true if the given positive integer is odd and false otherwise.
isOdd :: Integer -> Bool 
isOdd x
        | x == 0 = False
        | x > 0 = not (isOdd (x - 1)) 

-- ====================================================================
-- Task 4 

-- Function that converts a list of booleans representing a binary number to a base 10 integer. (Return 0 for an empty list because returning undefined created an exception) 
binToInteger :: [Bool] -> Integer  
binToInteger [] = 0  
binToInteger x = binToIntHelper x 1

-- Helper function for binToInt that keeps track of the current binary number that each boolean in the list represents to compute the integer value of the list. 
binToIntHelper :: [Bool] -> Integer -> Integer
binToIntHelper [] y = 0 
binToIntHelper x y = (y * boolToInt (head x)) + (binToIntHelper (tail x) (y * 2))  

-- Helper function for converting a boolean to an integer (0 or 1). 
boolToInt :: Bool -> Integer
boolToInt False = 0
boolToInt True = 1

-- ======================================================================
-- Task 5 

-- Function that returns true if the given list of integers is sorted in descending order, false otherwise. 
isDescending :: [Integer] -> Bool
isDescending [] = True
isDescending x = if (length x == 1) 
                    then True else 
                    if head x > head (tail x) 
                    then isDescending(tail x)
                    else False  

-- =====================================================================
-- Task 6

-- Data representation of a binary tree that is either a Leaf/Empty or a Node that stores a value and then two (left/right) subtrees. 
data BinaryTree = Empty 
                | Node Integer BinaryTree BinaryTree

-- Function that sums the values of all nodes in a BinaryTree. 
sumTree :: BinaryTree -> Integer 
sumTree Empty = 0 
sumTree (Node x left right) = x + sumTree left + sumTree right

 
