{- |
Module : Assignment02
Description : Assignment 2 submission for CS 4400.
Copyright : (c) Michael Lanotte
Maintainer : lanotte.m@northeastern.edu
-}

module Assignment02 where

import SimpleTests

-- ============================================================
-- Question 1

{- BNF

? means optional

<SExpr> ::= <Integer>
          | <Symbol>
          | ( <NonEmptyList>? )

<NonEmptyList> ::= <SExpr>
                 | <SExpr> <NonEmptyList>

-}

-- ============================================================
-- Question 2

-- Type representing an S-Expression
data SExpr = NumberExpr Integer
           | SymbolExpr String
           | ArrayExpr  [ SExpr ]
           deriving (Show, Eq)

{- Examples
These are the examples from the assignment description in my SExpr representation

(1 20 x 30 foo)
(ArrayExpr [ (NumberExpr 1), (NumberExpr 20), (SymbolExpr "x"), (NumberExpr 30), (SymbolExpr "foo") ])

(+ 13 23)
(ArrayExpr [ (SymbolExpr "+"), (NumberExpr 13), (NumberExpr 23) ] )

20
(NumberExpr 20)

(a b (c d))
(ArrayExpr [ (SymbolExpr "a"), (SymbolExpr "b"), (ArrayExpr [ (SymbolExpr "c"), (SymbolExpr "d") ] ) ] )

x
(SymbolExpr x)

(32 * (30 z) =)
(ArrayExpr [ (NumberExpr 32), (SymbolExpr "*"), (ArrayExpr [ (NumberExpr 30) , (SymbolExpr "z") ] ), (SymbolExpr "=") ] )

(/ (- 10 2) 4)
(ArrayExpr [ (SymbolExpr "/"), ArrayExpr ( [ (SymbolExpr "-"), (NumberExpr 10), (NumberExpr 2) ] ), (NumberExpr 4) ] )
-}

-- ============================================================
-- Question 3

-- Function that takes in an SExpr and returns the textual representation of that SExpr.
showSExpr :: SExpr -> String
showSExpr (NumberExpr n) = show n
showSExpr (SymbolExpr s) = s
showSExpr (ArrayExpr a) =  "(" ++ (showSExprListHelper a) ++ ")"

-- Function that is a helper for the showSExpr function which has the purpose of iterating through an array of an SExpr.
showSExprListHelper :: [SExpr] -> String
showSExprListHelper x = if (length x > 1)
                          then ( (showSExpr (head x)) ++ " " ++ (showSExprListHelper (tail x)) )
                          else (showSExpr (head x))


-- ===========================================================
-- Question 4
data SAE = Number Integer
         | Add SAE SAE
         | Sub SAE SAE
         | Mul SAE SAE
         | Div SAE SAE
         deriving (Eq, Show)

-- partA
-- Function that converts SExpr (with restricted symbols +,-,*,/ and lists of length 3) into an SAE.
fromSExpr :: SExpr -> SAE
fromSExpr (NumberExpr n) = (Number n)
fromSExpr (ArrayExpr a) = case (head a) of
                       (SymbolExpr "+") -> Add (fromSExpr (a !! 1)) (fromSExpr (last a))
                       (SymbolExpr "-") -> Sub (fromSExpr (a !! 1)) (fromSExpr (last a))
                       (SymbolExpr "*") -> Mul (fromSExpr (a !! 1)) (fromSExpr (last a))
                       (SymbolExpr "/") -> Div (fromSExpr (a !! 1)) (fromSExpr (last a))

-- partB
-- Function that converts an SAE expression to its SExpr representation.
toSExpr :: SAE -> SExpr
toSExpr (Number n) = (NumberExpr n)
toSExpr (Add x y) = (ArrayExpr [ (SymbolExpr "+"), (toSExpr x), (toSExpr y)])
toSExpr (Sub x y) = (ArrayExpr [ (SymbolExpr "-"), (toSExpr x), (toSExpr y)])
toSExpr (Mul x y) = (ArrayExpr [ (SymbolExpr "*"), (toSExpr x), (toSExpr y)])
toSExpr (Div x y) = (ArrayExpr [ (SymbolExpr "/"), (toSExpr x), (toSExpr y)])

-- ===================================================================
-- Question 5

-- Data representing a polymorphic BinaryTree
data BinaryTree a = Empty
                  | Node a (BinaryTree a) (BinaryTree a)
                  deriving (Eq, Show)

{-
Examples
Empty
(Node 3 Empty Empty)
(Node 42 Empty (Node 4 Empty Empty))
(Node 1 (Node 42 Empty (Node 4 Empty Empty)) (Node 3 Empty Empty))
-}

-- Function that applies a function to a tree similar to how a map function applies another function to a list
treeMap :: (a -> b ) -> ( BinaryTree a) -> (BinaryTree b)
treeMap _ Empty = Empty
treeMap p (Node x l r) = Node (p x) (treeMap p l) (treeMap p r)

-- ===================================================================
-- Question 6

-- Function that takes a function f, an Integer n and an initial value init (of an arbitrary type) and applies f n-times, starting with init
iterateN :: (a -> a) -> Integer -> a -> a
iterateN _ 0 init = init
iterateN f n init = iterateN f (n - 1) (f init)


-- Function used for testing Iterate N that doubles the value given
double :: Integer -> Integer
double x = x * 2

-- ===================================================================
-- Tests for Functions
main :: IO ()
main = do
       test "showSExpr Test Example 1" (showSExpr (ArrayExpr [ (NumberExpr 1), (NumberExpr 20), (SymbolExpr "x"), (NumberExpr 30), (SymbolExpr "foo") ])) "(1 20 x 30 foo)"
       test "showSExpr Test Example 2" (showSExpr (ArrayExpr [ (SymbolExpr "+"), (NumberExpr 13), (NumberExpr 23) ] )) "(+ 13 23)"
       test "showSExpr Test Example 3" (showSExpr (NumberExpr 20)) "20"
       test "showSExpr Test Example 4" (showSExpr (ArrayExpr [ (SymbolExpr "a"), (SymbolExpr "b"), (ArrayExpr [ (SymbolExpr "c"), (SymbolExpr "d") ] ) ] )) "(a b (c d))"
       test "showSExpr Test Example 5" (showSExpr (SymbolExpr "x")) "x"
       test "showSExpr Test Example 6" (showSExpr (ArrayExpr [ (NumberExpr 32), (SymbolExpr "*"), (ArrayExpr [ (NumberExpr 30), (SymbolExpr "z") ] ), (SymbolExpr "=") ] )) "(32 * (30 z) =)"
       test "showSExpr Test Example 7" (showSExpr (ArrayExpr [ (SymbolExpr "/"), ArrayExpr ( [ (SymbolExpr "-"), (NumberExpr 10), (NumberExpr 2) ] ), (NumberExpr 4) ] )) "(/ (- 10 2) 4)"

       test "fromSExpr Simple Number Test" (fromSExpr (NumberExpr 1)) (Number 1)
       test "fromSExpr Simple Add Test" (fromSExpr (ArrayExpr [(SymbolExpr "+"), (NumberExpr 1), (NumberExpr 2)])) (Add (Number 1) (Number 2))
       test "fromSExpr Simple Sub Test" (fromSExpr (ArrayExpr [(SymbolExpr "-"), (NumberExpr 1), (NumberExpr 2)])) (Sub (Number 1) (Number 2))
       test "fromSExpr Simple Mul Test" (fromSExpr (ArrayExpr [(SymbolExpr "*"), (NumberExpr 1), (NumberExpr 2)])) (Mul (Number 1) (Number 2))
       test "fromSExpr Simple Div Test" (fromSExpr (ArrayExpr [(SymbolExpr "/"), (NumberExpr 1), (NumberExpr 2)])) (Div (Number 1) (Number 2))
       test "fromSExpr Complex Test" (fromSExpr  (ArrayExpr [ (SymbolExpr "/"), ArrayExpr ( [ (SymbolExpr "-"), (NumberExpr 10), (NumberExpr 2) ] ), (NumberExpr 4) ] )) (Div (Sub (Number 10) (Number 2)) (Number 4))

       test "toSExpr Simple Number Test" (toSExpr (Number 1)) (NumberExpr 1)
       test "toSExpr Simple Add Test" (toSExpr (Add (Number 1) (Number 2))) (ArrayExpr [(SymbolExpr "+"), (NumberExpr 1), (NumberExpr 2)])
       test "toSExpr Simple Sub Test" (toSExpr (Sub (Number 1) (Number 2))) (ArrayExpr [(SymbolExpr "-"), (NumberExpr 1), (NumberExpr 2)])
       test "toSExpr Simple Mul Test" (toSExpr (Mul (Number 1) (Number 2))) (ArrayExpr [(SymbolExpr "*"), (NumberExpr 1), (NumberExpr 2)])
       test "toSExpr Simple Div Test" (toSExpr (Div (Number 1) (Number 2))) (ArrayExpr [(SymbolExpr "/"), (NumberExpr 1), (NumberExpr 2)])
       test "toSExpr Complex Test" (toSExpr (Div (Sub (Number 10) (Number 2)) (Number 4))) (ArrayExpr [ (SymbolExpr "/"), ArrayExpr ( [ (SymbolExpr "-"), (NumberExpr 10), (NumberExpr 2) ] ), (NumberExpr 4) ] )

       test "treeMap Test Example 1A" (treeMap show (Node 1 Empty Empty)) (Node "1" Empty Empty)
       test "treeMap Test Example 1B" (treeMap head (Node [1] Empty Empty)) (Node 1 Empty Empty)
       test "treeMap Test Example 2A" (treeMap show (Node 42 Empty (Node 4 Empty Empty))) (Node "42" Empty (Node "4" Empty Empty))
       test "treeMap Test Example 2B" (treeMap tail (Node [42, 35, 20] Empty (Node [4, 3] Empty Empty))) (Node [35, 20] Empty (Node [3] Empty Empty))
       test "treeMap Test Example 3A" (treeMap show (Node 1 (Node 42 Empty (Node 4 Empty Empty)) (Node 3 Empty Empty))) (Node "1" (Node "42" Empty (Node "4" Empty Empty)) (Node "3" Empty Empty))
       test "treeMap Test Example 3B" (treeMap head (Node [1] (Node [42] Empty (Node [4] Empty Empty)) (Node [3] Empty Empty))) (Node 1 (Node 42 Empty (Node 4 Empty Empty)) (Node 3 Empty Empty))

       test "iterateN Test 1" (iterateN double 5 1) 32
       test "iterateN Test 2" (iterateN double 0 42) 42
       test "iterateN Test 3" (iterateN tail 1 [3, 40, 30, 2]) [40, 30, 2]
       test "iterateN Test 4" (iterateN tail 4 [3, 40, 30, 2]) []
       test "iterateN Test 5" (iterateN tail 0 [4, 5]) [4,5]
