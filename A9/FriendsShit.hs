{- |
Module      :  Types
Description :  Type-checker implementation.

Maintainer  :  Ferd <f.vesely@northeastern.edu>
               Zachary Hillman <hillman.z@husky.neu.edu>
-}

{-# OPTIONS_GHC -fdefer-typed-holes -fwarn-incomplete-patterns #-}
module Types where

import Syntax

import Maps

import Debug.Trace (trace)

import SimpleTests


-- complete the definition below
typeOf :: TEnv -> Expr -> Maybe Type
typeOf tenv (Val (Bool _)) = return TyBool
typeOf tenv (Val (Num _)) = return TyInt
typeOf tenv e@(Val _) = fail ("Runtime-only value " ++ show e)
typeOf tenv (Var x) = get x tenv
typeOf tenv (Lam x t1 e) = 
  do t2 <- typeOf (add x t1 tenv) e
     return (TyArrow t1 t2)
typeOf tenv e@(App e1 e2) =
  do TyArrow t2 t1 <- typeOf tenv e1
     t2' <- typeOf tenv e2
     if t2 == t2'
        then return t1
        else fail "App"
typeOf tenv (Fix e) =
  do TyArrow t1 t2 <- typeOf tenv e
     if t1 == t2 
        then return t1
        else fail "Fix"
typeOf tenv (Let x e1 e2) = 
   do t1 <- typeOf tenv e1
      t2 <- typeOf (add x t1 tenv) e2
      return t2
typeOf tenv (Add e1 e2) =
  do TyInt <- typeOf tenv e1
     TyInt <- typeOf tenv e2
     return TyInt
-- Sub
typeOf tenv (Sub e1 e2) =
  do TyInt <- typeOf tenv e1
     TyInt <- typeOf tenv e2
     return TyInt
-- Mul
typeOf tenv (Mul e1 e2) =
   do TyInt <- typeOf tenv e1
      TyInt <- typeOf tenv e2
      return TyInt
-- And
typeOf tenv (And e1 e2) =
   do TyBool <- typeOf tenv e1
      TyBool <- typeOf tenv e2
      return TyBool
-- Not
typeOf tenv (Not e) =
   do TyBool <- typeOf tenv e
      return TyBool
-- Leq
typeOf tenv (Leq e1 e2) =
   do TyInt <- typeOf tenv e1
      TyInt <- typeOf tenv e2
      return TyBool
-- If
typeOf tenv (If e1 e2 e3) =
   do TyBool <- typeOf tenv e1
      t2 <- typeOf tenv e2
      t3 <- typeOf tenv e3
      if t2 == t3
         then return t2
         else fail "If"
-- Pair
typeOf tenv (Pair e1 e2) =
   do t1 <- typeOf tenv e1
      t2 <- typeOf tenv e2
      return (TyPair t1 t2)
-- Fst
typeOf tenv (Fst e) =
   do TyPair t1 t2 <- typeOf tenv e
      return t1
-- Snd
typeOf tenv (Snd e) =
   do TyPair t1 t2 <- typeOf tenv e
      return t2
--Cons
typeOf tenv (Cons e1 e2) =
   do t <- typeOf tenv e1
      TyList t' <- typeOf tenv e2
      if t == t'
         then return (TyList t')
         else fail "Cons"
--Nil
typeOf tenv (Nil t) = Just (TyList t)
--IsNil
typeOf tenv (IsNil e) =
   do TyList t <- typeOf tenv e
      return TyBool
--Head
typeOf tenv (Head e) =
   do TyList t <- typeOf tenv e
      return t
--Tail
typeOf tenv (Tail e) =
   do TyList t <- typeOf tenv e
      return (TyList t)


---------------------------- your helper functions --------------------------


----------------------------------- TESTS -----------------------------------

tests :: IO ()
tests = do
  test "|- 4 + 5 : TyInt" (typeOf empty (Add (num 4) (num 5))) (Just TyInt)
  test "|- True + 5 : TyInt" (typeOf empty (Add (bool True) (num 5))) Nothing
  test "|- 4 - 5 : TyInt" (typeOf empty (Sub (num 4) (num 5))) (Just TyInt)
  test "|- 4 - False : TyInt" (typeOf empty (Sub (num 4) (bool False))) Nothing
  test "|- 4 * 5 : TyInt" (typeOf empty (Mul (num 4) (num 5))) (Just TyInt)
  test "|- False * 5 : TyInt" (typeOf empty (Mul (bool False) (num 5))) Nothing
  test "|- True and False : TyBool" (typeOf empty (And (bool True) (bool False))) (Just TyBool)
  test "|- True and 4 : TyBool" (typeOf empty (And (bool True) (num 4))) Nothing
  test "let x = 3 in (x+3)"
    (typeOf empty (Let "x" (num 3) (Add (Var "x") (num 2))))
    (Just TyInt)
  test "let x = True in (x+3)"
    (typeOf empty (Let "x" (bool True) (Add (Var "x") (num 2))))
    Nothing
  test "let x = True in (True && False)"
    (typeOf empty (Let "x" (bool True) (And (Var "x") (bool False))))
    (Just TyBool)
  test "not True"
    (typeOf empty (Not (bool True))) (Just TyBool)
  test "not 3"
    (typeOf empty (Not (num 3))) Nothing
  test "3 <= 4"
    (typeOf empty (Leq (num 3) (num 4))) (Just TyBool)
  test "(True && False) <= 4"
    (typeOf empty (Leq (And (bool True) (bool False)) (num 4))) Nothing
  test "If True 3 4"
    (typeOf empty (If (bool True) (num 3) (num 4))) (Just TyInt)
  test "If True True False"
    (typeOf empty (If (bool True) (bool True) (bool False))) (Just TyBool)
  test "If 3 True False"
    (typeOf empty (If (num 3) (bool True) (bool False))) Nothing
  test "If True 3 False"
    (typeOf empty (If (bool True) (num 3) (bool False))) Nothing
  test "Pair True 3"
    (typeOf empty (Pair (bool True) (num 3))) (Just (TyPair TyBool TyInt))
  test "Pair True False"
    (typeOf empty (Pair (bool True) (bool False))) (Just (TyPair TyBool TyBool))
  test "Fst (True False)"
    (typeOf empty (Fst (Pair (bool True) (bool False)))) (Just TyBool)
  test "Fst (6 False)"
    (typeOf empty (Fst (Pair (num 6) (bool False)))) (Just TyInt)
  test "Fst ([int] False)"
    (typeOf empty (Fst (Pair (Nil TyInt) (bool False)))) (Just (TyList TyInt))
  test "Fst False"
    (typeOf empty (Fst (bool False))) Nothing
  test "Fst 3"
    (typeOf empty (Fst (num 3))) Nothing
  test "Snd (True False)"
    (typeOf empty (Snd (Pair (bool True) (bool False)))) (Just TyBool)
  test "Snd (False 6)"
    (typeOf empty (Snd (Pair (bool False) (num 6)))) (Just TyInt)
  test "Snd (False [int])"
    (typeOf empty (Snd (Pair (bool False) (Nil TyInt)))) (Just (TyList TyInt))
  test "Snd False"
    (typeOf empty (Snd (bool False))) Nothing
  test "Snd 3"
    (typeOf empty (Snd (num 3))) Nothing
  test "Cons 4 [int]"
    (typeOf empty (Cons (num 4) (Nil TyInt))) (Just (TyList TyInt))
  test "Cons True [int]"
    (typeOf empty (Cons (bool True) (Nil TyInt))) Nothing
  test "Cons True [bool]"
    (typeOf empty (Cons (bool True) (Nil TyBool))) (Just (TyList TyBool))
  test "Cons True True"
    (typeOf empty (Cons (bool True) (bool True))) Nothing
  test "Cons [bool] True"
    (typeOf empty (Cons (Nil TyBool) (bool True))) Nothing
  test "Cons 2 [1]"
    (typeOf empty (Cons (num 2) (Cons (num 1) (Nil TyInt)))) (Just (TyList TyInt))
  test "Nil [int]"
    (typeOf empty (Nil TyBool)) (Just (TyList TyBool))
  test "Nil [bool]"
    (typeOf empty (Nil TyBool)) (Just (TyList TyBool))
  test "Nil [[int]]"
    (typeOf empty (Nil (TyList TyInt))) (Just (TyList (TyList TyInt)))
  test "IsNil [bool]"
    (typeOf empty (IsNil (Nil TyBool))) (Just TyBool)
  test "IsNil [1]"
    (typeOf empty (IsNil (Cons (num 1) (Nil TyInt)))) (Just TyBool)
  test "IsNil 1"
    (typeOf empty (IsNil (num 1))) Nothing
  test "Head [bool]"
    (typeOf empty (Head (Nil TyBool))) (Just TyBool)
  test "Head [int]"
    (typeOf empty (Head (Nil TyInt))) (Just TyInt)
  test "Head [True]"
    (typeOf empty (Head (Cons (bool True) (Nil TyBool)))) (Just TyBool)
  test "Head [1, True]"
    (typeOf empty (Head (Cons (num 1) (Nil TyBool)))) Nothing
  test "Tail [bool]"
    (typeOf empty (Tail (Nil TyBool))) (Just (TyList TyBool))
  test "Tail [int]"
    (typeOf empty (Tail (Nil TyInt))) (Just (TyList TyInt))
  test "Tail [True]"
    (typeOf empty (Tail (Cons (bool True) (Nil TyBool)))) (Just (TyList TyBool))
  test "Tail [1, True]"
    (typeOf empty (Tail (Cons (num 1) (Nil TyBool)))) Nothing