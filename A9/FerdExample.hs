
{-
  n is an integer
------------------
 |- n : Integer

 |- e1 : Integer    |- e2 : Integer
 ----------------------------------
    |- e1 + e2 : Integer


-----------------
|- True : Boolean

------------------
|- False : Boolean


|- e1 : Boolean   |- e2 : Boolean
---------------------------------
 |- e1 and e2 : Boolean


|- e1 : Integer   |- e2 : Integer
---------------------------------
   |- e1 <= e2 : Boolean


tenv |- e1 : Boolean   tenv |- e2 : t     tenv |- e3 : t
---------------------------------------------------------
     tenv |- if e1 then e2 else e3 : t


 tenv |- e1 : t1     (set tenv x t1) |- e2 : t2
-----------------------------------------
 tenv |- let x = e1 in e2 : t2

 t = get tenv x
---------------------
 tenv |- x : t

let x = 42 in x + x

eval env (Let x (Integer 42) (Add (Var "x") (Var "x")) = 
  eval (set env "x" (eval env (Integer 42))) (Add (Var "x") (Var "x"))
eval env (Var x) = get env x

set tenv x t |- e : t'
------------------------------------
        tenv |- (λx : t. e) : t -> t'

tenv |- e1 : t2 -> t1     tenv |- e2 : t2
------------------------------------------
tenv |- e1 e2 : t1


((λx. x) 1) : Integer

((λx. x) True) : Boolean

((λx : Integer. x + x) True)

-}

import Maps

-- Abstract syntax
data Expr = Integer Integer
          | Boolean Bool
          | Add Expr Expr
          | And Expr Expr
          | Leq Expr Expr
          | If Expr Expr Expr
          | Var String
          | Let String Expr Expr
          | Lam String Type Expr
          | App Expr Expr
          deriving (Show, Eq)

-- Types
data Type = TyInteger
          | TyBoolean
          deriving (Show, Eq)

type TyEnv = Map String Type

-- Typing rules
typeOf :: TyEnv -> Expr -> Maybe Type
typeOf _ (Integer i) = return TyInteger
typeOf _ (Boolean b) = return TyBoolean
typeOf tenv (Add e1 e2) = 
{-    case typeOf e1 of
         Just TyIntger -> 
             case typeOf e2 of
                  Just TyInteger -> Just TyInteger
                  _ -> Nothing
         _ -> Nothing-}
  do
    TyInteger <- typeOf tenv e1
    TyInteger <- typeOf tenv e2
    return TyInteger
typeOf tenv (And e1 e2) = do
    TyBoolean <- typeOf tenv e1
    TyBoolean <- typeOf tenv e2
    return TyBoolean
typeOf tenv (Leq e1 e2) = do
    TyInteger <- typeOf tenv e1
    TyInteger <- typeOf tenv e2
    return TyBoolean
typeOf tenv (If e1 e2 e3) = do
    TyBoolean <- typeOf tenv e1
    t2 <- typeOf tenv e2
    t3 <- typeOf tenv e3
    if t2 == t3
        then return t2
        else fail "if: no type"
typeOf tenv (Var x) = get tenv x
typeOf tenv (Let x e1 e2) = do
    t1 <- typeOf tenv e1
    typeOf (set tenv x t1) e2
typeOf tenv (Lam x t e) = do
    t' <- typeOf (set tenv x t) e
    return $ TyArrow t t'
typeOf tenv (App e1 e2) = do
    TyArrow t2 t1 <- typeOf tenv e1
    t2' <- typeOf tenv e2
    if (t2 == t2')
        then t1
        else fail "Incompatible argument types."

ex1 = Add (Integer 1) (Integer 3)
ex2 = And (Integer 1) (Boolean True)
ex3 = And (Boolean True) (And (Boolean False) (Boolean True))
ex4 = If (Boolean False) (Integer 1) (Boolean True)
ex5 = If (Boolean False) (Integer 1) (Integer 3)
ex6 = Add (Integer 1) (If (Leq (Integer 4) (Integer 5)) (Integer 3) (Boolean False))
{-
  if typeOf e1 == TyBoolean && typeOf e2 = TyBoolean
     then TyBoolean
     else ...
-}

ex7 = Let "x" (Add (Integer 1) (Integer 3)) 
          (Add (Var "x") (Var "x"))
{-
typeOf tenv ex7 = 
    typeOf tenv (Add (Integer 1) (Integer 3)) -> TyInteger
    typeOf (set tenv "x" TyInteger) (Add (Var "x") (Var "x")
    - typeOf (set tenv "x" TyInteger) (Var "x") -> TyInteger
    return TyInteger
-}

