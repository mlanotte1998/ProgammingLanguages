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

import Eval 

import Syntax
import Church
import qualified Lambda as L

import Parser 

import Reduce (normalize, normalizeWithCount)

import SimpleTestsColor (test, testSection)


{-
<Expr> ::= Value (Pos Integers and Booleans)
| <Variable>
| (+ <Expr> <Expr>)
| (- <Expr> <Expr>)
| (* <Expr> <Expr>)
| (let (<Variable> <Expr>) <Expr>)
| (if <Expr> <Expr> <Expr>)
| (and <Expr> <Expr>)
| (or <Expr> <Expr>)
| (not <Expr>)
| (< <Expr> <Expr>)
| (> <Expr> <Expr>)
| (= <Expr> <Expr>)
| (<Variable> <Expr> <Expr>*)
-}



-- |Compile a protoScheme expression into PLC
compile :: Syntax.Expr -> Maybe L.Lambda
compile (Syntax.Integer x) = Just (toNumeral x)
compile (Syntax.Boolean x) = Just (toChurchBool x)
compile (Var x) = Just (L.Var x)
compile (Add x y) = 
    case compile x of 
         Just a -> case compile y of 
                         Just b -> Just (L.App (L.App cplus a) b)
                         _ -> Nothing
         _ -> Nothing  
compile (Sub x y) = 
    case compile x of 
         Just a -> case compile y of 
                         Just b -> Just (L.App (L.App cminus b) a)
                         _ -> Nothing
         _ -> Nothing          
compile (Mul x y) = 
    case compile x of 
         Just a -> case compile y of 
                         Just b -> Just (L.App (L.App ctimes a) b)
                         _ -> Nothing
         _ -> Nothing    
compile (Let x e1 e2) =
    case compile e1 of 
         Just a -> case compile e2 of 
                         Just b -> Just (L.App (L.Lam x b) a)
                         _ -> Nothing
         _ -> Nothing    
compile (If x y z) = 
    case compile x of 
         Just a -> case compile y of 
                         Just b -> case compile z of
                                         Just c -> Just (L.App (L.App (L.App cifthen a) b) c)
                                         _ -> Nothing
                         _ -> Nothing
         _ -> Nothing     
compile (And x y) = 
    case compile x of 
         Just a -> case compile y of 
                         Just b -> Just (L.App (L.App cand a) b)
                         _ -> Nothing
         _ -> Nothing     
compile (Or x y) = 
    case compile x of 
         Just a -> case compile y of 
                         Just b -> Just (L.App (L.App cor a) b)
                         _ -> Nothing
         _ -> Nothing  
compile (Not x) = 
    case compile x of 
        Just a -> Just (L.App cnot a)
        _ -> Nothing           
compile (Greater_Than x y) = 
    case compile x of 
         Just a -> case compile y of 
                         Just b -> Just (L.App (L.App cgt b) a)
                         _ -> Nothing
         _ -> Nothing  
compile (Less_Than x y) = 
    case compile x of 
         Just a -> case compile y of 
                         Just b -> Just (L.App (L.App clt b) a)
                         _ -> Nothing
         _ -> Nothing          
compile (Equal_To x y) = 
    case compile x of 
         Just a -> case compile y of 
                         Just b -> Just (L.App (L.App ceq a) b)
                         _ -> Nothing
         _ -> Nothing   
compile (Call x y) = compileCallHelper x y 
    where 
        compileCallHelper :: Variable -> [Syntax.Expr] -> Maybe L.Lambda
        compileCallHelper v [] = Just (L.Var v)
        compileCallHelper v (x:xs) = case compile x of 
                                          Just a -> case compileCallHelper v xs of 
                                                         Just b -> Just (L.App b a)
                                                         _ -> Nothing
                                          _ -> Nothing 
compile _ = Nothing    


compileNoMaybe :: Maybe L.Lambda -> L.Lambda 
compileNoMaybe (Nothing) = L.Var "Nothing" 
compileNoMaybe (Just x) = x 


test_compile = do 
    test "Compile Float test" (compile (Float 1.5)) Nothing
    test "Compile Pair test" (compile (Pair (Integer 10) (Boolean False))) Nothing 
    test "Compile Left test" (compile (Syntax.Left (Pair (Integer 10) (Integer 5)))) Nothing 
    test "Compile Right test" (compile (Syntax.Right (Pair (Integer 10) (Integer 5)))) Nothing 
    test "Compile Div test" (compile (Div (Integer 1) (Integer 2))) Nothing
    test "Compile cond no else test" (compile (Cond [((Integer 10), (Boolean False))] Nothing)) Nothing 
    test "Compile cond with else test" (compile (Cond [((Integer 10), (Boolean False))] (Just (Integer 15)))) Nothing
    test "Compile real? test" (compile (Real_Pred (Float 5.5))) Nothing 
    test "Compile integer? test" (compile (Real_Pred (Float 5.5))) Nothing
    test "Compile number? test" (compile (Real_Pred (Float 5.5))) Nothing
    test "Compile boolean? test" (compile (Real_Pred (Float 5.5))) Nothing
    test "Compile pair? test" (compile (Real_Pred (Float 5.5))) Nothing
    test "Compile Integer test 1" (fromNumeral (normalize (compileNoMaybe (compile (Integer 1))))) (Just 1)
    test "Compile Integer test 2" (fromNumeral (normalize (compileNoMaybe (compile (Integer 5))))) (Just 5)
    test "Compile Boolean test 1" (fromChurchBool (normalize (compileNoMaybe (compile (Boolean False))))) (Just False) 
    test "Compile Boolean test 1" (fromChurchBool (normalize (compileNoMaybe (compile (Boolean True))))) (Just True) 
    test "Compile Add test 1" (fromNumeral (normalize (compileNoMaybe (compile (Add (Integer 5) (Integer 10)))))) (Just 15)
    test "Compile Add test 2" (fromNumeral (normalize (compileNoMaybe (compile (Add (Integer 4) (Boolean False)))))) (Just 4) 
    test "Compile Add test Nothing 1" (fromNumeral (normalize (compileNoMaybe (compile (Add (Var "x") (Integer 10)))))) (Nothing)
    test "Compile Add test Nothing 2" (fromNumeral (normalize (compileNoMaybe (compile (Add (Integer  10) (Var "b")))))) (Nothing) 
    test "Compile Add test Nothing 3" (fromNumeral (normalize (compileNoMaybe (compile (Add (Boolean False) (Boolean True)))))) (Nothing) 
    test "Compile Add test Nothing 4" (compile (Add (Float 5.5) (Integer 10))) (Nothing)
    test "Compile Add test Nothing 5" (compile (Add (Integer  10) (Boolean_Pred (Boolean False)))) (Nothing) 
    test "Compile Sub test 1" (fromNumeral (normalize (compileNoMaybe (compile (Sub (Integer 10) (Integer 5)))))) (Just 5)
    test "Compile Sub test 2" (fromNumeral (normalize (compileNoMaybe (compile (Sub (Integer 2) (Integer 4)))))) (Just 0)
    test "Compile Sub test 3" (fromNumeral (normalize (compileNoMaybe (compile (Sub (Integer 4) (Boolean False)))))) (Just 4) 
    test "Compile Sub test Nothing 1" (fromNumeral (normalize (compileNoMaybe (compile (Sub (Var "x") (Integer 10)))))) (Nothing)
    test "Compile Sub test Nothing 2" (fromNumeral (normalize (compileNoMaybe (compile (Sub (Integer  10) (Var "b")))))) (Nothing) 
    test "Compile Sub test Nothing 3" (fromNumeral (normalize (compileNoMaybe (compile (Sub (Boolean False) (Boolean True)))))) (Nothing) 
    test "Compile Sub test Nothing 4" (compile (Sub (Float 5.5) (Integer 10))) (Nothing)
    test "Compile Sub test Nothing 5" (compile (Sub (Integer  10) (Boolean_Pred (Boolean False)))) (Nothing) 
    test "Compile Mul test 1" (fromNumeral (normalize (compileNoMaybe (compile (Mul (Integer 5) (Integer 10)))))) (Just 50)
    test "Compile Mul test 2" (fromNumeral (normalize (compileNoMaybe (compile (Mul (Integer 4) (Integer 0)))))) (Just 0)
    test "Compile Mul test 3" (fromNumeral (normalize (compileNoMaybe (compile (Mul (Boolean False) (Integer 4)))))) (Just 0) 
    test "Compile Mul test 4" (fromNumeral (normalize (compileNoMaybe (compile (Mul (Boolean False) (Boolean True)))))) (Just 0) 
    test "Compile Mul test Nothing 1" (fromNumeral (normalize (compileNoMaybe (compile (Mul (Var "x") (Integer 10)))))) (Nothing)
    test "Compile Mul test Nothing 2" (fromNumeral (normalize (compileNoMaybe (compile (Mul (Integer  10) (Var "b")))))) (Nothing) 
    test "Compile Mul test Nothing 3" (compile (Mul (Float 5.5) (Integer 10))) (Nothing)
    test "Compile Mul test Nothing 4" (compile (Mul (Integer  10) (Boolean_Pred (Boolean False)))) (Nothing) 
    test "Compile Let test 1" (fromNumeral (normalize (compileNoMaybe 
     (compile (Let "var" (Integer 5) (Add (Integer 1) (Var "var"))))))) (Just 6)
    test "Compile Let test 2" (fromNumeral (normalize (compileNoMaybe 
     (compile (Let "var" (Integer 1) (Sub (Integer 5) (Var "var"))))))) (Just 4)
    test "Compile Let test 3" (fromChurchBool (normalize (compileNoMaybe 
     (compile (Let "var" (Boolean True) (And (Boolean True) (Var "var"))))))) (Just True) 
    test "Compile Let test Nothing 1" (compile (Let "var" (Float 5.5) (And (Boolean True) (Var "var")))) (Nothing) 
    test "Compile Let test Nothing 2" (compile (Let "var" (Var "x") (Div (Integer 5) (Var "var")))) (Nothing)  
    test "Compile If test 1" (fromNumeral (normalize (compileNoMaybe (compile (If (Boolean True) (Integer 5) (Integer 4)))))) (Just 5) 
    test "Compile If test 2" (fromNumeral (normalize (compileNoMaybe (compile (If (Boolean False) (Integer 5) (Integer 4)))))) (Just 4)
    test "Compile If test 3" (fromNumeral (normalize (compileNoMaybe (compile (If (And (Boolean True) (Boolean True)) (Integer 5) (Integer 4)))))) (Just 5)
    test "Compile If test Nothing 1" (compile (If (Float 5.5) (Integer 5) (Integer 4))) (Nothing) 
    test "Compile If test Nothing 2" (compile (If (Boolean True) (Div (Integer 3) (Integer 10)) (Integer 4))) (Nothing) 
    test "Compile If test Nothing 3" (compile (If (Boolean True) (Integer 10) (Boolean_Pred (Boolean True)))) (Nothing)
    test "Compile And test 1" (fromChurchBool (normalize (compileNoMaybe (compile (And (Boolean False) (Boolean True)))))) (Just False)
    test "Compile And test 2" (fromChurchBool (normalize (compileNoMaybe (compile (And (Boolean True) (Boolean True)))))) (Just True)
    test "Compile And test 3" (fromChurchBool (normalize (compileNoMaybe (compile (And (Boolean True) (Boolean False)))))) (Just False) 
    test "Compile And test 4" (fromChurchBool (normalize (compileNoMaybe (compile (And (Boolean False) (Boolean False)))))) (Just False) 
    test "Compile And test Nothing 1" (compile (And (Float 5.5) (Integer 10))) (Nothing)
    test "Compile And test Nothing 2" (compile (And (Boolean True) (Pair_Pred (Integer 10)))) (Nothing)
    test "Compile Or test 1" (fromChurchBool (normalize (compileNoMaybe (compile (Or (Boolean False) (Boolean True)))))) (Just True)
    test "Compile Or test 2" (fromChurchBool (normalize (compileNoMaybe (compile (Or (Boolean True) (Boolean True)))))) (Just True)
    test "Compile Or test 3" (fromChurchBool (normalize (compileNoMaybe (compile (Or (Boolean True) (Boolean False)))))) (Just True) 
    test "Compile Or test 4" (fromChurchBool (normalize (compileNoMaybe (compile (Or (Boolean False) (Boolean False)))))) (Just False) 
    test "Compile Or test Nothing 1" (compile (Or (Float 5.5) (Integer 10))) (Nothing)
    test "Compile Or test Nothing 2" (compile (Or (Boolean True) (Pair_Pred (Integer 10)))) (Nothing)    
    test "Compile Not test 1" (fromChurchBool (normalize (compileNoMaybe (compile (Not (Boolean False)))))) (Just True)
    test "Compile Not test 2" (fromChurchBool (normalize (compileNoMaybe (compile (Not (Boolean True)))))) (Just False)
    test "Compile Not test Nothing 1" (compile (Not (Float 5.5))) (Nothing)
    test "Compile Not test Nothing 2" (fromChurchBool (normalize (compileNoMaybe 
     (compile (Not (Integer 5)))))) (Nothing)
    test "Compile < test 1" (fromChurchBool (normalize (compileNoMaybe (compile (Less_Than (Integer 5) (Integer 10)))))) (Just True)
    test "Compile < test 2" (fromChurchBool (normalize (compileNoMaybe (compile (Less_Than (Integer 10) (Integer 5)))))) (Just False)
    test "Compile < test 3" (fromChurchBool (normalize (compileNoMaybe (compile (Less_Than (Boolean True) (Integer 6)))))) (Nothing) 
    test "Compile < test 4" (fromChurchBool (normalize (compileNoMaybe (compile (Less_Than (Integer 20) (Boolean False)))))) (Just False) 
    test "Compile < test Nothing 1" (compile (Less_Than (Float 5.5) (Integer 10))) (Nothing)
    test "Compile < test Nothing 2" (compile (Less_Than (Boolean True) (Pair_Pred (Integer 10)))) (Nothing)
    test "Compile > test 1" (fromChurchBool (normalize (compileNoMaybe (compile (Greater_Than (Integer 5) (Integer 10)))))) (Just False)
    test "Compile > test 2" (fromChurchBool (normalize (compileNoMaybe (compile (Greater_Than (Integer 10) (Integer 5)))))) (Just True)
    test "Compile > test 3" (fromChurchBool (normalize (compileNoMaybe (compile (Greater_Than (Boolean True) (Integer 6)))))) (Just False) 
    test "Compile > test 4" (fromChurchBool (normalize (compileNoMaybe (compile (Greater_Than (Integer 20) (Boolean False)))))) (Just True) 
    test "Compile > test Nothing 1" (compile (Greater_Than (Float 5.5) (Integer 10))) (Nothing)
    test "Compile > test Nothing 2" (compile (Greater_Than (Boolean True) (Pair_Pred (Integer 10)))) (Nothing)    
    test "Compile = test 1" (fromChurchBool (normalize (compileNoMaybe (compile (Equal_To (Integer 5) (Integer 10)))))) (Just False)
    test "Compile = test 2" (fromChurchBool (normalize (compileNoMaybe (compile (Equal_To (Integer 10) (Integer 10)))))) (Just True)
    -- next two are strange but consistent with what ceq does 
    test "Compile = test 3" (fromChurchBool (normalize (compileNoMaybe (compile (Equal_To (Boolean True) (Boolean True)))))) (Just False) 
    test "Compile = test 4" (fromChurchBool (normalize (compileNoMaybe (compile (Equal_To (Boolean False) (Boolean True)))))) (Nothing)
    test "Compile = test 5" (fromChurchBool (normalize (compileNoMaybe (compile (Equal_To (Boolean True) (Integer 6)))))) (Just False) 
    test "Compile = test 6" (fromChurchBool (normalize (compileNoMaybe (compile (Equal_To (Integer 20) (Boolean False)))))) (Just False) 
    test "Compile = test Nothing 1" (compile (Equal_To (Float 5.5) (Integer 10))) (Nothing)
    test "Compile = test Nothing 2" (compile (Equal_To (Boolean True) (Pair_Pred (Integer 10)))) (Nothing)
      

-- |Compile the given protoScheme program into PLC
compileProgram :: Program -> Maybe L.Lambda
compileProgram (Program [] x) = compile x 
compileProgram (Program ((Defun v (v1, vlist) e): xs) y) = case compileProgramDefun (Defun v (v1, reverse (vlist)) e) of 
                                                                Just a -> case compileProgram (Program xs y) of 
                                                                               Just b -> (Just (L.App (L.Lam v b) (L.App cfix (L.Lam v a)))) 
                                                                               Nothing -> Nothing
                                                                Nothing -> Nothing 
    where 
        compileProgramDefun :: GlobalDef -> Maybe L.Lambda
        compileProgramDefun (Defun v (arg1, []) e) = case compile e of 
                                                        Just a -> Just (L.Lam arg1 $ normalize a)
                                                        _ -> Nothing
        compileProgramDefun (Defun v (arg1, (x:xs)) e) = case compileProgramDefun (Defun v (arg1, xs) e) of 
                                                              Just a -> Just (L.Lam x a)
                                                              _ -> Nothing                                                                                                                     
compileProgram (Program ((Define v x): xs) e) = case compileProgram (Program xs e) of
                                                     Just a -> case compile x of 
                                                         Just b -> (Just (L.App (L.Lam v a) b))
                                                         _ -> Nothing
                                                     _ -> Nothing
                    


test_compileProgram = do 
    test "Compile defun and call test 1" (fromNumeral (normalize (compileNoMaybe (compileProgram 
       (Program [Defun "func" ("x", []) (Add (Syntax.Integer 5) (Var "x"))] (Call "func" [Syntax.Integer 10]))))))
       (Just 15) 
    test "Compile defun and call test 2" (fromNumeral (normalize (compileNoMaybe (compileProgram 
     (Program [Defun "func" ("x", ["y"]) (Sub (Var "x") (Var "y"))] (Call "func" [Syntax.Integer 10, Syntax.Integer 5]))))))
      (Just 5)  
    test "Compile defun and call test 3" (fromNumeral (normalize (compileNoMaybe (compileProgram 
     (Program [Defun "func" ("x", ["y", "z"]) 
      (Mul (Var "z") (Sub (Var "x") (Var "y")))] (Call "func" [Syntax.Integer 10, Syntax.Integer 5, Syntax.Integer 2]))))))
     (Just 10) 

    test "Compile defun and call test 4" (fromNumeral (normalize (compileNoMaybe (compileProgram 
     (Program [Defun "func" ("x", ["y", "z"]) (Add (Syntax.Integer 5) (Var "x"))] (Call "func" [Syntax.Integer 10]))))))
      (Nothing) 
    test "Compile defun and call test 5" (fromNumeral (normalize (compileNoMaybe (compileProgram 
     (Program [Defun "func" ("x", ["y"]) (Sub (Var "x") (Var "y"))] (Call "func" [Syntax.Integer 10]))))))
      (Nothing)  
    test "Compile defun and call test 6" (fromNumeral (normalize (compileNoMaybe (compileProgram 
     (Program [Defun "func" ("x", ["y", "z"]) 
      (Mul (Var "z") (Sub (Var "x") (Var "y")))] (Call "notFunc" [Syntax.Integer 10, Syntax.Integer 5, Syntax.Integer 2]))))))
     (Nothing)                

    test "CompileProgram Define test 1" (fromNumeral (normalize (compileNoMaybe (compileProgram (Program [Define "var" (Integer 10)] (Integer 11)))))) (Just 11)
    test "CompileProgram Define test 2" (fromNumeral (normalize (compileNoMaybe (compileProgram (Program [Define "var" (Integer 10)] (Var "var")))))) (Just 10)

-- |Generate the source code of a program calculating the factorial of the
-- given number
factorialProgram :: Integer -> String
factorialProgram number =                        
  "((defun fact (n) (if (= n 1) 1 (* n (fact (- n 1))))) (fact " ++ show number ++ "))" 

test_factorial = do 
     case parseSExpression $ factorialProgram 4 of 
         Just a -> case (normalizeWithCount (compileNoMaybe (compileProgram (programFromSExpression a)))) of 
             (lam, count) -> show count ++ " " ++ show (fromNumeral lam)


countdownTo1Program = 
    "((defun down (n)\
    \   (if (= n 1)\
    \       n\
    \       (down (- n 1))))\
    \ (down 5))"

allTests = do
    test_factorial

