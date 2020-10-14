module Lec07b where

import SimpleTests (test, testError, testErrorMsg)

import Maps (Map, get, set, empty)

-- <SAE> ::= <Number>
--         | (+ <SAE> <SAE>)
--         | (- <SAE> <SAE>)
--         | (* <SAE> <SAE>)
--         | (/ <SAE> <SAE>)
--         | (let (<Variable> <SAE>) <SAE>)
--         | (<Variable> <SAE>)
--         | (if (= 0 <SAE>) <SAE> <SAE>)
--         | <Variable>

-- <Program> ::= <SAE>
--             | (defun <Variable> (<Variable>) <SAE>) <Program>
--
-- or
--
-- <GlobalDef> ::= (defun <Variable> (<Variable>) <SAE>)
--
-- <Program> ::= <GlobalDef>* <SAE>

type Variable = String

-- |Abstract syntax tree for SAE
data SAE = Number Integer
         | Add SAE SAE
         | Sub SAE SAE
         | Mul SAE SAE
         | Div SAE SAE
         | Let Variable SAE SAE
         | Call Variable SAE
         | IfZero SAE SAE SAE
         | Var Variable
         deriving (Eq, Show)

data Program = Program [GlobalDef] SAE
             deriving (Eq, Show)

data GlobalDef = Defun Variable Variable SAE
               deriving (Eq, Show)

-- Examples
ex_sae1, ex_sae2 :: SAE
-- (- (+ 1 2) 3)
ex_sae1 = Sub (Add (Number 1) (Number 2)) (Number 3)
-- (/ 44 (+ (* 2 5) 1))
ex_sae2 = Div (Number 44) (Add (Mul (Number 2) (Number 5)) (Number 1))
-- (let (y (- 20 8)) (let (x (+ y 4)) (+ x 1)))
ex_sae3 = Let "y" (Sub (Number 20) (Number 8)) 
            (Let "x" (Add (Var "y") (Number 4)) 
              (Add (Var "x") (Number 1)))

ex_program1 = Program [Defun "incr" "x" (Add (Var "x") (Number 1))] 
                 (Call "incr" (Call "incr" (Call "incr" (Number 1))))
ex_program2 = Program [Defun "f" "x" (Add (Var "x") (Var "y"))]
                 (Let "y" (Number 10) (Call "f" (Number 10)))
ex_program3 = Program [Defun "incr" "x" (Add (Var "x") (Number 1))] 
                 (Let "z" (Number 20) (Call "incr" (Var "z")))
ex_program4 = Program 
                [ Defun "fact" "n" 
                    (IfZero 
                      (Var "n") 
                      (Number 1) 
                      (Mul (Var "n") (Call "fact" (Sub (Var "n") (Number 1)))))]
                (Call "fact" (Number 5))
            

-- |Environments are maps from Variables to values (Integers)
type Env = Map Variable Integer

type GlobalEnv = Map Variable GlobalDef

runProgram :: Program -> Maybe Integer
runProgram (Program globalDefs e) = eval globals empty e
  where 
    globals = collectDefs globalDefs
    collectDefs [] = empty
    collectDefs (Defun f x body : globalDefs) =  -- Warning: this collects the definitions in reverse order
        set (collectDefs globalDefs) f (Defun f x body)


test_runProgram = do
    test "runProgram ex_program1" (runProgram ex_program1) (Just 4)
    test "runProgram ex_program2" (runProgram ex_program2) Nothing
    test "runProgram ex_program3" (runProgram ex_program3) (Just 21)
    test "runProgram ex_program4" (runProgram ex_program4) (Just 120)

-- |Evaluates the given SAE, computing the corresponding integer.
eval :: GlobalEnv -> Env -> SAE -> Maybe Integer
eval g m (Number n) = Just n
eval g m (Add e1 e2) = 
    case eval g m e1 of
         Just n1 -> 
             case eval g m e2 of
                  Just n2 -> Just (n1 + n2)
                  Nothing -> Nothing
         Nothing -> Nothing
eval g m (Sub e1 e2) = 
    case eval g m e1 of
         Just n1 -> 
             case eval g m e2 of
                  Just n2 -> Just (n1 - n2)
                  Nothing -> Nothing
         Nothing -> Nothing
eval g m (Mul e1 e2) = 
    case eval g m e1 of
         Just n1 -> 
             case eval g m e2 of
                  Just n2 -> Just (n1 * n2)
                  Nothing -> Nothing
         Nothing -> Nothing
eval g m (Div e1 e2) = 
    case eval g m e1 of
         Just n1 -> 
             case eval g m e2 of
                  Just 0 -> Nothing
                  Just n2 -> Just (n1 `div` n2)
                  Nothing -> Nothing
         Nothing -> Nothing
eval g m (Call f e) =
    case get g f of
         Just (Defun _ x body) ->
             case eval g m e of 
                  Just v -> eval g (set empty x v) body
         Nothing -> Nothing
eval g m (Let x e1 e2) = 
    case eval g m e1 of
         Just n1 -> eval g (set m x n1) e2
         Nothing -> Nothing
eval g m (IfZero e1 e2 e3) = 
    case eval g m e1 of
         Just 0 -> eval g m e2
         Just _ -> eval g m e3
         Nothing -> Nothing
eval g m (Var x) = get m x

test_eval = do
    test "ex_sae1" (eval empty empty ex_sae1) (Just 0)
    test "ex_sae2" (eval empty empty ex_sae2) (Just 4)
    test "ex_sae3" (eval empty empty ex_sae3) (Just 17)



main = do 
    test_eval
    test_runProgram
