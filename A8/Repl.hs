{-|
Module      : Repl
Description : Repl function for passing arguments in to parser and evaluating them. 
Copyright   : (c) Michael Lanotte, 2020
                  Rachel Johanek, 2020
Maintainer  : lanotte.m@northeastern.edu
              johanek.r@northeastern.edu

-}

module Repl where 

import qualified Maps as M
import qualified SExpression as S
import qualified Parser as P
import qualified Syntax as Syn
import qualified Eval as E
import qualified Result as R

--Data type respresenting an Expr or a Global Def
data DefOrExpr = GlobalDef Syn.GlobalDef
               | Expr Syn.Expr
              deriving(Eq, Show) 



-- //This is the Read, Evaluate, Print, Loop that takes any user input in the terminal
--   parses it into SExpressions, converts it into our protoscheme syntax, evaluates it,
--   Turns to result of the evaluation back into an SExpression and then outputs a string 
--   representing the evaluated expression. The REPL updates a map with any definitions the
--   user might create and checks the map each time it evaluates.
repl :: Syn.Env -> IO [R.Result Syn.Value]
repl env = do
   line <- getLine
   -- Terminate the program if the user ever inputs ':quit'
   if (line == ":quit") 
      then 
           do 
               print "Bye bye."
               return []
      else 
           do       
           input (call line)
               where 
                    call x = runFromSExpression (P.parseSExpression(x))
                         where 
                            -- //The function runFromSExpression takes the parsed input, a R.Result S.SExpression, 
                            --   and if the input is a Failure it returns nothing, if it contain S.List with "define",
                            --   representing or an S.List with "defun", the expressions are converted to Results with GlobalDefs
                            --   Simarly, if the input is an SExpression representing a Syn.Expr then it is converted as well
                            runFromSExpression :: R.Result S.Expr -> R.Result DefOrExpr 
                            runFromSExpression (R.Failure f) =  R.Failure f
                            runFromSExpression (R.Success (S.List [S.Symbol "define", S.Symbol x, e])) = R.Success (GlobalDef (Syn.Define x (Syn.fromSExpression e)))
                            runFromSExpression (R.Success (S.List [S.Symbol "defun", S.Symbol x, S.List v, e])) = 
                                 R.Success (GlobalDef (Syn.Define x (Syn.Lambda (makeFunctionArguments v) (Syn.fromSExpression e))))
                                   where 
                                      -- //Converts an S.SExpression Symbol to a Syn.Expr Variable
                                      makeFunctionArguments :: [S.Expr] -> [Syn.Variable]
                                      makeFunctionArguments [] = []
                                      makeFunctionArguments ((S.Symbol x):xs) = x : makeFunctionArguments xs
                            runFromSExpression (R.Success x) = 
                                 R.Success (Expr (Syn.fromSExpression(x)))
                    -- //input is given the output of runFromSExpression as an argument, which is a R.Result DefOrExpr
                    --   if the input is a Failure, then there is a parse error and the user is prompted to try again
                    --   if the input is a Success with a Syn.GlobalDef, the user's definition is added to 
                    --   the environment unless it is already defined. The user is told of the definition being made or of
                    --   the error. Lastly, if the input is representative of an Syn.Expr the expression is evaluated and
                    --   printed to the user. 
                    input :: R.Result DefOrExpr -> IO [R.Result Syn.Value]     
                    -- The input is a Failure    
                    input (R.Failure f) = do
                                    putStrLn "Parse error. Try again."
                                    repl env
                    -- A GlobalDef was the input, and the environment is updated to include the definition
                    -- unless it is already defined.
                    input (R.Success (GlobalDef (Syn.Define x y))) = if (M.get env x) == Nothing
                                                   then 
                                                        do 
                                                            putStrLn ("Variable " ++ x ++ " defined.")
                                                            -- setGlobalMap env 
                                                            case E.eval env M.empty y of 
                                                                R.Success y' -> repl (M.set env x y') 
                                                                R.Failure y' -> do 
                                                                                putStrLn ("Error: parse error for variable " ++ x ++ " " ++ y')
                                                                                repl env
                                                   else 
                                                        do 
                                                            putStrLn ("Error: variable " ++ x ++ " is already defined.")
                                                            repl env
                    -- The input represents a Syn.Exp,  the Syn.Expr is evaluated and printed to the user.                                       
                    input (R.Success (Expr v)) = case (E.eval env M.empty v) of 
                                          R.Failure x -> do 
                                                        putStrLn ("Evaluation error. Try again. " ++ x)
                                                        repl env
                                          R.Success v -> do 
                                                        putStrLn (exprEvalToString v ) 
                                                        repl env
                                                    where 
                                                         -- //Prints the evalued expression to the user
                                                         exprEvalToString :: Syn.Value -> String 
                                                         exprEvalToString (Syn.PairVal l r) = 
                                                              "(" ++ (exprEvalToString l) ++ " . " ++ (exprEvalToString r) ++ ")"
                                                         exprEvalToString (Syn.Integer x) = show x     
                                                         exprEvalToString (Syn.Float x) = show x  
                                                         exprEvalToString (Syn.Boolean x) = show x 
                                                         exprEvalToString (Syn.Closure x e env) = show x ++ " " ++ show e ++ " " ++ show env                                                                             
                                      