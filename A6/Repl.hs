
module Repl where 

import qualified Maps as M
import qualified SExpression as S
import qualified Parser as P
import qualified Syntax as Syn
import qualified Eval as E

--Data type respresenting an Expr or a Global Def
data DefOrExpr = GlobalDef Syn.GlobalDef
               | Expr Syn.Expr
              deriving(Eq, Show) 



-- //This is the Read, Evaluate, Print, Loop that takes any user input in the terminal
--   parses it into SExpressions, converts it into our protoscheme syntax, evaluates it,
--   Turns to result of the evaluation back into an SExpression and then outputs a string 
--   representing the evaluated expression. The REPL updates a map with any definitions the
--   user might create and checks the map each time it evaluates.
repl :: Syn.GlobalEnv -> IO [(Maybe Syn.ExprEval)]
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
                            -- //The function runFromSExpression takes the parsed input, a Maybe S.SExpression, 
                            --   and if the input is not an S.SExpression it returns nothing, if it is an S.List with "define",
                            --   representing the Syn.GlobalDef type Define, or an S.List with "defun", representing the Syn.GlobalDef
                            --   type Defun, the expressions are converted to their respective types
                            --   Simarly, if the input is an SExpression representing a Syn.Expr then it is converted as well
                            runFromSExpression :: (Maybe S.Expr) -> (Maybe DefOrExpr) 
                            runFromSExpression (Nothing) =  Nothing
                            runFromSExpression (Just (S.List [S.Symbol "define", S.Symbol x, e])) = (Just (GlobalDef (Syn.Define x (Syn.fromSExpression e))))
                            runFromSExpression (Just (S.List [S.Symbol "defun", S.Symbol x, S.List v, e])) = 
                                 (Just (GlobalDef (Syn.Defun x (makeFunctionArguments v) (Syn.fromSExpression e))))
                                   where 
                                      -- //Converts an S.SExpression Symbol to a Syn.Expr Variable
                                      makeFunctionArguments :: [S.Expr] -> (Syn.Variable, [Syn.Variable])
                                      makeFunctionArguments ((S.Symbol x):xs) = (x, makeFunctionArgumentsList xs)
                                          where 
                                               -- //Handles a list of S.SExpressions and converts it to a list of Syn.Expr
                                               --   by calling itself recursively
                                               makeFunctionArgumentsList :: [S.Expr] -> [Syn.Variable]
                                               makeFunctionArgumentsList [] = []
                                               makeFunctionArgumentsList ((S.Symbol x):xs) =  x : makeFunctionArgumentsList xs
                            runFromSExpression (Just x) = 
                                 Just (Expr (Syn.fromSExpression(x)))
                    -- //input is given the output of runFromSExpression as an argument, which is a Maybe DefOrExpr
                    --   if the input is Nothing, then there is a parse error and the user is prompted to try again
                    --   if the input is a Syn.GlobalDef, either of type Define or Defun, the user's definition is added to 
                    --   the environment unless it is already defined. The user is told of the definition being made or of
                    --   the error. Lastly, if the input is representative of an Syn.Expr the expression is evaluated and
                    --   printed to the user. 
                    input :: (Maybe DefOrExpr) -> IO [Maybe Syn.ExprEval]     
                    -- There was no input or no parsable input     
                    input Nothing = do
                                    putStrLn "Parse error. Try again."
                                    repl env
                    -- The GlobalDef type Define was the input, and the environment is updated to include the definition
                    -- unless it is already defined.
                    input (Just (GlobalDef (Syn.Define x y))) = if ((M.get env x) == Nothing) 
                                                   then 
                                                        do 
                                                            putStrLn ("Variable " ++ x ++ " defined.")
                                                            repl (M.set env x (Syn.Define x y)) 
                                                   else 
                                                        do 
                                                            putStrLn ("Error: variable " ++ x ++ " is already defined.")
                                                            repl env
                    -- The GlobalDef type Defun was the input, and the environment is updated to include the definition
                    -- unless it is already defined.
                    input (Just (GlobalDef (Syn.Defun x y e))) = if ((M.get env x) == Nothing) 
                                                   then 
                                                        do 
                                                            putStrLn ("Function " ++ x ++ " defined.")
                                                            repl (M.set env x (Syn.Defun x y e)) 
                                                   else 
                                                        do 
                                                            putStrLn ("Error: function " ++ x ++ " is already defined.")
                                                            repl env 
                    -- The input represents a Syn.Expr or Nothing. If Nothing, the user is prompted to try again, otherwise
                    -- the Syn.Expr is evaluated and printed to the user.                                       
                    input (Just (Expr v)) = case (E.eval env M.empty v) of 
                                          Nothing -> do 
                                                        putStrLn ("Evaluation error. Try again.")
                                                        repl env
                                          Just v -> do 
                                                        putStrLn (exprEvalToString v ) 
                                                        repl env
                                                    where 
                                                         -- //Prints the evalued expression to the user
                                                         exprEvalToString :: Syn.ExprEval -> String 
                                                         exprEvalToString (Syn.Eval_Pair l r) = 
                                                              "(" ++ (exprEvalToString l) ++ " . " ++ (exprEvalToString r) ++ ")"
                                                         exprEvalToString (Syn.Eval_Integer x) = show x     
                                                         exprEvalToString (Syn.Eval_Float x) = show x  
                                                         exprEvalToString (Syn.Eval_Boolean x) = show x                                                                             
      