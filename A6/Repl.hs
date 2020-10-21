
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




repl :: Syn.GlobalEnv -> IO [(Maybe Syn.ExprEval)]
repl env = do
   line <- getLine
   if (line == ":quit") 
      then 
           do 
               putStrLn "Bye bye."
               return []
      else 
           do       
           input (call line)
               where 
                    call x = runFromSExpression (P.parseSExpression(x))
                         where 
                            runFromSExpression :: (Maybe S.Expr) -> (Maybe DefOrExpr) 
                            runFromSExpression (Nothing) = Nothing
                            runFromSExpression (Just (S.List [S.Symbol "define", S.Symbol x, e])) = (Just (GlobalDef (Syn.Define x (Syn.fromSExpression e))))
                            runFromSExpression (Just (S.List [S.Symbol "defun", S.Symbol x, S.List v, e])) = 
                                 (Just (GlobalDef (Syn.Defun x (makeFunctionArguments v) (Syn.fromSExpression e))))
                                   where 
                                      makeFunctionArguments :: [S.Expr] -> (Syn.Variable, [Syn.Variable])
                                      makeFunctionArguments ((S.Symbol x):xs) = (x, makeFunctionArgumentsList xs)
                                          where 
                                               makeFunctionArgumentsList :: [S.Expr] -> [Syn.Variable]
                                               makeFunctionArgumentsList [] = []
                                               makeFunctionArgumentsList ((S.Symbol x):xs) =  x : makeFunctionArgumentsList xs
                            runFromSExpression (Just x) = Just (Expr (Syn.fromSExpression(x)))
                    input :: (Maybe DefOrExpr) -> IO [Maybe Syn.ExprEval]          
                    input Nothing = do
                                    putStrLn "Parse error. Try again."
                                    repl env
                    input (Just (GlobalDef (Syn.Define x y))) = if ((M.get env x) == Nothing) 
                                                   then 
                                                        do 
                                                            putStrLn ("Variable " ++ x ++ " defined.")
                                                            repl (M.set env x (Syn.Define x y)) 
                                                   else 
                                                        do 
                                                            putStrLn ("Error: variable " ++ x ++ " is already defined.")
                                                            repl env
                    input (Just (GlobalDef (Syn.Defun x y e))) = if ((M.get env x) == Nothing) 
                                                   then 
                                                        do 
                                                            putStrLn ("Function " ++ x ++ " defined.")
                                                            repl (M.set env x (Syn.Defun x y e)) 
                                                   else 
                                                        do 
                                                            putStrLn ("Error: function " ++ x ++ " is already defined.")
                                                            repl env                                        
                    input (Just (Expr v)) = case (E.eval env M.empty v) of 
                                          Nothing -> do 
                                                        putStrLn (show v)
                                                        putStrLn (show env)
                                                        putStrLn ("Evaluation error. Try again.")
                                                        repl env
                                          Just v -> do 
                                                        putStrLn (exprEvalToString v ) 
                                                        repl env
                                                    where 
                                                         exprEvalToString :: Syn.ExprEval -> String 
                                                         exprEvalToString (Syn.Eval_Pair l r) = "(" ++ (exprEvalToString l) ++ " . " ++ (exprEvalToString r) ++ ")"
                                                         exprEvalToString (Syn.Eval_Integer x) = show x     
                                                         exprEvalToString (Syn.Eval_Float x) = show x  
                                                         exprEvalToString (Syn.Eval_Boolean x) = show x                                                                             
      