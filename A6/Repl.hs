
import qualified Parser as P
import qualified Syntax as Syn

calcLoop :: Syn.GlobalEnv -> IO [Maybe Syn.ExprEval]
calcLoop numbers = do
   line <- getLine
   input call 
      where 
        call = runFromSExpression P.parseSExpression(line) 
                where 
                  runFromSExpression :: (Maybe S.Expr) -> (Maybe Expr) 
                  runFromSExpression (Nothing) = Nothing
                  runFromSExpression (Just x) = Syn.fromSExpression(parsedLine)
   
    where
      input "quit" = do
        putStrLn "Bye bye."
        return []
      input "+" = do
        putStrLn $ "Result: " ++ show (sum numbers)
        calcLoop []
      input "-" = do
        putStrLn $ "Result: " ++ show (product numbers)
        calcLoop []
      input "*" = do
        putStrLn $ "Result: " ++ show (sum numbers)
        calcLoop []
      input "/" = do
        putStrLn $ "Result: " ++ show (product numbers)
        calcLoop []
      input "print" = do
        putStrLn $ "This is what I have so far: " ++ show numbers
        calcLoop numbers
      input other = do
        calcLoop $ read other : numbers

main :: IO ()
main = do
    putStrLn "Welcome to the mostly useless calculator program."
    calcLoop []
    return ()