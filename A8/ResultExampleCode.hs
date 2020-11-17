
import Maps

type Variable = String

data Value = Closure Variable Expr Env
           | Integer Integer
           | Boolean Bool
           | PrimOp Op Integer [Value]
           deriving (Show, Eq)

int i = Val (Integer i)
true = Val (Boolean True)
false = Val (Boolean False)

data Expr = Var Variable
          | Lam Variable Expr
          | App Expr Expr
          | And Expr Expr
          | If Expr Expr Expr
          | Let Variable Expr Expr
          | LetRec Variable Expr Expr
--          | PrimApp Op [Expr]
          | Val Value
           deriving (Show, Eq)

data Op = Op String ([Value] -> Result Value)
{-        |  AddOp
        | SubOp
        | MulOp
        | LeqOp
        | NotOp
        deriving (Show, Eq)-}

instance Show Op where
    show (Op s _) = "Op " ++ s

instance Eq Op where
    _ == _ = False

type Env = Map Variable Value

-- Call-by-value evaluator

eval :: Env -> Expr -> Result Value
eval env (Var x) = case get env x of
    Just v -> return v
    Nothing -> fail $ "Variable " ++ x  ++ " not defined."
eval env (Lam x e) = return $ Closure x e env
eval env (App e1 e2) = do
    v1 <- eval env e1
    case v1 of 
         Closure x e env' -> do
            v2 <- eval env e2
            eval (set env' x v2) e
         PrimOp op 1 args -> do 
            v2 <- eval env e2
            apply op (args ++ [v2])
         PrimOp op n args | n > 1 -> do 
            v2 <- eval env e2
            return $ PrimOp op (n - 1) (args ++ [v2])
{-eval env (Add e1 e2) = do
    Integer i1 <- eval env e1
    Integer i2 <- eval env e2
    return $ Integer $ i1 + i2
eval env (Sub e1 e2) = do
    Integer i1 <- eval env e1
    Integer i2 <- eval env e2
    return $ Integer $ i1 - i2
eval env (Mul e1 e2) = do
    Integer i1 <- eval env e1
    Integer i2 <- eval env e2
    return $ Integer $ i1 * i2
eval env (Leq e1 e2) = do 
    Integer i1 <- eval env e1
    Integer i2 <- eval env e2
    return $ Boolean $ i1 <= i2-}
eval env (If e1 e2 e3) = do
    Boolean b <- eval env e1
    if b then eval env e2
         else eval env e3
eval env (Let x e1 e2) = do
  v1 <- eval env e1
  eval (set env x v1) e2
  -- eval env (App (Lam x e2) e1)
eval env (LetRec x e1 e2) = do -- letrec x = e1 in e2 ==> let x = fix (λx. e1) in e2
  v1 <- eval env (App zComb (Lam x e1))
  eval (set env x v1) e2
  -- eval env (Let x (App zComb (Lam x e1)) e2)
{-eval env (PrimApp op es) = do
    vs <- mapM (eval env) es
    apply op vs
  where evalArgs (e : es) = do
            v <- eval env e
            vs <- evalArgs es
            return $ v : vs
        evalArgs [] = return []
        {-
        mapM :: Monad m => (a -> m b) -> [a] -> m [b]
        mapM f (x : xs) = 
          y <- f x
          ys <- mapM f xs
          return $ y : ys
        mapM f [] = return []
        -}
-}
eval env (Val v) = return v


apply :: Op -> [Value] -> Result Value
{-apply AddOp [Integer i1, Integer i2] = return $  Integer $ i1 + i2
apply SubOp [Integer i1, Integer i2] = return $  Integer $ i1 - i2
apply MulOp [Integer i1, Integer i2] = return $  Integer $ i1 * i2
apply LeqOp [Integer i1, Integer i2] = return $ Boolean $ i1 <= i2
apply NotOp [Boolean b] = return $ Boolean $ not b
apply _ _ = fail "Invalid operation or arguments."-}
apply (Op _ f) vs = f vs

addOp = PrimOp (Op "+" op) 2 []
  where
    op [Integer i1, Integer i2] = return $ Integer $ i1 + i2
    op _ = fail "Wrong number or type of arguments."
mulOp = PrimOp (Op "*" op) 2 []
  where
    op [Integer i1, Integer i2] = return $ Integer $ i1 * i2
    op _ = fail "Wrong number or type of arguments."
subOp = PrimOp (Op "-" op) 2 []
  where
    op [Integer i1, Integer i2] = return $ Integer $ i1 - i2
    op _ = fail "Wrong number or type of arguments."
leqOp = PrimOp (Op "<=" op) 2 []
  where
    op [Integer i1, Integer i2] = return $ Boolean $ i1 <= i2
    op _ = fail "Wrong number or type of arguments."


builtins = 
  [ ("+", addOp)
  , ("-", subOp)
  , ("<=", leqOp)
  ]

ex1 = LetRec "sum" (Lam "n" $
          (If (App (App (Var "<=") (Var "n")) (int 0))
          (int 0)
          (App (App (Var "+") (Var "n"))
               (App (Var "sum") (App (App (Var "-") (Var "n")) (int 1))))))
      (App (Var "sum") (int 5))

zComb = Lam "f" $ 
        (Lam "x" $ Var "f" `App` Lam "v" (Var "x" `App` Var "x" `App` Var "v"))
  `App` (Lam "x" $ Var "f" `App` Lam "v" (Var "x" `App` Var "x" `App` Var "v"))



data Result a = Success a
              | Failure String
              deriving (Show, Eq)


{-
- class Functor f where
-     fmap :: (a -> b) -> f a -> f b
-
- instance Functor Maybe where
-     fmap _ Nothing = Nothing
-     fmap f (Just x) = Just $ f x
-}

instance Functor Result where
    fmap f (Success x) = Success $ f x
    fmap _ (Failure s) = Failure s

{-
- class Functor f => Applicative f where
-     pure :: a -> f a
-     (<*>) :: f (a -> b) -> f a -> f b
-}

instance Applicative Result where
    pure x = Success x
    Success f <*> x = fmap f x
    Failure s <*> _ = Failure s

{-
class Applicative m => Monad m where
    return :: a -> m a
    (>>=) :: m a -> (a -> m b) -> m b

for maybe:
  return :: a -> Maybe a
  return x = Just x

  (>>=) :: Maybe a -> (a -> Maybe b) -> Maybe b
  Just x >>= f = f x
  Nothing >>= _ = Nothing

  eval e1 >>= \v1 -> eval e2 >>= \v2 -> return $ v1 + v2
-}
instance Monad Result where
    return x = Success x
    Success x >>= f = f x
    Failure s >>= _ = Failure s

instance MonadFail Result where
  fail s = Failure s

eval' :: Env -> Expr -> Result Value
eval' env (Val v) = return v
eval' env (Var x) = case get env x of
                         Just v -> Success v
                         Nothing -> Failure "Variable not found"
eval' env (If e1 e2 e3) = do
    Boolean b <- eval' env e1
    if b then eval' env e2
         else eval' env e3





