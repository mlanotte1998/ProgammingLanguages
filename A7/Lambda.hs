{- |
Module      :  Lambda
Description :  Pure Lambda Calculus abstract syntax.

Maintainer  :  Ferd <f.vesely@northeastern.edu>
-}
module Lambda 
    ( Variable
    , Lambda (..)
    , showLambda
    , fromSExpression
    , toSExpression
    , Lambda.allTests
    ) where

import qualified SExpression as S

import SimpleTestsColor (test, testSection)

import Control.Monad (mapM)

type Variable = String

data Lambda = Lam Variable Lambda
            | App Lambda Lambda
            | Var Variable
            deriving (Eq)

-- pretty printing Lambda terms
showLambda (Var x) = x
showLambda (Lam x e) = "(λ" ++ x ++ ". " ++ showLambda e ++ ")"
showLambda (App e1 e2) = "(" ++ showLambda e1 ++ " " ++ showLambda e2 ++ ")"

-- If you want Haskell to use the above pretty-printer as default (e.g., in 
-- GHCi), remove Show from the `deriving` clasue above and uncomment the 
-- instance definition below.
 
instance Show Lambda where
  show = showLambda



-- |Convert an s-expression into a lambda expression
fromSExpression :: S.Expr -> Maybe Lambda
fromSExpression (S.List [S.Symbol lambda, S.List vars, body]) 
    | lambda `elem` [ "lambda", "lam", "λ" ] && not (null vars) = do
        body' <- fromSExpression body
        vars' <- mapM unSymbol vars
        return $ foldr Lam body' vars'
  where
    unSymbol (S.Symbol x) = Just x
    unSymbol _ = Nothing
fromSExpression (S.List es@(_ : _ : _)) =
    foldl1 App <$> mapM fromSExpression es
fromSExpression (S.Symbol x) = return $ Var x
fromSExpression _ = Nothing
    
-- |Convert a lambda expression to an s-expression
toSExpression :: Lambda -> S.Expr
toSExpression (Var x) = S.Symbol x
toSExpression (App e1 e2) = S.List $ foldApps e1 e2
  where
    foldApps (App e1 e2) e3 = foldApps e1 e2 ++ [ toSExpression e3 ]
    foldApps e1 e2 = [ toSExpression e1, toSExpression e2 ]
toSExpression (Lam x e) = S.List [ S.Symbol "lambda", S.List vars, body ]
  where
    foldLam xs (Lam x e) = foldLam (S.Symbol x : xs) e
    foldLam xs e = (reverse xs, toSExpression e)
    (vars, body) = foldLam [ S.Symbol x ] e


test_fromSExpression = do
    testSection "fromSExpression"
    test "x" (fromSExpression (S.Symbol "x")) (Just $ Var "x")
    test "(x y)" 
        (fromSExpression (S.List [S.Symbol "x", S.Symbol "y"]))
        (Just $ App (Var "x") (Var "y"))
    test "(x (y z))" 
        (fromSExpression $
            S.List [ S.Symbol "x"
                   , S.List [ S.Symbol "y" , S.Symbol "z" ]
                   ])
        (Just $ App (Var "x") (App (Var "y") (Var "z")))
    test "((x y) z)" 
        (fromSExpression $
            S.List [ S.List [S.Symbol "x", S.Symbol "y" ]
                   , S.Symbol "z" 
                   ])
        (Just $ App (App (Var "x") (Var "y")) (Var "z"))
    test "(x y z)" 
        (fromSExpression $
            S.List [ S.Symbol "x", S.Symbol "y", S.Symbol "z" ])
        (Just $ App (App (Var "x") (Var "y")) (Var "z"))
    test "(x y z xx yy zz xxx yyy zzz)" 
        (fromSExpression $
            S.List [ S.Symbol "x", S.Symbol "y", S.Symbol "z" 
                   , S.Symbol "xx", S.Symbol "yy", S.Symbol "zz"
                   , S.Symbol "xxx", S.Symbol "yyy", S.Symbol "zzz"
                   ])
        (Just $ App 
                  (App 
                    (App 
                      (App 
                        (App 
                          (App 
                            (App 
                              (App (Var "x") (Var "y")) 
                              (Var "z")) 
                            (Var "xx")) 
                          (Var "yy")) 
                        (Var "zz")) 
                      (Var "xxx"))
                    (Var "yyy"))
                  (Var "zzz"))
    test "(lambda (x) x)"
        (fromSExpression $
            S.List [ S.Symbol "lambda"
                   , S.List [ S.Symbol "x" ]
                   , S.Symbol "x"
                   ])
        (Just $ Lam "x" (Var "x"))
    test "(lam (x y) x)"
        (fromSExpression $
            S.List [ S.Symbol "lam"
                   , S.List $ map S.Symbol [ "x", "y" ]
                   , S.Symbol "x"
                   ])
        (Just $ Lam "x" $ Lam "y" (Var "x"))
    test "(λ (x y z) x)"
        (fromSExpression $
            S.List [ S.Symbol "λ"
                   , S.List $ map S.Symbol [ "x", "y", "z" ]
                   , S.Symbol "x"
                   ])
        (Just $ Lam "x" $ Lam "y" $ Lam "z" (Var "x"))
    test "(λ (x y z) (x y z))"
        (fromSExpression $
            S.List [ S.Symbol "λ"
                   , S.List $ map S.Symbol [ "x", "y", "z" ]
                   , S.List $ map S.Symbol [ "x", "y", "z" ]
                   ])
        (Just $ 
            Lam "x" $ Lam "y" $ Lam "z"  
                (App (App (Var "x") (Var "y")) (Var "z")))
    test "((λ (x) (x x)) (lam (x) (x x)))"
        (fromSExpression $
            S.List [ S.List [ S.Symbol "λ"
                            , S.List [ S.Symbol "x" ]
                            , S.List $ map S.Symbol [ "x", "x" ]
                            ]
                   , S.List [ S.Symbol "lam"
                            , S.List [ S.Symbol "x" ]
                            , S.List $ map S.Symbol [ "x", "x" ]
                            ]
                   ])
        (Just $ 
            App (Lam "x" $ App (Var "x") (Var "x"))
                (Lam "x" $ App (Var "x") (Var "x")))

test_toSExpression = do
    testSection "toSExpression"
    test' (Var "x") (S.Symbol "x")
    test' 
        (Lam "x" $ Var "x") 
        (S.List [ S.Symbol "lambda", S.List [S.Symbol "x"], S.Symbol "x" ])
    test'
        (Lam "x" $ Lam "y" $ Lam "z"  
            (App (App (Var "x") (Var "y")) (Var "z")))
        (S.List [ S.Symbol "lambda"
                , S.List $ map S.Symbol [ "x", "y", "z" ]
                , S.List $ map S.Symbol [ "x", "y", "z" ]
                ])
    test' 
        (App (Var "x") (App (Var "y") (Var "z")))
        (S.List [ S.Symbol "x"
                , S.List [ S.Symbol "y" , S.Symbol "z" ]
                ])

        
  where
    test' x = test (show x) (toSExpression x)

allTests = do
    test_fromSExpression
    test_toSExpression

