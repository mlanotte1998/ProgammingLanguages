{- |
Module      :  Reduce
Description :  Normal-order reduction for Lambda calculus.

Maintainer  :  Ferd <f.vesely@northeastern.edu>
-}

module Reduce 
    ( normalize
    , normalizeWithCount
    , stepNormal
    , step
    ) where

import Data.List (delete, union)

import Lambda

-- |Iterate normal-order reduction until a normal form is reached
normalize :: Lambda -> Lambda
normalize = iter stepNormal

-- as above, but also count the number of steps
normalizeWithCount :: Lambda -> (Lambda, Integer)
normalizeWithCount = iterCount stepNormal

-- |Oerform one step of normal-order reduction.
-- Returns Nothing if no redex was found
stepNormal :: Lambda -> Maybe Lambda
stepNormal e@(App (Lam _ _) _) = reduce e
stepNormal (App e1 e2) = 
  case stepNormal e1 of
       Just e1' -> Just (App e1' e2)
       Nothing -> case stepNormal e2 of
                       Just e2' -> Just (App e1 e2')
                       Nothing -> Nothing
stepNormal (Lam x e) =
  case stepNormal e of
       Just e' -> Just (Lam x e')
       Nothing -> Nothing
stepNormal _ = Nothing

-- |Perform the next step in a series of reductions. Useful for debugging in
-- GHCi:
-- > stepNormal e
-- ...
-- > step it
-- ...
-- > step it
-- ...
-- etc.
step :: Maybe Lambda -> Maybe Lambda
step Nothing = Nothing
step (Just e) = stepNormal e 

-- |Beta redue the given PLC expression.
--
-- If the argument is not a redex, return nothing.
reduce :: Lambda -> Maybe Lambda
reduce (App (Lam x e1) e2) = Just $ subst x e2 e1
reduce _ = Nothing

-- |Substitution with variable renaming
subst :: Variable -> Lambda -> Lambda -> Lambda
subst x s t@(Var y) | x == y = s
                    | otherwise = t
subst x s t@(Lam y t') | x == y = t   
                       | otherwise = Lam y' (subst x s (subst y (Var y') t'))
  where 
    y' = makeFresh y [Var x, s, t']
subst x s (App e1 e2) = App (subst x s e1) (subst x s e2)

-- |Generate a new variable name that's fresh for the given set of expressions
makeFresh :: Variable -> [Lambda] -> Variable
makeFresh x es | x `notElem` fv = x
               | otherwise = findFresh 0
  where 
    findFresh n =
        let x'' = x' ++ show n
        in if x'' `elem` fv 
              then findFresh (n + 1) 
              else x''
    fv = foldr (\e xs -> freeVars e `union` xs) [] es
    x' = stripNumericSuffix x

-- |Collect the free variables of a lambda expression
freeVars :: Lambda -> [Variable]
freeVars (Var x) = [x]
freeVars (Lam x e) = delete x $ freeVars e
freeVars (App e1 e2) = freeVars e1 `union` freeVars e2

-- |Strip a numeric suffix of a variable name
stripNumericSuffix :: Variable -> Variable
stripNumericSuffix = reverse . dropWhile isDigit . reverse
  where 
      isDigit x = x `elem` "0123456789"

-- |Iterate a partial function
iter :: (a -> Maybe a) -> a -> a
iter f x = case f x of
    Just x' -> x' `seq` iter f x'
    Nothing -> x

-- |Iterate a pratial function, counting the number of steps
iterCount :: (a -> Maybe a) -> a -> (a, Integer)
iterCount f = aux 0
  where 
    aux n x = case f x of
        Just x' -> aux (n + 1) x'
        Nothing -> (x, n) 


