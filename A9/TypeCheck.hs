{-# LANGUAGE TupleSections #-}
{-|
Module      : TypeCheck
Description : A type-checker for protoScheme with type inference and let-polymorphism.
Copyright   : (c) Ferd, 2020
Maintainer  : f.vesely@northeastern

An implementation of the protoScheme type-checker.

-}
module TypeCheck where

import Prelude hiding (Left, Right)
import Types
import Maps
import Syntax 
import Result

import qualified SExpression as S

import SimpleTestsColor (test, testSection)

-- |Type environments
type TyEnv = Map Variable Type

-- |Compute the type of the given expression
typeOf :: TyEnv -> Expr -> Result Type
typeOf _ (Val v) = TyBase <$> typeOfValue v
  where
    typeOfValue :: Value -> Result BaseType
    typeOfValue (Integer _) = return TyInteger
    typeOfValue (Float _) = return TyReal
    typeOfValue (Boolean _) = return TyBoolean
    typeOfValue _ = fail "Invalid value."
typeOf tenv (Var x) = 
    fromMaybe' ("Variable " ++ x ++ " is not defined") $
        get tenv x
-- typeOf tenv e@(Lambda (x : ty) body) = do
--     ty' <- typeOf (set tenv x ty) body 
--     return $ TyArrow [ty, ty']
-- typeOf tenv (App (e1:elist)) = do 
--     TyArrow [ty2, ty1] <- typeOf tenv e1
--     ty2' <- typeOf tenv elist
--     if ty2 == ty2'
--         then return ty1
--         else fail "Argument types do not match"
typeOf tenv (Pair e1 e2) = do
    ty1 <- typeOf tenv e1
    ty2 <- typeOf tenv e2
    return $ TyPair ty1 ty2
typeOf tenv (Left e) = do 
    TyPair ty1 _ <- typeOf tenv e
    return ty1
typeOf tenv (Right e) = do
    TyPair _ ty2 <- typeOf tenv e
    return ty2
typeOf tenv _ = undefined


-- |Compute the type of the given program, relative to the given type environment
typeOfProgram :: TyEnv -> Program -> Result Type
typeOfProgram _ _ = undefined -- TODO: complete

-- |Compute the 
typeOfProgramSExpr :: [S.Expr] -> Result S.Expr
typeOfProgramSExpr sexprs = do
    typ <- typeOfProgram tyBase (programFromSExpression (S.List [S.Symbol "Program", S.List sexprs]))
    return $ Types.toSExpression typ

tyBase = empty -- TODO: complete 

