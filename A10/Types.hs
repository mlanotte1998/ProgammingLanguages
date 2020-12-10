{-|
Module      : Types
Description : Types for protoScheme
Copyright   : (c) Ferd, 2020
Maintainer  : f.vesely@northeastern

Types used in protoScheme.

This module defines the type language of protoScheme. Types have the following syntax:

> <BaseType> ::= Integer
>              | Real
>              | Boolean
>
> <Type> ::= <BaseType>
>          | (-> <Type>+)
>          | (Pair-of <Type> <Type>)
>          | (List-of <Type>)
>          | <TypeVariable>

-}
module Types 
    ( BaseType (..)
    , Type(..)
    , Scheme(..)
    , TyVariable
    , Constraint
    , Substitution
    , fromSExpression
    , toSExpression
    , schemeFromSExpression
    , schemeToSExpression
    , showType
    , showScheme
    , unify
    , specializes
    , tySubst
    , applySubst
    , freeTyVars
    , freeSchemeVars
    , generalizeType
    , instantiateScheme
    , instantiateSchemeWith
    ) where

import Result
import Gensym

import qualified SExpression as S

import Data.Char (isUpper)
import Data.List (union, (\\))

-- |Type variables
type TyVariable = String

-- |Constraints between types. The pair @(ty1, ty2)@ represents a constraint @ty1 = ty2@.
type Constraint = (Type, Type)

-- |Type variable substitutions: sets of type-variable and type pairings.
type Substitution = [(TyVariable, Type)]

-- |Base types
data BaseType = TyInteger
              | TyReal
              | TyBoolean
              deriving (Show, Eq)

-- |protoScheme types
data Type = TyBase BaseType         -- ^Base types
          | TyArrow [Type]          -- ^Function type
          | TyPair Type Type        -- ^Pair type
          | TyList Type             -- ^List type
          | TyVar TyVariable        -- ^Type variable
          deriving (Show, Eq)

-- |Type schemes for polymorphic types.
data Scheme = All [TyVariable] Type
            deriving (Eq, Show)

-- |Convert an s-expression into a type, if possible.
fromSExpression :: S.Expr -> Result Type
fromSExpression (S.Symbol "Integer") = return $ TyBase TyInteger
fromSExpression (S.Symbol "Real") = return $ TyBase TyReal
fromSExpression (S.Symbol "Boolean") = return $ TyBase TyBoolean
fromSExpression (S.List (S.Symbol "->" : ses )) = TyArrow <$> mapM fromSExpression ses
fromSExpression (S.List [ S.Symbol "Pair-of", se1, se2 ]) = 
    TyPair <$> fromSExpression se1 <*> fromSExpression se2
fromSExpression (S.List [ S.Symbol "List-of", se]) = 
    TyList <$> fromSExpression se
fromSExpression (S.Symbol x) | isUpper (head x) = return $ TyVar x
fromSExpression _ = fail "Given s-expression cannot be parsed as a type"

-- |Convert a type into an s-expression.
toSExpression :: Type -> S.Expr
toSExpression (TyBase b) = S.Symbol $ base b
  where
    base TyInteger = "Integer"
    base TyReal = "Real"
    base TyBoolean = "Boolean"
toSExpression (TyArrow tys) =
    S.List $ S.Symbol "->" : map toSExpression tys
toSExpression (TyPair ty1 ty2) = 
    S.List [ S.Symbol "Pair-of", toSExpression ty1, toSExpression ty2 ]
toSExpression (TyList ty) = 
    S.List [ S.Symbol "List-of", toSExpression ty ]
toSExpression (TyVar x) = S.Symbol x

-- |Parse a scheme from an s-expression.
schemeFromSExpression :: S.Expr -> Result Scheme
schemeFromSExpression (S.List [S.Symbol symAll, S.List vars, tySexpr]) 
    | symAll `elem` ["All", "∀"] = 
        All <$> mapM unSymbol vars <*> fromSExpression tySexpr
  where
    unSymbol (S.Symbol x) | isUpper (head x) = return x
    unSymbol _ = fail "Expected a symbol starting with a capital letter"
schemeFromSExpression tySexpr = All [] <$> fromSExpression tySexpr

-- |Convert a type scheme to an s-expression.
schemeToSExpression :: Scheme -> S.Expr
schemeToSExpression (All [] ty) = toSExpression ty
schemeToSExpression (All vars ty) =
    S.List [S.Symbol "All", S.List $ map S.Symbol vars, toSExpression ty]

-- |Pretty print a type as its s-expression representation
showType :: Type -> String
showType = S.toString . toSExpression

-- |Pretty print a type as its s-expression representation
showScheme :: Scheme -> String
showScheme = S.toString . schemeToSExpression

-- |Unify the given list of constraints
unify :: [Constraint] -> Result Substitution
unify ((t1, t2) : rest) | t1 == t2 = unify rest
unify ((TyVar x, t) : rest) | x `notElem` freeTyVars t = do
    s <- unify $ map (tySubstConstr x t) rest
    return $ (x, t) : s
unify ((t, TyVar x) : rest) | x `notElem` freeTyVars t = do
    s <- unify $ map (tySubstConstr x t) rest
    return $ (x, t) : s
unify ((TyArrow tys, TyArrow tys') : rest) | length tys == length tys' =
    unify $ zip tys tys' ++ rest
unify ((TyPair ty1 ty2, TyPair ty1' ty2') : rest) = 
    unify $ [(ty1, ty1'), (ty2, ty2')] ++ rest
unify ((TyList ty, TyList ty') : rest) = 
    unify $ (ty, ty') : rest
unify [] = return []
unify ((t1, t2) : _) = fail $ "Could not unify " ++ showType t1 ++ " and " ++ showType t2

-- |Substitute type in a constraint.
tySubstConstr :: TyVariable -> Type -> Constraint -> Constraint
tySubstConstr x ty (ty1, ty2) = (tySubst x ty ty1, tySubst x ty ty2)


-- |Does the LHS type specialize the RHS type?
specializes :: Type -> Type -> Bool
_              `specializes` TyVar _ = True
TyArrow tys    `specializes` TyArrow tys' = and $ zipWith specializes tys tys'
TyPair ty1 ty2 `specializes` TyPair ty1' ty2' = ty1 `specializes` ty1' && ty2 `specializes` ty2'
TyList ty      `specializes` TyList ty' = ty `specializes` ty'
t1             `specializes` t2 = t1 == t2

-- |Substitute the given type for the given variable.
tySubst :: TyVariable -> Type -> Type -> Type
tySubst x t (TyArrow tys) = TyArrow $ map (tySubst x t) tys
tySubst x t (TyPair ty1 ty2) = TyPair (tySubst x t ty1) (tySubst x t ty2)
tySubst x t (TyList ty) = TyList (tySubst x t ty)
tySubst x t (TyVar y) | x == y = t
                      | otherwise = TyVar y
tySubst _ _ t' = t'

-- |Apply all substitutions in the given list to the given type
applySubst :: Substitution -> Type -> Type
applySubst ((x, t) : s) t' = applySubst s (tySubst x t t')
applySubst [] t' = t'

-- |Free type variables in a type.
freeTyVars :: Type -> [TyVariable]
freeTyVars (TyArrow tys) = foldl (\vars ty -> vars `union` freeTyVars ty) [] tys
freeTyVars (TyPair ty1 ty2) = freeTyVars ty1 `union` freeTyVars ty2
freeTyVars (TyList ty) = freeTyVars ty
freeTyVars (TyVar x) = [x]
freeTyVars _ = []

-- |Free type variables in a type scheme.
freeSchemeVars :: Scheme -> [TyVariable]
freeSchemeVars (All vars ty) = freeTyVars ty \\ vars

-- |Generalize the given type, omitting the given variables.
generalizeType :: [TyVariable] -> Type -> Scheme
generalizeType omit ty = All vars ty
  where 
    vars = freeTyVars ty \\ omit

-- |Instantiate a type scheme with fresh type variables.
instantiateScheme :: Scheme -> Type
instantiateScheme (All vars ty) = 
  vars' `seq` instantiateSchemeWith vars' (All vars ty)
  where
    vars' = map (\_ -> gensym "X") [1..length vars]

-- | Instantiate a type scheme with the given type variables.
instantiateSchemeWith :: [TyVariable] -> Scheme -> Type
instantiateSchemeWith newVars (All vars ty) = 
    applySubst (zip vars vars') ty
  where
    vars' = map TyVar newVars

