{-# LANGUAGE TupleSections #-}
{-|
Module      : TypeCheck
Description : A type-checker for protoScheme with type inference and let-polymorphism.
Copyright   : (c) Ferd, 2020
                  Michael Lanotte, 2020
                  Rachel Johanek, 2020
Maintainer  : f.vesely@northeastern
              lanotte.m@northeastern.edu
              johanek.r@northeastern.edu

An implementation of the protoScheme type-checker.

-}
module TypeCheck where

import Prelude hiding (Left, Right)
import qualified Types as T
import Maps
import Syntax 
import Result
import Gensym

import Parser

import System.IO.Unsafe (unsafePerformIO)

import qualified SExpression as S

import SimpleTestsColor (test, testSection)

-- |Type environments
type TyEnv = Map Variable T.Type

-- |Compute the type of the given expression
typeOf :: TyEnv -> Expr -> Result (T.Type, [T.Constraint])

typeOf tenv (Val v) = typeOfValue tenv v
  where
    typeOfValue :: TyEnv -> Value -> Result (T.Type, [T.Constraint])
    typeOfValue _ (Integer _) = return (T.TyBase T.TyInteger, [])
    typeOfValue _ (Float _) = return (T.TyBase T.TyReal, [])
    typeOfValue _ (Boolean _) = return (T.TyBase T.TyBoolean, [])
    typeOfValue t (PairVal l r) = do
        (l', cl) <- typeOfValue t l
        (r', cr) <- typeOfValue t r
        return (T.TyPair l' r', cl++cr)
    typeOfValue _ _ = fail "Invalid value."
typeOf tenv (Var x) = do
    t <- fromMaybe' ("Variable " ++ x ++ " is not defined") $ get tenv x
    return (t, [])
typeOf tenv (Let x e1 e2) = do 
    (ty1, c1) <- typeOf tenv e1 
    (ty2, c2) <- typeOf (set tenv x ty1) e2 
    return (ty2, c1 ++ c2)  
typeOf tenv (Pair l r) = do 
    (l', cl) <- typeOf tenv l
    (r', cr) <- typeOf tenv r
    return (T.TyPair l' r', cl ++ cr)
typeOf tenv (Left e) = do 
    (t1, c1) <- typeOf tenv e
    case t1 of 
        T.TyPair l r -> return (l, ([(t1, (T.TyPair l r))] ++ c1))
        _ -> fail "Left was not called on a pair."
typeOf tenv (Right e) = do
    (t1, c1) <- typeOf tenv e
    case t1 of 
        T.TyPair l r -> return (r, ([(t1, (T.TyPair l r))] ++ c1))   
        _ -> fail "Right was not called on a pair."
typeOf tenv (Lambda vars e) = do
    -- make env with all of the variables and get the type and constraints of the body.
    (tenv', vartypes) <- Success $ addVarsToEnv tenv vars []
    (ty', c') <- typeOf tenv' e
    -- append the type of the body as the return type for the tyArrow with the sig type list as the args. 
    return (T.TyArrow (vartypes ++ [ty']), c')
    where 
        -- Takes a type env and a list of variables, an d a list of types, adds each variable
        -- to the environment, and stores the type of each (TyVar tX) in a list of Types
        -- returns the updated environment and list of types
        addVarsToEnv :: TyEnv -> [Variable] -> [T.Type] -> (TyEnv, [T.Type])
        addVarsToEnv tenv [] list = (tenv, list)
        addVarsToEnv tenv (x:xs) list = do
            let tX = T.TyVar (gensym "X")
            addVarsToEnv (set tenv x tX) xs (list++[tX])

typeOf tenv (App (func : argList)) = do 
    (t1, c1) <- typeOf tenv func
    (t2, c2) <- getArgumentTypeList tenv argList 
    let tX = T.TyVar $ gensym "Y"
    return (tX, [(t1, T.TyArrow (t2++[tX]))] ++ c1 ++ c2)
    where  
        getArgumentTypeList :: TyEnv -> [Expr] -> Result ([T.Type], [T.Constraint])
        getArgumentTypeList tenv (arg : list) = do
            (t, c) <- typeOf tenv arg
            (t2, c2) <- getArgumentTypeList tenv list
            return (t : t2, c ++ c2)
        getArgumentTypeList tenv [] = Success ([], [])
typeOf tenv (If e1 e2 e3) = do
    (ty1, c1) <- typeOf tenv e1
    case ty1 of 
        T.TyBase T.TyBoolean -> do
            (ty2, c2) <- typeOf tenv e2
            (ty3, c3) <- typeOf tenv e3
            if ty2 == ty3
                then return (ty2, [(ty1, T.TyBase T.TyBoolean), (ty2, ty3)] ++ c1 ++ c2 ++ c3)
                else fail "Incompatible return types for If"
        _ -> fail "First argument in If was not of type TyBoolean."       
typeOf tenv (And e1 e2) = do 
    (ty1, c1) <- typeOf tenv e1 
    (ty2, c2) <- typeOf tenv e2
    return (T.TyBase T.TyBoolean, [(ty1, T.TyBase T.TyBoolean), (ty2, T.TyBase T.TyBoolean)] ++ c1 ++ c2 )                  
typeOf tenv (Or e1 e2) = do 
    (ty1, c1) <- typeOf tenv e1 
    (ty2, c2) <- typeOf tenv e2
    return (T.TyBase T.TyBoolean, [(ty1, T.TyBase T.TyBoolean), (ty2, T.TyBase T.TyBoolean)] ++ c1 ++ c2 )           
typeOf tenv (Cond [] e3) = do
    case e3 of 
        Nothing -> fail "Cond has no return type."
        Just x ->  typeOf tenv x
typeOf tenv (Cond ((e1, e2) : xs) e3) = do 
    (ty1, c1) <- typeOf tenv e1 
    (ty2, c2) <- typeOf tenv e2
    clist <- typeOfCondList tenv xs ty2
    case e3 of  
        Nothing -> return (ty2, [(ty1, T.TyBase T.TyBoolean)] ++ c1 ++ c2 ++ clist)
        Just e3' -> do
            (ty3, c3) <- typeOf tenv e3'
            return (ty2, [(ty1, T.TyBase T.TyBoolean)] ++ c1 ++ c2 ++ clist ++ [(ty3, ty2)] ++ c3)                           
        where 
            -- ensures that the whole cond list has a boolean clause and the same
            -- expr type for the e2 of each pairing and if so then return that type. 
            -- accumulates constraints
            typeOfCondList :: TyEnv -> [(Expr, Expr)] -> T.Type -> Result [T.Constraint]
            typeOfCondList _ [] t = return []
            typeOfCondList tenv ((e1, e2) : xs) t = do
                (ty1, c1) <- typeOf tenv e1 
                (ty2, c2) <- typeOf tenv e2 
                rest <- typeOfCondList tenv xs t     
                return ([(ty1, T.TyBase T.TyBoolean)] ++ c1 ++ [(ty2, t)] ++ c2 ++ rest)
-- gotta fix nil                
-- typeOf _ Nil = return (???) 
-- -- Probably need to iterate through cons until reaching nil 
-- -- because nil wont know what type to return
-- typeOf tenv (Cons e1 e2) = 
--     case typeOf tenv e1 of
--         Success ty1 -> case typeOf tenv e2 of 
--                             Success (TyList ty2) -> if ty1 == ty2 
--                                              then return (TyList ty2)
--                                              else fail "Cons list has inconsistent types" 
--                             Success _ -> fail "Cons list is not properly structed."                 
--                             f -> f 
--         Failure f -> fail $ "Cons failed because of inner element error: " ++ f                
-- -- For predicates, if e type checks to anything then return boolean        
-- typeOf tenv (List_Pred e) = 
--     case typeOf tenv e of 
--         Success _ -> return $ TyBase TyBoolean
--         Failure f -> fail $ "List_Pred failed because: " ++ f  
-- typeOf tenv (Cons_Pred e) = 
--     case typeOf tenv e of 
--         Success _ -> return $ TyBase TyBoolean
--         Failure f -> fail $ "Cons_Pred failed because: " ++ f 
-- typeOf tenv (Nil_Pred e) = 
--     case typeOf tenv e of 
--         Success _ -> return $ TyBase TyBoolean
--         Failure f -> fail $ "Nil_Pred failed because: " ++ f
-- typeOf tenv (Head e) = do 
--     case typeOf tenv e of 
--         Success (TyList t) -> return t
--         Success _ -> fail "Head not called on list."
--         Failure f -> fail $ "Head failed because: " ++ f       
-- typeOf tenv (Tail e) = do 
--     case typeOf tenv e of 
--         Success (TyList t) -> return (TyList t)
--         Success _ -> fail "Tail not called on list."
--         Failure f -> fail $ "Tail failed because: " ++ f                                               

typeOf _ _ = fail "Given incompatible expr."

-- ====================================================================================================

-- |Compute the type of the given program, relative to the given type environment
typeOfProgram :: TyEnv -> Program -> Result T.Type
typeOfProgram tenv (Program globalDefs e) = 
    case ensureGlobalDefTypes tenv globalDefs of 
        Success tenv' -> do 
            (t, c) <- typeOf tenv' e
            return t
        Failure f -> fail f

-- Adds all of the program define and defun types to the type environment
typeOfProgramTyEnv :: TyEnv -> [S.Expr] -> Result TyEnv 
typeOfProgramTyEnv tenv [] = return tenv
typeOfProgramTyEnv tenv (S.List[S.Symbol name, S.Symbol ":", typeSignature] : _ :xs) = 
    case T.fromSExpression typeSignature of 
        Success ty -> typeOfProgramTyEnv (set tenv name ty) xs 
        Failure f -> fail f

-- Checks the given program define and defun types with their actual computed types
ensureGlobalDefTypes :: TyEnv -> [GlobalDef] -> Result TyEnv
ensureGlobalDefTypes tenv [] = return tenv 
ensureGlobalDefTypes tenv ((Define (Sig name _) e):xs) = do 
    case typeOf tenv e of 
        Success (ty, c) -> do 
            -- will always be defined but in here as precaution
            ty' <- fromMaybe' ("Variable " ++ name ++ " is not defined") $ get tenv name
            if ty == ty' 
                then ensureGlobalDefTypes tenv xs 
                else fail $ "Function or variable " ++ name ++ " actual type is not the same as the expected type."
        Failure f -> fail $ "Possible function or variable " ++ name ++ " with incorrect type: " ++ f        


-- |Compute the type of program given a list of SExpr - program form, and return a SExpr of the type. 
typeOfProgramSExpr :: [S.Expr] -> Result S.Expr
typeOfProgramSExpr sexprs = do
    -- Get the program
    (Program globals e) <- programFromSExpression (S.List [S.Symbol "Program", S.List sexprs])
    -- Build up the TyEnv with the parsed types from the s expr.
    case typeOfProgramTyEnv tyBase (init sexprs) of 
        Success tenv' -> do 
            -- pass on the updated TyEnv to then compute the program type. 
            case typeOfProgram tenv' (Program globals e) of 
                Success ty -> return $ T.toSExpression ty
                Failure f -> fail f
        Failure f -> fail f                      


-- =====================================================================================================================


integerToIntegerIsInteger = T.TyArrow [T.TyBase T.TyInteger, T.TyBase T.TyInteger, T.TyBase T.TyInteger]
integerToIntegerIsBoolean = T.TyArrow [T.TyBase T.TyInteger, T.TyBase T.TyInteger, T.TyBase T.TyBoolean]

booleanIsBoolean = T.TyArrow [T.TyBase T.TyBoolean, T.TyBase T.TyBoolean]

tyBase = fromList 
  [
      ("+", integerToIntegerIsInteger),
      ("-", integerToIntegerIsInteger),
      ("*", integerToIntegerIsInteger),
      ("/", integerToIntegerIsInteger),
      ("not", booleanIsBoolean),
      ("<", integerToIntegerIsBoolean),
      (">", integerToIntegerIsBoolean),
      ("=", integerToIntegerIsBoolean),
      ("<=", integerToIntegerIsBoolean),
      (">=", integerToIntegerIsBoolean)
  ]

typeCheck :: TyEnv -> Expr -> Result T.Type
typeCheck tenv e = do
  (t, c) <- typeOf tenv e
  s <- T.unify c
  return $ T.applySubst s t   


-- =================================================================================================================
test_typeOf = do 

    -- Basic Tests 
    test "typeOf test integer" (typeCheck tyBase (Val (Integer 2))) (Success (T.TyBase T.TyInteger))

    test "typeOf test real" (typeCheck tyBase (Val (Float 2.5))) (Success (T.TyBase T.TyReal))

    test "typeOf test boolean" (typeCheck tyBase (Val (Boolean True))) (Success (T.TyBase T.TyBoolean))

    test "typeOf test undefined var" (typeCheck tyBase (Var "x")) (fail "Variable x is not defined")

    test "typeOf test defined var" (typeCheck (set empty "x" (T.TyBase T.TyInteger)) (Var "x")) (Success (T.TyBase T.TyInteger))

    test "typeOf test let" (typeCheck tyBase (Let "x" (Val (Integer 20)) (Var "x"))) (Success (T.TyBase T.TyInteger))

    test "typeOf test pair" (typeCheck tyBase (Pair (Val (Integer 10)) (Val (Float 4.1)))) (Success (T.TyPair (T.TyBase T.TyInteger) (T.TyBase T.TyReal)))

    test "typeOf test left on pair" (typeCheck tyBase (Left (Pair (Val (Integer 10)) (Val (Float 4.1))))) (Success (T.TyBase T.TyInteger))

    test "typeOf test left not on pair" (typeCheck tyBase (Left (Val (Integer 10)))) (Failure "Left was not called on a pair.")

    test "typeOf test right on pair" (typeCheck tyBase (Right (Pair (Val (Integer 10)) (Val (Float 4.1))))) (Success (T.TyBase T.TyReal))
    
    test "typeOf test right not on pair" (typeCheck tyBase (Right (Val (Float 4.1)))) (Failure "Right was not called on a pair.")

     -- And tests 
    test "typeof test and success" (typeCheck tyBase (And (Val (Boolean True)) (Val (Boolean True)))) (Success (T.TyBase T.TyBoolean))

    test "typeOf test and mismatch 1" (typeCheck tyBase (And (Val (Boolean True)) (Val (Integer 10)))) (Failure "Could not unify Integer and Boolean")

    test "typeOf test and mismatch 2" (typeCheck tyBase (And (Val (Integer 10)) (Val (Boolean True)))) (Failure "Could not unify Integer and Boolean")
    
    -- Or tests
    test "typeof test or success" (typeCheck tyBase (Or (Val (Boolean True)) (Val (Boolean True)))) (Success (T.TyBase T.TyBoolean))

    test "typeOf test or mismatch 1" (typeCheck tyBase (Or (Val (Boolean True)) (Val (Integer 10)))) (Failure "Could not unify Integer and Boolean") 
    
    test "typeOf test or mismatch 2" (typeCheck tyBase (Or (Val (Integer 10)) (Val (Boolean True)))) (Failure "Could not unify Integer and Boolean")
    
    -- If tests
    test "typeOf test if success" (typeCheck tyBase (If (Val (Boolean False)) (Val (Integer 10)) (Val (Integer 11)))) (Success (T.TyBase T.TyInteger))
        
    test "typeOf test if fail 1" (typeCheck tyBase (If (Val (Integer 9)) (Val (Integer 10)) (Val (Integer 11)))) (fail "First argument in If was not of type TyBoolean." )   

    test "typeOf test if fail 2" (typeCheck tyBase (If (Val (Boolean True)) (Val (Integer 10)) (Val (Boolean False)))) (fail "Incompatible return types for If")  

    test "typeOf test if fail 2" (typeCheck tyBase (If (Val (Boolean True)) (Val (Integer 10)) (Val (Boolean False)))) (fail "Incompatible return types for If") 

    --  Cond Tests
    test "typeOf test Cond success 1" (typeCheck tyBase ( Cond [(Val (Boolean True), 
     App [Var "+", Val (Integer 5), Val (Integer 2)])]  Nothing))
       (Success (T.TyBase T.TyInteger))

    test "typeOf test Cond success 2" (typeCheck tyBase (Cond [(Val (Boolean False), 
     App [Var "+", Val (Integer 5), Val (Integer 2)]), 
        (Val (Boolean True), App [Var "/", Val (Integer 4), Val (Integer 2)])] Nothing))
        (Success (T.TyBase T.TyInteger))

    test "typeOf Cond first clause isnt boolean" (typeCheck tyBase (Cond [(Val (Integer 10), 
     App [Var "+", Val (Integer 5), Val (Integer 2)]), 
        (Val (Boolean False), App [Var "/", Val (Integer 4), Val (Integer 2)])]
         (Just (App [Var "-", Val (Integer 5), Val (Integer 2)]))))
       (Failure "Could not unify Integer and Boolean")   

    test "typeOf Cond non first clause isnt boolean" (typeCheck tyBase (Cond [(Val (Boolean False), 
     App [Var "+", Val (Integer 5), Val (Integer 2)]), 
        (Val (Float 20), App [Var "/", Val (Integer 4), Val (Integer 2)])]
         (Just (App [Var "-", Val (Integer 5), Val (Integer 2)]))))
       (Failure "Could not unify Real and Boolean")     

    test "typeOf Cond with else that is not of the same type" (typeCheck tyBase (Cond [(Val (Boolean False), 
     App [Var "+", Val (Integer 5), Val (Integer 2)]), 
        (Val (Boolean False), App [Var "/", Val (Integer 4), Val (Integer 2)])]
         (Just (Val (Boolean False)))))
       (Failure "Could not unify Boolean and Integer")

    test "typeOf Cond with else that is the same return type" (typeCheck tyBase (Cond [(Val (Boolean False), 
     App [Var "+", Val (Integer 5), Val (Integer 2)]), 
        (Val (Boolean False), Val (Integer 10))]
         (Just (App [Var "-", Val (Integer 5), Val (Integer 2)]))))
       (Success (T.TyBase T.TyInteger))

    test "typeOf Cond with else that has expressions in list of different type" (typeCheck tyBase (Cond [(Val (Boolean False), 
     App [Var "+", Val (Integer 5), Val (Integer 2)]), 
        (Val (Boolean True), Val (Float 10.5))]
         (Just (App [Var "-", Val (Integer 5), Val (Integer 2)]))))
       (Failure "Could not unify Real and Integer")   

    -- Predicates

    test "typeOf test Boolean?" (typeCheck tyBase (Boolean_Pred (Val (Boolean True)))) (fail "Given incompatible expr.")

    test "typeOf test Real?" (typeCheck tyBase (Real_Pred (Val (Boolean True)))) (fail "Given incompatible expr.")

    test "typeOf test Integer?" (typeCheck tyBase (Integer_Pred (Val (Boolean True)))) (fail "Given incompatible expr.")

    test "typeOf test Number?" (typeCheck tyBase (Number_Pred (Val (Boolean True)))) (fail "Given incompatible expr.")

    test "typeOf test Pair?" (typeCheck tyBase (Pair_Pred (Val (Boolean True)))) (fail "Given incompatible expr.")   
       

    -- Add Tests

    test "typeOf test app with + success" (typeCheck tyBase (App [Var "+", Val (Integer 10),Val (Integer 20)])) (Success (T.TyBase T.TyInteger))

    test "typeOf test app with + fail not enough arguments" (typeCheck tyBase (App [Var "+", Val (Integer 10)])) (Failure "Could not unify (-> Integer Integer Integer) and (-> Integer Y#10)")

    test "typeOf test app with + fail too many arguments" (typeCheck tyBase (App [Var "+", Val (Integer 10), Val (Integer 5), Val (Integer 30)])) (Failure "Could not unify (-> Integer Integer Integer) and (-> Integer Integer Integer Y#11)")

    test "typeOf test app with + argument types did not match 1" (typeCheck tyBase (App [Var "+", Val (Boolean True), Val (Integer 5), Val (Integer 30)])) (Failure "Could not unify (-> Integer Integer Integer) and (-> Boolean Integer Integer Y#12)")

    test "typeOf test app with + argument types did not match 2" (typeCheck tyBase (App [Var "+", Val (Integer 10), Val (Boolean False), Val (Integer 30)])) (fail "Could not unify (-> Integer Integer Integer) and (-> Integer Boolean Integer Y#13)")

    -- Sub Tests

    test "typeOf test app with - success" (typeCheck tyBase (App [Var "-", Val (Integer 10),Val (Integer 20)])) (Success (T.TyBase T.TyInteger))

    test "typeOf test app with - fail not enough arguments" (typeCheck tyBase (App [Var "-", Val (Integer 10)])) (Failure "Could not unify (-> Integer Integer Integer) and (-> Integer Y#15)")

    test "typeOf test app with - fail too many arguments" (typeCheck tyBase (App [Var "-", Val (Integer 10), Val (Integer 5), Val (Integer 30)])) (Failure "Could not unify (-> Integer Integer Integer) and (-> Integer Integer Integer Y#16)")

    test "typeOf test app with - argument types did not match 1" (typeCheck tyBase (App [Var "-", Val (Boolean True), Val (Integer 5), Val (Integer 30)])) (fail "Could not unify (-> Integer Integer Integer) and (-> Boolean Integer Integer Y#17)")

    test "typeOf test app with - argument types did not match 2" (typeCheck tyBase (App [Var "-", Val (Integer 10), Val (Boolean False), Val (Integer 30)])) (fail "Could not unify (-> Integer Integer Integer) and (-> Integer Boolean Integer Y#18)")

    -- Mul Tests

    test "typeOf test app with * success" (typeCheck tyBase (App [Var "*", Val (Integer 10),Val (Integer 20)])) (Success (T.TyBase T.TyInteger))

    test "typeOf test app with * fail not enough arguments" (typeCheck tyBase (App [Var "*", Val (Integer 10)])) 
     (fail "Could not unify (-> Integer Integer Integer) and (-> Integer Y#20)")

    test "typeOf test app with * fail too many arguments" (typeCheck tyBase (App [Var "*", Val (Integer 10), Val (Integer 5), Val (Integer 30)])) 
     (fail "Could not unify (-> Integer Integer Integer) and (-> Integer Integer Integer Y#21)")

    test "typeOf test app with * argument types did not match 1" (typeCheck tyBase (App [Var "*", Val (Boolean True), Val (Integer 5), Val (Integer 30)])) 
     (fail "Could not unify (-> Integer Integer Integer) and (-> Boolean Integer Integer Y#22)")

    test "typeOf test app with * argument types did not match 2" (typeCheck tyBase (App [Var "*", Val (Integer 10), Val (Boolean False), Val (Integer 30)])) 
     (fail "Could not unify (-> Integer Integer Integer) and (-> Integer Boolean Integer Y#23)")

    -- Div Tests

    test "typeOf test app with / success" (typeCheck tyBase (App [Var "/", Val (Integer 10),Val (Integer 20)])) 
     (Success (T.TyBase T.TyInteger))

    test "typeOf test app with / fail not enough arguments" (typeCheck tyBase (App [Var "/", Val (Integer 10)])) 
     (fail "Could not unify (-> Integer Integer Integer) and (-> Integer Y#25)")

    test "typeOf test app with / fail too many arguments" (typeCheck tyBase (App [Var "/", Val (Integer 10), Val (Integer 5), Val (Integer 30)])) 
     (fail "Could not unify (-> Integer Integer Integer) and (-> Integer Integer Integer Y#26)")

    test "typeOf test app with / argument types did not match 1" (typeCheck tyBase (App [Var "/", Val (Boolean True), Val (Integer 5)])) 
     (fail "Could not unify Integer and Boolean")

    test "typeOf test app with / argument types did not match 2" (typeCheck tyBase (App [Var "/", Val (Integer 10), Val (Boolean False)])) 
     (fail "Could not unify Integer and Boolean")

    -- Not Tests

    test "typeOf test app with not success" (typeCheck tyBase (App [Var "not", Val (Boolean False)])) (Success (T.TyBase T.TyBoolean))

    test "typeOf test app with not fail not enough arguments" (typeCheck tyBase (App [Var "not"])) 
     (fail "Could not unify (-> Boolean Boolean) and (-> Y#28)")

    test "typeOf test app with not fail too many arguments" (typeCheck tyBase (App [Var "not", Val (Boolean True), Val (Boolean False)])) 
     (fail "Could not unify (-> Boolean Boolean) and (-> Boolean Boolean Y#29)")

    test "typeOf test app with not argument types did not match" (typeCheck tyBase (App [Var "not", Val (Float 5.5)]))
     (fail "Could not unify Boolean and Real")

    -- < Tests

    test "typeOf test app with < success" (typeCheck tyBase (App [Var "<", Val (Integer 10),Val (Integer 20)])) (Success (T.TyBase T.TyBoolean))

    test "typeOf test app with < fail not enough arguments" (typeCheck tyBase (App [Var "<", Val (Integer 10)])) 
     (fail "Could not unify (-> Integer Integer Boolean) and (-> Integer Y#31)")

    test "typeOf test app with < fail too many arguments" (typeCheck tyBase (App [Var "<", Val (Integer 10), Val (Integer 5), Val (Integer 30)])) 
     (fail "Could not unify (-> Integer Integer Boolean) and (-> Integer Integer Integer Y#32)")

    test "typeOf test app with < argument types did not match 1" (typeCheck tyBase (App [Var "<", Val (Boolean True), Val (Integer 5)])) 
     (fail "Could not unify Integer and Boolean")

    test "typeOf test app with < argument types did not match 2" (typeCheck tyBase (App [Var "<", Val (Integer 10), Val (Boolean False)])) 
     (fail "Could not unify Integer and Boolean")

    -- > Tests

    test "typeOf test app with > success" (typeCheck tyBase (App [Var ">", Val (Integer 10),Val (Integer 20)])) (Success (T.TyBase T.TyBoolean))

    test "typeOf test app with > fail not enough arguments" (typeCheck tyBase (App [Var ">", Val (Integer 10)])) 
     (fail "Could not unify (-> Integer Integer Boolean) and (-> Integer Y#34)")

    test "typeOf test app with > fail too many arguments" (typeCheck tyBase (App [Var ">", Val (Integer 10), Val (Integer 5), Val (Integer 30)])) 
     (fail "Could not unify (-> Integer Integer Boolean) and (-> Integer Integer Integer Y#35)")

    test "typeOf test app with > argument types did not match 1" (typeCheck tyBase (App [Var ">", Val (Boolean True), Val (Integer 5)])) 
     (fail "Could not unify Integer and Boolean")

    test "typeOf test app with > argument types did not match 2" (typeCheck tyBase (App [Var ">", Val (Integer 10), Val (Boolean False)])) 
     (fail "Could not unify Integer and Boolean")

    -- = Tests

    test "typeOf test app with = success" (typeCheck tyBase (App [Var "=", Val (Integer 10),Val (Integer 20)])) (Success (T.TyBase T.TyBoolean))

    test "typeOf test app with = fail not enough arguments" (typeCheck tyBase (App [Var "=", Val (Integer 10)])) 
     (fail "Could not unify (-> Integer Integer Boolean) and (-> Integer Y#37)")

    test "typeOf test app with = fail too many arguments" (typeCheck tyBase (App [Var "=", Val (Integer 10), Val (Integer 5), Val (Integer 30)])) 
     (fail "Could not unify (-> Integer Integer Boolean) and (-> Integer Integer Integer Y#38)")

    test "typeOf test app with = argument types did not match 1" (typeCheck tyBase (App [Var "=", Val (Boolean True), Val (Integer 5)])) 
     (fail "Could not unify Integer and Boolean")

    test "typeOf test app with = argument types did not match 2" (typeCheck tyBase (App [Var "=", Val (Integer 10), Val (Boolean False)])) 
     (fail "Could not unify Integer and Boolean")

    -- <= Tests

    test "typeOf test app with <= success" (typeCheck tyBase (App [Var "=", Val (Integer 10),Val (Integer 20)])) (Success (T.TyBase T.TyBoolean))

    test "typeOf test app with <= fail not enough arguments" (typeCheck tyBase (App [Var "=", Val (Integer 10)])) 
     (fail "Could not unify (-> Integer Integer Boolean) and (-> Integer Y#40)")

    test "typeOf test app with <= fail too many arguments" (typeCheck tyBase (App [Var "=", Val (Integer 10), Val (Integer 5), Val (Integer 30)])) 
     (fail "Could not unify (-> Integer Integer Boolean) and (-> Integer Integer Integer Y#41)")

    test "typeOf test app with <= argument types did not match 1" (typeCheck tyBase (App [Var "=", Val (Boolean True), Val (Integer 5)])) 
     (fail "Could not unify Integer and Boolean")

    test "typeOf test app with <= argument types did not match 2" (typeCheck tyBase (App [Var "=", Val (Integer 10), Val (Boolean False)])) 
     (fail "Could not unify Integer and Boolean")

    -- >= Tests

    test "typeOf test app with >= success" (typeCheck tyBase (App [Var "=", Val (Integer 10),Val (Integer 20)])) (Success (T.TyBase T.TyBoolean))

    test "typeOf test app with >= fail not enough arguments" (typeCheck tyBase (App [Var "=", Val (Integer 10)])) 
     (fail "Could not unify (-> Integer Integer Boolean) and (-> Integer Y#43)")

    test "typeOf test app with >= fail too many arguments" (typeCheck tyBase (App [Var "=", Val (Integer 10), Val (Integer 5), Val (Integer 30)])) 
     (fail "Could not unify (-> Integer Integer Boolean) and (-> Integer Integer Integer Y#44)")

    test "typeOf test app with >= argument types did not match 1" (typeCheck tyBase (App [Var "=", Val (Boolean True), Val (Integer 5)])) 
     (fail "Could not unify Integer and Boolean")

    test "typeOf test app with >= argument types did not match 2" (typeCheck tyBase (App [Var "=", Val (Integer 10), Val (Boolean False)])) 
     (fail "Could not unify Integer and Boolean")

    -- Lambda tests 
    
    test "typeOf test lambda: simple 1" (typeCheck tyBase (Lambda ["x"] (Var "x")))  
     (Success (T.TyArrow [T.TyVar "X#45", T.TyVar "X#45"]))

    test "typeOf test lambda: simple 2" (typeCheck tyBase (Lambda ["x", "y"] (Var "x"))) 
     (Success (T.TyArrow [T.TyVar "X#46", T.TyVar "X#47", T.TyVar "X#46"]))

    test "typeOf test lambda with app 1" (typeCheck tyBase (App [Lambda ["x" ] (Var "x"), Val (Boolean False)])) 
     (Success (T.TyBase T.TyBoolean))

    test "typeOf test lambda with app 2" (typeCheck tyBase (App 
     [Lambda ["x", "y"] (App [Var "+", Var "x", Var "y"]) , Val (Integer 10), Val (Integer 15)])) 
     (Success (T.TyBase T.TyInteger))

    test "typeOf test lambda with app too few args 1" (typeCheck tyBase (App [Lambda ["x"] (Var "x")])) 
     (fail "Could not unify (-> X#54 X#54) and (-> Y#55)")

    test "typeOf test lambda with app too few args 2" (typeCheck tyBase (App 
     [Lambda ["x", "y"] (App [Var "+", Var "x", Var "y"]) , Val (Integer 15)])) 
     (fail "Could not unify (-> X#56 X#57 Y#58) and (-> Integer Y#59)")

    test "typeOf test lambda with app too many args" (typeCheck tyBase (App 
     [Lambda ["x", "y" ] (App [Var "+", Var "x", Var "y"]) , Val (Integer 15), Val (Integer 20), Val (Integer 22)])) 
     (fail "Could not unify (-> X#60 X#61 Y#62) and (-> Integer Integer Integer Y#63)") 

    test "typeOf test lambda with app types do not match 1" (typeCheck tyBase (App 
     [Lambda ["x", "y"] (App [Var "+", Var "x", Var "y"]) , Val (Float 5.5), Val (Integer 15)])) 
     (fail "Could not unify Integer and Real") 

    test "typeOf test lambda with app types do not match 2" (typeCheck tyBase (App 
      [Lambda ["x", "y"] (App [Var "+", Var "x", Var "y"]) , Val (Integer 5), Val (Boolean False)])) 
      (fail "Could not unify Integer and Boolean")  

     -- Tests for List Exprs 

    -- test "typeOf test nil" (typeOf tyBase Nil) (Success )  
    
    -- test "typeOf test cons all same type 1" (typeOf tyBase (Cons (Val $ Integer 10) Nil)) 
    --  (Success $ TyList (TyBase TyInteger))

    -- test "typeOf test cons all same type 2" (typeOf tyBase (Cons (Val $ Float 6) (Cons (Val $ Float 5.5) Nil)))
    --  (Success $ TyList (TyBase TyReal))

    -- test "typeOf test cons not all same type 1" (typeOf tyBase (Cons (Val $ Integer 10) Nil)) 
    --  (fail "Cons list has inconsistent types")

    -- test "typeOf test cons not all same type 2" (typeOf tyBase (Cons (Val $ Float 6) (Cons (Val $ Boolean True) Nil)))
    --  (fail "Cons list has inconsistent types")

    -- test "typeOf test cons inner element fails" (typeOf tyBase (Cons (App [Var "+", Val $ Float 5.5, Val $ Boolean False]) Nil))
    --  (fail "Cons failed because of inner element error: App argument types do not match.") 

    -- test "typeOf test list? succeeds" (typeOf tyBase (List_Pred (Cons (Val $ Integer 10) Nil)))
    --  (Success $ TyBase TyBoolean)

    -- test "typeOf test list? fails" (typeOf tyBase (List_Pred (Cons (Val $ Integer 10) Nil)))
    --  (fail "List_Pred failed because: Cons list has inconsistent types")  

    -- test "typeOf test cons? succeeds" (typeOf tyBase (Cons_Pred (Cons (Val $ Integer 10) Nil)))
    --  (Success $ TyBase TyBoolean)

    -- test "typeOf test cons? fails" (typeOf tyBase (Cons_Pred (Cons (Val $ Integer 10) Nil)))
    --  (fail "Cons_Pred failed because: Cons list has inconsistent types")   

    -- test "typeOf test nil? succeeds" (typeOf tyBase (Nil_Pred (Cons (Val $ Integer 10) Nil )))
    --  (Success $ TyBase TyBoolean)

    -- test "typeOf test nil? fails" (typeOf tyBase (Nil_Pred (Cons (Val $ Integer 10) Nil )))
    --  (fail "Nil_Pred failed because: Cons list has inconsistent types")  

    -- test "typeOf test head succeeds" (typeOf tyBase (Head (Cons (Val $ Integer 10) Nil)))
    --  (Success $ TyBase TyInteger)

    -- test "typeOf test head fails because expr it is called on fails" (typeOf tyBase (Head (Cons (Val $ Integer 10) Nil)))
    --  (fail "Head failed because: Cons list has inconsistent types")  

    -- test "typeOf test head fails because expr it is called on is not a cons" (typeOf tyBase (Head (Val $ Integer 50))) 
    --  (fail "Head not called on list.")

    -- test "typeOf test tail succeeds" (typeOf tyBase (Tail (Cons (Val $ Integer 10) Nil )))
    --  (Success $ TyList $ TyBase TyInteger)

    -- test "typeOf test tail fails because expr it is called on fails" (typeOf tyBase (Tail (Cons (Val $ Integer 10) Nil)))
    --  (fail "Tail failed because: Cons list has inconsistent types")  

    -- test "typeOf test tail fails because expr it is called on is not a cons" (typeOf tyBase (Tail (Val $ Integer 50))) 
    --  (fail "Tail not called on list.") 
   


-- ==============================================================================================================

-- Helper function for easily running example files as tests for the typeOfProgramSExpr function
typeOfProgramSExprHelper :: (Result [S.Expr]) -> [S.Expr]
typeOfProgramSExprHelper (Success x)= x 
-- this should never happen
typeOfProgramSExprHelper (Failure f) = []


{-
(x : Boolean)
(define x 12)
(f : (-> Boolean Integer))
(defun f (x) (+ x 1))
(g : (-> Integer Boolean))
(defun g (x) (+ x 1))
-}

sexpr_ex_incorrect_function_def_1 = 
     [S.List [S.Symbol "x", S.Symbol ":", S.Symbol "Boolean"], 
            S.List[S.Symbol "define", S.Symbol "x", S.Integer 12],
            S.Symbol "x"]

sexpr_ex_incorrect_function_def_2 = 
     [S.List [S.Symbol "f", S.Symbol ":", S.List[S.Symbol "->", S.Symbol "Boolean", S.Symbol "Integer"]], 
            S.List[S.Symbol "defun", S.Symbol "f", S.List[S.Symbol "x"], S.List[S.Symbol "+", S.Symbol "x", S.Integer 1]],
            S.Integer 10]

sexpr_ex_incorrect_function_def_3 = 
     [S.List [S.Symbol "g", S.Symbol ":", S.List[S.Symbol "->", S.Symbol "Integer", S.Symbol "Boolean"]], 
            S.List[S.Symbol "defun", S.Symbol "f", S.List[S.Symbol "x"], S.List[S.Symbol "+", S.Symbol "x", S.Integer 1]],
            S.Integer 10]        

sexpr_ex_incorrect_signature = 
     [S.List [S.Symbol "h", S.Symbol ":", S.List[S.Symbol "->", S.Symbol "Integer", S.Symbol "real"]], 
            S.List[S.Symbol "defun", S.Symbol "h", S.List[S.Symbol "x"], S.List[S.Symbol "+", S.Symbol "x", S.Integer 1]],
            S.Integer 10]    

sexpr_ex_function_body_undefined_variable = 
     [S.List [S.Symbol "l", S.Symbol ":", S.List[S.Symbol "->", S.Symbol "Integer", S.Symbol "real"]], 
            S.List[S.Symbol "defun", S.Symbol "l", S.List[S.Symbol "x"], S.List[S.Symbol "+", S.Symbol "y", S.Integer 1]],
            S.Integer 10]                    



--tests runProgram
test_typeOfProgramSExpr = do 
     test "typeOfProgramSExpr 1" (typeOfProgramSExpr (typeOfProgramSExprHelper (unsafePerformIO (fromFile "example1.pss")))) 
      (Success $ S.List [S.Symbol "Pair-of", S.Symbol "Boolean", S.Symbol "Boolean"])

     test "typeOfProgramSExpr 2" (typeOfProgramSExpr (typeOfProgramSExprHelper (unsafePerformIO (fromFile "example2.pss")))) 
      (Success $ S.Symbol "Integer")

     test "typeOfProgramSExpr 3" (typeOfProgramSExpr (typeOfProgramSExprHelper (unsafePerformIO (fromFile "example3.pss")))) 
      (Success $ S.Symbol "Integer")

     test "typeOfProgramSExpr 4" (typeOfProgramSExpr (typeOfProgramSExprHelper (unsafePerformIO (fromFile "example4.pss")))) 
      (Success $ S.List [S.Symbol "Pair-of", S.List [S.Symbol "->", S.Symbol "Integer", S.Symbol "Boolean"], 
                                             S.List [S.Symbol "->", S.Symbol "Boolean", S.Symbol "Integer"]])

     test "typeOfProgramSExpr 5" (typeOfProgramSExpr (typeOfProgramSExprHelper (unsafePerformIO (fromFile "example5.pss")))) 
      (Success (S.List [S.Symbol "Pair-of", S.Symbol "Integer", S.Symbol "Integer"]))

     test "typeOfProgramSExpr 6" (typeOfProgramSExpr (typeOfProgramSExprHelper (unsafePerformIO (fromFile "example6.pss")))) 
      (Success (S.List [S.Symbol "Pair-of", S.Symbol "Integer", S.Symbol "Integer"]))                                                                             
                 
     test "typeOfProgramSExpr function defs dont match 1" (typeOfProgramSExpr sexpr_ex_incorrect_function_def_1) 
      (fail "Function or variable x actual type is not the same as the expected type.")

     test "typeOfProgramSExpr function defs dont match 2" (typeOfProgramSExpr sexpr_ex_incorrect_function_def_2) 
      (fail "Possible function or variable f with incorrect type: Argument types do not match.")

     test "typeOfProgramSExpr function defs dont match 3" (typeOfProgramSExpr sexpr_ex_incorrect_function_def_3) 
      (fail "Function or variable g actual type is not the same as the expected type.")  

     test "typeOfProgramSExpr function with signature that cant be parsed" (typeOfProgramSExpr sexpr_ex_incorrect_signature) 
      (fail "Given s-expression cannot be parsed as a type")   

     test "typeOfProgramSExpr function body has undefined variable" (typeOfProgramSExpr sexpr_ex_function_body_undefined_variable) 
      (fail "Given s-expression cannot be parsed as a type")   

ex1 :: Expr
ex1 = (Lambda ["x"] (Var "x"))

ex2:: Expr
ex2 = (Lambda ["x", "y"] (Var "x"))

ex3 = (App [Lambda ["x" ] (Var "x"), Val (Boolean False)])

ex4 = (App [Lambda ["x", "y"] (App [Var "+", Var "x", Var "y"]) , Val (Boolean True), Val (Integer 15)])



 