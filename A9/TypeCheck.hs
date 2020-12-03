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
typeOf tenv (Let x e1 e2) = do 
    ty1 <- typeOf tenv e1 
    typeOf (set tenv x ty1) e2    
typeOf tenv (Pair e1 e2) = do
    ty1 <- typeOf tenv e1
    ty2 <- typeOf tenv e2
    return $ TyPair ty1 ty2
typeOf tenv (Left e) = do 
    ty <- typeOf tenv e
    case ty of 
        TyPair ty1 _ -> return ty1
        _ -> fail "Left was not called on a pair."
typeOf tenv (Right e) = do
    ty <- typeOf tenv e
    case ty of 
        TyPair _ ty2 -> return ty2
        _ -> fail "Right was not called on a pair."     
typeOf tenv (Lambda sigs e) = do
    -- make env with all of the signature variables and get the type of the body.
    ty' <- typeOf (addSigTypesToEnv tenv sigs) e
    -- append the type of the body as the return type for the tyArrow with the sig type list as the args. 
    return $ TyArrow (convertSigsToTypeList sigs ++ [ty'])
    where 
        -- Takes a list of signatures and converts it to a list of types from the signatures.
        convertSigsToTypeList :: [Signature] -> [Type]
        convertSigsToTypeList [] = []
        convertSigsToTypeList ((Sig _ t):xs) = t: convertSigsToTypeList xs

        -- Takes a type env and a list of signatures and applies all of the signatures as variables in the type env. 
        addSigTypesToEnv :: TyEnv -> [Signature] -> TyEnv
        addSigTypesToEnv tenv [] = tenv
        addSigTypesToEnv tenv ((Sig x t):xs)  = addSigTypesToEnv (set tenv x t) xs
typeOf tenv (App (func:argList)) = do 
    TyArrow arrowList <- typeOf tenv func
    confirmAppArgumentTypes tenv (init arrowList) argList (last arrowList) 
    where 
        -- Looks at the expected types of an app (all in list except final type aka the init) 
        -- and compares the types of them to the given arguments (the argList) and also pass on the last
        -- type from to then return if success (because the final element in an tyArrow is the return type). 
        confirmAppArgumentTypes :: TyEnv -> [Type] -> [Expr] -> Type -> Result Type
        confirmAppArgumentTypes _ [] [] resultType = return resultType 
        confirmAppArgumentTypes _ [] _ _ = fail "App was given too many arguments."
        confirmAppArgumentTypes _ _ [] _ = fail "App was given too few arguments."
        confirmAppArgumentTypes tenv (x:xs) (y:ys) resultType = do 
            y' <- typeOf tenv y
            if x == y' 
                then confirmAppArgumentTypes tenv xs ys resultType
                else fail "Argument types do not match."
typeOf tenv (If e1 e2 e3) = do
    ty1 <- typeOf tenv e1
    case ty1 of 
        TyBase TyBoolean -> do
            ty2 <- typeOf tenv e2
            ty3 <- typeOf tenv e3
            if ty2 == ty3
                then return ty2
                else fail "Incompatible return types for If"
        _ -> fail "First argument in If was not of type TyBoolean."       
typeOf tenv (And e1 e2) = do 
    ty1 <- typeOf tenv e1 
    ty2 <- typeOf tenv e2
    case ty1 of 
        TyBase TyBoolean -> case ty2 of 
                                TyBase TyBoolean -> return (TyBase TyBoolean)
                                _ -> fail "Second argument in And was not of type TyBoolean." 
        _ -> fail "First argument in And was not of type TyBoolean."                         
typeOf tenv (Or e1 e2) = do 
    ty1 <- typeOf tenv e1 
    ty2 <- typeOf tenv e2
    case ty1 of 
        TyBase TyBoolean -> case ty2 of 
                                TyBase TyBoolean -> return (TyBase TyBoolean)
                                _ -> fail "Second argument in Or was not of type TyBoolean." 
        _ -> fail "First argument in Or was not of type TyBoolean."          
typeOf tenv (Cond [] e3) = do
    case e3 of 
        Nothing -> fail "Cond has no return type."
        Just x ->  typeOf tenv x
typeOf tenv (Cond ((e1, e2) : xs) e3) = do 
    ty1 <- typeOf tenv e1 
    ty2 <- typeOf tenv e2
    case ty1 of 
        TyBase TyBoolean -> 
            case typeOfCondList tenv xs ty2 of 
                Failure f -> Failure f 
                s -> case e3 of  
                        Nothing -> return ty2
                        Just e3' -> if (Success ty2 == s) && (s == typeOf tenv e3')
                                        then return ty2
                                        else fail "Incompatible return types for Cond."
        _ -> fail "Cond clause was not of type TyBoolean."                                     
        where 
            -- ensures that the whole cond list has a boolean clause and the same
            -- expr type for the e2 of each pairing and if so then return that type. 
            typeOfCondList :: TyEnv -> [(Expr, Expr)] -> Type -> Result Type
            typeOfCondList _ [] t = Success t
            typeOfCondList tenv ((e1, e2) : xs) t = do
                ty1 <- typeOf tenv e1 
                case ty1 of 
                    TyBase TyBoolean -> do 
                        ty2 <- typeOf tenv e2 
                        if ty2 == t 
                            then typeOfCondList tenv xs t 
                            else fail "Cond doesnt have the same return types."
                    _ -> fail "Cond clause was not of type TyBoolean."        
typeOf _ _ = fail "Given incompatible expr."

-- |Compute the type of the given program, relative to the given type environment
typeOfProgram :: TyEnv -> Program -> Result Type
typeOfProgram _ _ = undefined -- TODO: complete

-- |Compute the 
typeOfProgramSExpr :: [S.Expr] -> Result S.Expr
typeOfProgramSExpr sexprs = do
    program <- programFromSExpression (S.List [S.Symbol "Program", S.List sexprs])
    typ <- typeOfProgram tyBase program
    return $ Types.toSExpression typ



-- =====================================================================================================================


integerToIntegerIsInteger = Types.TyArrow [Types.TyBase Types.TyInteger, Types.TyBase Types.TyInteger, Types.TyBase Types.TyInteger]
integerToIntegerIsBoolean = Types.TyArrow [Types.TyBase Types.TyInteger, Types.TyBase Types.TyInteger, Types.TyBase Types.TyBoolean]

booleanIsBoolean = Types.TyArrow [Types.TyBase Types.TyBoolean, Types.TyBase Types.TyBoolean]

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


-- =================================================================================================================
test_typeOf = do 

    -- Basic Tests 
    test "typeOf test integer" (typeOf tyBase (Val (Integer 2))) (Success $ TyBase TyInteger)

    test "typeOf test real" (typeOf tyBase (Val (Float 2.5))) (Success $ TyBase TyReal)

    test "typeOf test boolean" (typeOf tyBase (Val (Boolean True))) (Success $ TyBase TyBoolean)

    test "typeOf test undefined var" (typeOf tyBase (Var "x")) (fail "Variable x is not defined")

    test "typeOf test defined var" (typeOf (set empty "x" (TyBase TyInteger)) (Var "x")) (Success $ TyBase TyInteger)

    test "typeOf test let" (typeOf tyBase (Let "x" (Val (Integer 20)) (Var "x"))) (Success $ TyBase TyInteger)

    test "typeOf test pair" (typeOf tyBase (Pair (Val (Integer 10)) (Val (Float 4.1)))) (Success $ TyPair (TyBase TyInteger) (TyBase TyReal))

    test "typeOf test left on pair" (typeOf tyBase (Left (Pair (Val (Integer 10)) (Val (Float 4.1))))) (Success $ TyBase TyInteger)

    test "typeOf test left not on pair" (typeOf tyBase (Left (Val (Integer 10)))) (Failure "Left was not called on a pair.")

    test "typeOf test right on pair" (typeOf tyBase (Right (Pair (Val (Integer 10)) (Val (Float 4.1))))) (Success $ TyBase TyReal)

    test "typeOf test right not on pair" (typeOf tyBase (Right (Val (Float 4.1)))) (Failure "Right was not called on a pair.")

     -- And tests 
    test "typeof test and success" (typeOf tyBase (And (Val (Boolean True)) (Val (Boolean True)))) (Success $ TyBase TyBoolean)

    test "typeOf test and fail 1" (typeOf tyBase (And (Val (Boolean True)) (Val (Integer 10)))) (fail "Second argument in And was not of type TyBoolean.")

    test "typeOf test and fail 2" (typeOf tyBase (And (Val (Integer 10)) (Val (Boolean True)))) (fail "First argument in And was not of type TyBoolean.")
    
    -- Or tests
    test "typeof test or success" (typeOf tyBase (Or (Val (Boolean True)) (Val (Boolean True)))) (Success $ TyBase TyBoolean)

    test "typeOf test or fail 1" (typeOf tyBase (Or (Val (Boolean True)) (Val (Integer 10)))) (fail "Second argument in Or was not of type TyBoolean.")

    test "typeOf test or fail 2" (typeOf tyBase (Or (Val (Integer 10)) (Val (Boolean True)))) (fail "First argument in Or was not of type TyBoolean.")
    
    -- If tests
    test "typeOf test if success" (typeOf tyBase (If (Val (Boolean False)) (Val (Integer 10)) (Val (Integer 11)))) (Success $ TyBase TyInteger)

    test "typeOf test if fail 1" (typeOf tyBase (If (Val (Integer 9)) (Val (Integer 10)) (Val (Integer 11)))) (fail "First argument in If was not of type TyBoolean." )   

    test "typeOf test if fail 2" (typeOf tyBase (If (Val (Boolean True)) (Val (Integer 10)) (Val (Boolean False)))) (fail "Incompatible return types for If")  

    test "typeOf test if fail 2" (typeOf tyBase (If (Val (Boolean True)) (Val (Integer 10)) (Val (Boolean False)))) (fail "Incompatible return types for If") 

    --  Cond Tests
    test "typeOf test Cond success 1" (typeOf tyBase ( Cond [(Val (Boolean True), 
     App [Var "+", Val (Integer 5), Val (Integer 2)])]  Nothing))
       (Success $ TyBase TyInteger)

    test "typeOf test Cond success 2" (typeOf tyBase ( Cond [(Val (Boolean False), 
     App [Var "+", Val (Integer 5), Val (Integer 2)]), 
        (Val (Boolean True), App [Var "/", Val (Integer 4), Val (Integer 2)])] Nothing))
       (Success $ TyBase TyInteger)

    test "typeOf Cond first clause isnt boolean" (typeOf tyBase ( Cond [(Val (Integer 10), 
     App [Var "+", Val (Integer 5), Val (Integer 2)]), 
        (Val (Boolean False), App [Var "/", Val (Integer 4), Val (Integer 2)])]
         (Just (App [Var "-", Val (Integer 5), Val (Integer 2)]))))
       (fail "Cond clause was not of type TyBoolean.")   

    test "typeOf Cond non first clause isnt boolean" (typeOf tyBase (Cond [(Val (Boolean False), 
     App [Var "+", Val (Integer 5), Val (Integer 2)]), 
        (Val (Float 20), App [Var "/", Val (Integer 4), Val (Integer 2)])]
         (Just (App [Var "-", Val (Integer 5), Val (Integer 2)]))))
       (fail "Cond clause was not of type TyBoolean.")     

    test "typeOf Cond with else that is not of the same type" (typeOf tyBase ( Cond [(Val (Boolean False), 
     App [Var "+", Val (Integer 5), Val (Integer 2)]), 
        (Val (Boolean True), App [Var "/", Val (Integer 4), Val (Integer 2)])]
         (Just (App [Var "not", Val (Boolean False)]))))
       (fail "Incompatible return types for Cond.")

    test "eval Cond with else that is the same return type" (typeOf tyBase (Cond [(Val (Boolean False), 
     App [Var "+", Val (Integer 5), Val (Integer 2)]), 
        (Val (Boolean False), Val (Integer 10))]
         (Just (App [Var "-", Val (Integer 5), Val (Integer 2)]))))
       (Success $ TyBase TyInteger)

    test "eval Cond with else that has expressions in list of different type" (typeOf tyBase (Cond [(Val (Boolean False), 
     App [Var "+", Val (Integer 5), Val (Integer 2)]), 
        (Val (Boolean False), Val (Float 10.5))]
         (Just (App [Var "-", Val (Integer 5), Val (Integer 2)]))))
       (fail "Cond doesnt have the same return types.")   
       

    -- Add Tests

    test "typeOf test app with + success" (typeOf tyBase (App [Var "+", Val (Integer 10),Val (Integer 20)])) (Success $ TyBase TyInteger)

    test "typeOf test app with + fail not enough arguments" (typeOf tyBase (App [Var "+", Val (Integer 10)])) (fail "App was given too few arguments.")

    test "typeOf test app with + fail too many arguments" (typeOf tyBase (App [Var "+", Val (Integer 10), Val (Integer 5), Val (Integer 30)])) (fail "App was given too many arguments.")

    test "typeOf test app with + argument types did not match 1" (typeOf tyBase (App [Var "+", Val (Boolean True), Val (Integer 5), Val (Integer 30)])) (fail "Argument types do not match.")

    test "typeOf test app with + argument types did not match 2" (typeOf tyBase (App [Var "+", Val (Integer 10), Val (Boolean False), Val (Integer 30)])) (fail "Argument types do not match.")

    -- Sub Tests

    test "typeOf test app with - success" (typeOf tyBase (App [Var "-", Val (Integer 10),Val (Integer 20)])) (Success $ TyBase TyInteger)

    test "typeOf test app with - fail not enough arguments" (typeOf tyBase (App [Var "-", Val (Integer 10)])) (fail "App was given too few arguments.")

    test "typeOf test app with - fail too many arguments" (typeOf tyBase (App [Var "-", Val (Integer 10), Val (Integer 5), Val (Integer 30)])) (fail "App was given too many arguments.")

    test "typeOf test app with - argument types did not match 1" (typeOf tyBase (App [Var "-", Val (Boolean True), Val (Integer 5), Val (Integer 30)])) (fail "Argument types do not match.")

    test "typeOf test app with - argument types did not match 2" (typeOf tyBase (App [Var "-", Val (Integer 10), Val (Boolean False), Val (Integer 30)])) (fail "Argument types do not match.")

    -- Mul Tests

    test "typeOf test app with * success" (typeOf tyBase (App [Var "*", Val (Integer 10),Val (Integer 20)])) (Success $ TyBase TyInteger)

    test "typeOf test app with * fail not enough arguments" (typeOf tyBase (App [Var "*", Val (Integer 10)])) (fail "App was given too few arguments.")

    test "typeOf test app with * fail too many arguments" (typeOf tyBase (App [Var "*", Val (Integer 10), Val (Integer 5), Val (Integer 30)])) (fail "App was given too many arguments.")

    test "typeOf test app with * argument types did not match 1" (typeOf tyBase (App [Var "*", Val (Boolean True), Val (Integer 5), Val (Integer 30)])) (fail "Argument types do not match.")

    test "typeOf test app with * argument types did not match 2" (typeOf tyBase (App [Var "*", Val (Integer 10), Val (Boolean False), Val (Integer 30)])) (fail "Argument types do not match.")

    -- Div Tests

    test "typeOf test app with / success" (typeOf tyBase (App [Var "/", Val (Integer 10),Val (Integer 20)])) (Success $ TyBase TyInteger)

    test "typeOf test app with / fail not enough arguments" (typeOf tyBase (App [Var "/", Val (Integer 10)])) (fail "App was given too few arguments.")

    test "typeOf test app with / fail too many arguments" (typeOf tyBase (App [Var "/", Val (Integer 10), Val (Integer 5), Val (Integer 30)])) (fail "App was given too many arguments.")

    test "typeOf test app with / argument types did not match 1" (typeOf tyBase (App [Var "/", Val (Boolean True), Val (Integer 5)])) (fail "Argument types do not match.")

    test "typeOf test app with / argument types did not match 2" (typeOf tyBase (App [Var "/", Val (Integer 10), Val (Boolean False)])) (fail "Argument types do not match.")

    -- Not Tests

    test "typeOf test app with not success" (typeOf tyBase (App [Var "not", Val (Boolean False)])) (Success $ TyBase TyBoolean)

    test "typeOf test app with not fail not enough arguments" (typeOf tyBase (App [Var "not"])) (fail "App was given too few arguments.")

    test "typeOf test app with not fail too many arguments" (typeOf tyBase (App [Var "not", Val (Boolean True), Val (Boolean False)])) (fail "App was given too many arguments.")

    test "typeOf test app with not argument types did not match" (typeOf tyBase (App [Var "not", Val (Float 5.5)])) (fail "Argument types do not match.")

    -- < Tests

    test "typeOf test app with < success" (typeOf tyBase (App [Var "<", Val (Integer 10),Val (Integer 20)])) (Success $ TyBase TyBoolean)

    test "typeOf test app with < fail not enough arguments" (typeOf tyBase (App [Var "<", Val (Integer 10)])) (fail "App was given too few arguments.")

    test "typeOf test app with < fail too many arguments" (typeOf tyBase (App [Var "<", Val (Integer 10), Val (Integer 5), Val (Integer 30)])) (fail "App was given too many arguments.")

    test "typeOf test app with < argument types did not match 1" (typeOf tyBase (App [Var "<", Val (Boolean True), Val (Integer 5)])) (fail "Argument types do not match.")

    test "typeOf test app with < argument types did not match 2" (typeOf tyBase (App [Var "<", Val (Integer 10), Val (Boolean False)])) (fail "Argument types do not match.")

    -- > Tests

    test "typeOf test app with > success" (typeOf tyBase (App [Var ">", Val (Integer 10),Val (Integer 20)])) (Success $ TyBase TyBoolean)

    test "typeOf test app with > fail not enough arguments" (typeOf tyBase (App [Var ">", Val (Integer 10)])) (fail "App was given too few arguments.")

    test "typeOf test app with > fail too many arguments" (typeOf tyBase (App [Var ">", Val (Integer 10), Val (Integer 5), Val (Integer 30)])) (fail "App was given too many arguments.")

    test "typeOf test app with > argument types did not match 1" (typeOf tyBase (App [Var ">", Val (Boolean True), Val (Integer 5)])) (fail "Argument types do not match.")

    test "typeOf test app with > argument types did not match 2" (typeOf tyBase (App [Var ">", Val (Integer 10), Val (Boolean False)])) (fail "Argument types do not match.")

    -- = Tests

    test "typeOf test app with = success" (typeOf tyBase (App [Var "=", Val (Integer 10),Val (Integer 20)])) (Success $ TyBase TyBoolean)

    test "typeOf test app with = fail not enough arguments" (typeOf tyBase (App [Var "=", Val (Integer 10)])) (fail "App was given too few arguments.")

    test "typeOf test app with = fail too many arguments" (typeOf tyBase (App [Var "=", Val (Integer 10), Val (Integer 5), Val (Integer 30)])) (fail "App was given too many arguments.")

    test "typeOf test app with = argument types did not match 1" (typeOf tyBase (App [Var "=", Val (Boolean True), Val (Integer 5)])) (fail "Argument types do not match.")

    test "typeOf test app with = argument types did not match 2" (typeOf tyBase (App [Var "=", Val (Integer 10), Val (Boolean False)])) (fail "Argument types do not match.")

    -- <= Tests

    test "typeOf test app with <= success" (typeOf tyBase (App [Var "=", Val (Integer 10),Val (Integer 20)])) (Success $ TyBase TyBoolean)

    test "typeOf test app with <= fail not enough arguments" (typeOf tyBase (App [Var "=", Val (Integer 10)])) (fail "App was given too few arguments.")

    test "typeOf test app with <= fail too many arguments" (typeOf tyBase (App [Var "=", Val (Integer 10), Val (Integer 5), Val (Integer 30)])) (fail "App was given too many arguments.")

    test "typeOf test app with <= argument types did not match 1" (typeOf tyBase (App [Var "=", Val (Boolean True), Val (Integer 5)])) (fail "Argument types do not match.")

    test "typeOf test app with <= argument types did not match 2" (typeOf tyBase (App [Var "=", Val (Integer 10), Val (Boolean False)])) (fail "Argument types do not match.")

    -- >= Tests

    test "typeOf test app with >= success" (typeOf tyBase (App [Var "=", Val (Integer 10),Val (Integer 20)])) (Success $ TyBase TyBoolean)

    test "typeOf test app with >= fail not enough arguments" (typeOf tyBase (App [Var "=", Val (Integer 10)])) (fail "App was given too few arguments.")

    test "typeOf test app with >= fail too many arguments" (typeOf tyBase (App [Var "=", Val (Integer 10), Val (Integer 5), Val (Integer 30)])) (fail "App was given too many arguments.")

    test "typeOf test app with >= argument types did not match 1" (typeOf tyBase (App [Var "=", Val (Boolean True), Val (Integer 5)])) (fail "Argument types do not match.")

    test "typeOf test app with >= argument types did not match 2" (typeOf tyBase (App [Var "=", Val (Integer 10), Val (Boolean False)])) (fail "Argument types do not match.")

    -- Lambda tests 
    
    test "typeOf test lambda: simple 1" (typeOf tyBase (Lambda [Sig "x" (TyBase TyInteger)] (Var "x")))  
     (Success $ TyArrow [TyBase TyInteger,TyBase TyInteger])

    test "typeOf test lambda: simple 2" (typeOf tyBase (Lambda [Sig "x" (TyBase TyInteger), Sig "y" (TyBase TyInteger)] (Var "x"))) 
     (Success $ TyArrow [TyBase TyInteger, TyBase TyInteger, TyBase TyInteger])

    test "typeOf test lambda with app 1" (typeOf tyBase (App [Lambda [Sig "x" (TyBase TyBoolean)] (Var "x"), Val (Boolean False)])) 
     (Success $ TyBase TyBoolean)

    test "typeOf test lambda with app 2" (typeOf tyBase (App 
     [Lambda [Sig "x" (TyBase TyInteger), Sig "y" (TyBase TyInteger)] (App [Var "+", Var "x", Var "y"]) , Val (Integer 10), Val (Integer 15)])) 
     (Success $ TyBase TyInteger) 

    test "typeOf test lambda with app too few args 1" (typeOf tyBase (App [Lambda [Sig "x" (TyBase TyBoolean)] (Var "x")])) 
     (fail "App was given too few arguments.")

    test "typeOf test lambda with app too few args 2" (typeOf tyBase (App 
     [Lambda [Sig "x" (TyBase TyInteger), Sig "y" (TyBase TyInteger)] (App [Var "+", Var "x", Var "y"]) , Val (Integer 15)])) 
     (fail "App was given too few arguments.")

    test "typeOf test lambda with app too many args" (typeOf tyBase (App 
     [Lambda [Sig "x" (TyBase TyInteger), Sig "y" (TyBase TyInteger)] (App [Var "+", Var "x", Var "y"]) , Val (Integer 15), Val (Integer 20), Val (Integer 22)])) 
     (fail "App was given too many arguments.") 

    test "typeOf test lambda with app types do not match 1" (typeOf tyBase (App 
     [Lambda [Sig "x" (TyBase TyInteger), Sig "y" (TyBase TyInteger)] (App [Var "+", Var "x", Var "y"]) , Val (Float 5.5), Val (Integer 15)])) 
     (fail "Argument types do not match.") 

    test "typeOf test lambda with app types do not match 2" (typeOf tyBase (App 
      [Lambda [Sig "x" (TyBase TyInteger), Sig "y" (TyBase TyInteger)] (App [Var "+", Var "x", Var "y"]) , Val (Integer 5), Val (Boolean False)])) 
      (fail "Argument types do not match.")  

     --test Predicates

    test "typeOf test Boolean?" (typeOf tyBase (Boolean_Pred (Val (Boolean True)))) (fail "Given incompatible expr.")
    test "typeOf test Real?" (typeOf tyBase (Real_Pred (Val (Boolean True)))) (fail "Given incompatible expr.")
    test "typeOf test Integer?" (typeOf tyBase (Integer_Pred (Val (Boolean True)))) (fail "Given incompatible expr.")
    test "typeOf test Number?" (typeOf tyBase (Number_Pred (Val (Boolean True)))) (fail "Given incompatible expr.")
    test "typeOf test Pair?" (typeOf tyBase (Pair_Pred (Val (Boolean True)))) (fail "Given incompatible expr.")

 