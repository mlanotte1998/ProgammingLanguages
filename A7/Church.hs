{- |
Module      :  Church
Description :  Church encodings of values and operations.
               Fixpoint operator.
Copyright   : (c) Ferd, 2020
              (c) <your names>

Maintainer  : f.vesely@northeastern.edu 
              <your emails>
-}


module Church where

import Lambda
import Reduce

import SimpleTestsColor (test, testSection)


-- |Abbreviation to write a lambda with multiple arguments
lam :: [Variable] -> Lambda -> Lambda
lam = flip $ foldr Lam

app :: [Lambda] -> Lambda
app es | not $ null es = foldl1 App es

test_lam_app = do
  test "lam [x, y, z] $ app [x, y, z]"
      (lam ["x", "y", "z"] $ app [Var "x", Var "y", Var "z"])
      (Lam "x" $
          Lam "y" $
              Lam "z" $
                  App (App (Var "x") (Var "y"))
                      (Var "z"))

-- |Convert a boolean to its Church encoding
toChurchBool :: Bool -> Lambda
toChurchBool False = lam ["t", "f"] $ Var "f"
toChurchBool True =  lam ["t", "f"] $ Var "t"                      

-- |Convert a boolean from its Church encoding
fromChurchBool :: Lambda -> Maybe Bool
fromChurchBool (Lam x (Lam y (Var z))) = 
    if x == z && x /= y 
        then Just True 
    else if y == z && x/= y 
        then Just False
    else 
        Nothing 
fromChurchBool _ = Nothing                 


test_bools = do 
    test "toChurchBool True" (toChurchBool True) (Lam "t" (Lam "f" (Var "t"))) 
    
    test "toChurchBool False" (toChurchBool False) (Lam "t" (Lam "f" (Var "f")))
    
    test "fromChurchBool True" (fromChurchBool (Lam "t" (Lam "f" (Var "t")))) (Just (True))

    test "fromChurchBool False" (fromChurchBool (Lam "t" (Lam "f" (Var "f")))) (Just (False))
    
    test "fromChurchBool not a boolean lambda" (fromChurchBool (Lam "f" (Lam "t" (Var "z")))) (Nothing)

    test "fromChurchBool toChurchBool True" (fromChurchBool (toChurchBool True)) (Just True)

    test "fromChurchBool toChurchBool False" (fromChurchBool (toChurchBool False)) (Just False)
    
-- |Numerals
czero :: Lambda
czero = lam ["s", "z"] $ Var "z"

cone :: Lambda
cone = lam ["s", "z"] $ App (Var "s") (Var "z")

ctwo :: Lambda
ctwo = lam ["s", "z"] $ App (Var "s") (App (Var "s") (Var "z"))

cthree :: Lambda
cthree = lam ["s", "z"] $ App (Var "s") (App (Var "s") (App (Var "s") (Var "z")))


-- |Generalized numeral: convert a given integer >= 0 to a Church numeral
toNumeral :: Integer -> Lambda
toNumeral 0 = czero 
toNumeral n = 
   case toNumeral (n - 1) of 
       (Lam "s" (Lam "z" e)) -> (Lam "s" (Lam "z" (App (Var "s") e)))

-- |Convert a normalized numeral into an integer. Return Nothing if the 
-- numeral cannot be converted.
fromNumeral :: Lambda -> Maybe Integer
fromNumeral (Lam x (Lam y e)) = fromNumeralAccumulator (Lam x (Lam y e)) 0
  where 
      fromNumeralAccumulator :: Lambda -> Integer ->  Maybe Integer
      fromNumeralAccumulator (Lam x (Lam y (Var z))) a = if x /= y && y == z 
                                                             then Just a 
                                                             else Nothing 
      fromNumeralAccumulator (Lam x (Lam y (App (Var z) e))) a = if x /=y && x == z 
                                                                    then fromNumeralAccumulator (Lam x (Lam y e)) (a + 1)
                                                                    else Nothing
      fromNumeralAccumulator _ _ = Nothing 
fromNumeral _ = Nothing                           

test_numerals = do
    test "toNumeral 0" (toNumeral 0) czero

    test "toNumeral 1" (toNumeral 1) cone 

    test "toNumeral 2" (toNumeral 2) ctwo

    test "fromNumeral 0" (fromNumeral czero) (Just 0)

    test "fromNumeral 1" (fromNumeral cone) (Just 1)

    test "fromNumeral 2" (fromNumeral ctwo) (Just 2)

    test "fromNumeral 3" (fromNumeral cthree) (Just 3)

    test "fromNumeral toNumeral 0" (fromNumeral (toNumeral 0)) (Just 0)

    test "fromNumeral toNumeral 1" (fromNumeral (toNumeral 1)) (Just 1)

    test "fromNumeral toNumeral 2" (fromNumeral (toNumeral 2)) (Just 2)
    
    test "fromNumeral bool" (fromNumeral (Lam "t" (Lam "f" (Var "t")))) Nothing


-- |Successor of a natural number
csucc :: Lambda
csucc = lam ["n", "s", "z"] $
    App (Var "s") (App (App (Var "n") (Var "s")) (Var "z"))

test_csucc = do 
    test "(csucc ~0)" (fromNumeral $ normalize $ App csucc (toNumeral 0)) (Just 1)

    test "(csucc ~1)" (fromNumeral $ normalize $ App csucc (toNumeral 1)) (Just 2)

    test "(csucc ~2)" (fromNumeral $ normalize $ App csucc (toNumeral 2)) (Just 3)

-- |Predecessor of a natural number
cpred :: Lambda
cpred = Lam "n" (Lam "f" (Lam "x" (
          App (
            App (
              App (Var "n") 
                  (Lam "g" (Lam "h" (
                    App (Var "h") (App (Var "g") (Var "f")))))) 
              (Lam "u" (Var "x"))) 
            (Lam "u" (Var "u")))))

test_cpred = do        
    test "cpred 1" (fromNumeral $ normalize $ App cpred (toNumeral 1)) (Just 0)

    test "cpred 2" (fromNumeral $ normalize $ App cpred (toNumeral 2)) (Just 1)

    test "cpred 3" (fromNumeral $ normalize $ App cpred (toNumeral 3)) (Just 2)

    test "cpred 0" (fromNumeral $ normalize $ App cpred (toNumeral 0)) (Just 0)

-- |Addition on naturals
cplus :: Lambda
cplus = lam ["m", "n"] $ Var "m" `App` csucc `App` Var "n"

-- some examples of cplus 
-- notation: I use ~n for Church numeral corresponding to n
test_cplus = do
    test "(cplus ~3 ~4)"
        (fromNumeral (normalize (App (App cplus (toNumeral 3)) (toNumeral 4))))
        (Just 7)
    test "(cplus ~0 ~5)"
        (fromNumeral (normalize (App (App cplus (toNumeral 0)) (toNumeral 5))))
        (Just 5)
    test "(cplus ~1 ~1)"
        (fromNumeral (normalize (App (App cplus (toNumeral 1)) (toNumeral 1))))
        (Just 2)

-- |Subtraction on naturals
cminus :: Lambda
cminus = lam ["m", "n"] $ Var "m" `App` cpred `App` Var "n"             

test_cminus = do 
    test "(cminus ~4 ~3)"
        (fromNumeral (normalize (App (App cminus (toNumeral 3)) (toNumeral 4))))
        (Just 1)
    test "(cminus ~5 ~0)"
        (fromNumeral (normalize (App (App cminus (toNumeral 0)) (toNumeral 5))))
        (Just 5)
    test "(cminus ~1 ~1)"
        (fromNumeral (normalize (App (App cminus (toNumeral 1)) (toNumeral 1))))
        (Just 0)

-- |Multiplication on naturals
-- plus = λm n. m succ n
-- cplus = lam ["m", "n"] $ Var "m" `App` csucc `App` Var "n"
-- times = λm n. m (plus n) zero
-- ctimes = lam ["m", "n"] $ Var "m" (`App` cplus `App` Var "n") z 

ctimes :: Lambda
-- ctimes = lam ["m", "n"] $ Var "m" `App` (cplus `App` Var "n") `App` Var "z"   
ctimes = (Lam "m" (Lam "n" (App (App (Var "m") (App cplus (Var "n"))) (toNumeral 0))))                 

test_ctimes = do
    test "(ctimes ~2 ~3)" (fromNumeral (normalize (App (App ctimes (toNumeral 2)) (toNumeral 3)))) (Just 6)                     
    test "(ctimes ~0 ~3)" (fromNumeral (normalize (App (App ctimes (toNumeral 0)) (toNumeral 3)))) (Just 0) 
    test "(ctimes ~4 ~1)" (fromNumeral (normalize (App (App ctimes (toNumeral 4)) (toNumeral 1)))) (Just 4) 
    test "(ctimes ~3 ~3)" (fromNumeral (normalize (App (App ctimes (toNumeral 3)) (toNumeral 3)))) (Just 9) 

-- |Boolean and
cand :: Lambda
{-
λa b. if-else a b false
= λa b. (λb t f. b t f) a b false
--> λa b. (λt f. a t f) b false
--> λa b. (λf. a b f) false
--> λa b. a b false
-}
cand = (Lam "a" (Lam "b" (App (App (Var "a") (Var "b")) (toChurchBool False))))

test_cand = do
    test "test cand t t" (fromChurchBool $ normalize $ App (App cand (toChurchBool True)) (toChurchBool True)) (Just True)
    test "test cand t f" (fromChurchBool $ normalize $ App (App cand (toChurchBool True)) (toChurchBool False)) (Just False)
    test "test cand f t" (fromChurchBool $ normalize $ App (App cand (toChurchBool False)) (toChurchBool True)) (Just False)
    test "test cand f f" (fromChurchBool $ normalize $ App (App cand (toChurchBool False)) (toChurchBool False)) (Just False)
    

-- |Boolean or
cor :: Lambda 
cor = (Lam "a" (Lam "b" (App (App (Var "a") (toChurchBool True)) (Var "b"))))

test_cor = do
    test "test cor t t" (fromChurchBool $ normalize $ App (App cor (toChurchBool True)) (toChurchBool True)) (Just True)
    test "test cor t f" (fromChurchBool $ normalize $ App (App cor (toChurchBool True)) (toChurchBool False)) (Just True)
    test "test cor f t" (fromChurchBool $ normalize $ App (App cor (toChurchBool False)) (toChurchBool True)) (Just True)
    test "test cor f f" (fromChurchBool $ normalize $ App (App cor (toChurchBool False)) (toChurchBool False)) (Just False)

-- |Boolean negation
cnot :: Lambda
cnot = (Lam "a" (App (App (Var "a") (toChurchBool False)) (toChurchBool True)))                           

test_cnot = do
    test "test cnot true" (fromChurchBool $ normalize (App cnot (toChurchBool True))) (Just False)
    test "test cnot false" (fromChurchBool $ normalize (App cnot (toChurchBool False))) (Just True)

-- conditional expression
cifthen :: Lambda
cifthen = lam ["b", "t", "f"] $ Var "b" `App` Var "t" `App` Var "f"

test_cifthen = do
    test "test cifthen t t f" (fromChurchBool $ normalize $ App (App (App cifthen (toChurchBool True)) (toChurchBool True)) (toChurchBool False)) (Just True)
    test "test cifthen t 0 1" (fromNumeral $ normalize (App (App (App cifthen (toChurchBool True)) (toNumeral 0)) (toNumeral 1))) (Just 0)
    test "test cifthen (cand t f) (ctimes 2 3) (cminus 1 2)" (fromNumeral (normalize (App (App (App cifthen (App (App cand (toChurchBool True)) (toChurchBool False))) 
       (App (App ctimes (toNumeral 2)) (toNumeral 3))) (App (App cminus (toNumeral 2)) (toNumeral 3))))) (Just 1)
    test "test cifthen f t f" (fromChurchBool $ normalize $ App (App (App cifthen (toChurchBool False)) (toChurchBool True)) (toChurchBool False)) (Just False)
    test "test ciften (cor t f) (cplus 1 2) (cminus 1 2)" (fromNumeral (normalize (App (App (App cifthen (App (App cor (toChurchBool True)) (toChurchBool False))) 
       (App (App cplus (toNumeral 1)) (toNumeral 2))) (App (App cminus (toNumeral 1)) (toNumeral 1))))) (Just 3)

-- is a given numeral zero?
ciszero :: Lambda
ciszero = Lam "n" $ Var "n" `App` (Lam "x" $ toChurchBool False) `App` (toChurchBool True)

test_ciszero = do
    test "ciszero 0" (fromChurchBool $ normalize (App ciszero (toNumeral 0))) (Just True) 
    test "ciszero 2" (fromChurchBool $ normalize (App ciszero (toNumeral 2))) (Just False) 
    test "ciszero True" (fromChurchBool $ normalize (App ciszero (toChurchBool True))) Nothing --Nothing

-- |"less or equal"
cleq :: Lambda 
cleq = lam ["m", "n"] $ ciszero `App` (cminus `App` Var "m" `App` Var "n")

test_leq = do
    test "cleq 3 4" (fromChurchBool $ normalize (App (App cleq (toNumeral 4)) (toNumeral 3))) (Just True)
    test "cleq 8 8" (fromChurchBool $ normalize (App (App cleq (toNumeral 8)) (toNumeral 8))) (Just True)
    test "cleq 5 4" (fromChurchBool $ normalize (App (App cleq (toNumeral 4)) (toNumeral 5))) (Just False)
    test "cleq False 4" (fromChurchBool $ normalize (App (App cleq (toChurchBool False)) (toNumeral 4))) (Just False) --why not nothing or why not false for iszero

-- |"less than"
clt :: Lambda 
clt = lam ["m", "n"] $
    cand `App` (cleq `App` Var "m" `App` Var "n") 
         `App` (cnot `App` (ceq `App` Var "m" `App` Var "n"))

test_clt = do
    test "clt 3 4" (fromChurchBool $ normalize (App (App clt (toNumeral 4)) (toNumeral 3))) (Just True)
    test "clt 8 8" (fromChurchBool $ normalize (App (App clt (toNumeral 8)) (toNumeral 8))) (Just False)
    test "clt 5 4" (fromChurchBool $ normalize (App (App clt (toNumeral 4)) (toNumeral 5))) (Just False)
    test "clt False 4" (fromChurchBool $ normalize (App (App clt (toChurchBool False)) (toNumeral 4))) (Just False) --another False


-- |"greater than"
cgt :: Lambda
cgt = lam ["m", "n"] $ cnot `App` (cleq `App` Var "m" `App` Var "n")

test_cgt = do
    test "cgt 3 4" (fromChurchBool $ normalize (App (App cgt (toNumeral 4)) (toNumeral 3))) (Just False)
    test "cgt 8 8" (fromChurchBool $ normalize (App (App cgt (toNumeral 8)) (toNumeral 8))) (Just False)
    test "cgt 5 4" (fromChurchBool $ normalize (App (App cgt (toNumeral 4)) (toNumeral 5))) (Just True)
    --test "cgt False 4" (fromChurchBool $ normalize (App (App cgt (toChurchBool False)) (toNumeral 4))) (Just False)  --returns true?
    test "cgt 2 True" (fromChurchBool $ normalize (App (App cgt (toNumeral 2)) (toChurchBool True))) (Just False) --another False

-- |"equal" for natural numbers
ceq :: Lambda
ceq = lam ["m", "n"] $
    cand `App` (cleq `App` Var "m" `App` Var "n")
         `App` (cleq `App` Var "n" `App` Var "m")

test_ceq = do 
    test "ceq 3 4" (fromChurchBool $ normalize (App (App ceq (toNumeral 4)) (toNumeral 3))) (Just False)
    test "ceq 8 8" (fromChurchBool $ normalize (App (App ceq (toNumeral 8)) (toNumeral 8))) (Just True)
    test "ceq 5 4" (fromChurchBool $ normalize (App (App ceq (toNumeral 4)) (toNumeral 5))) (Just False)
    test "ceq False 4" (fromChurchBool $ normalize (App (App ceq (toChurchBool False)) (toNumeral 4))) (Just False)
    test "ceq 2 True" (fromChurchBool $ normalize (App (App ceq (toNumeral 2)) (toChurchBool True))) Nothing --Nothing, not Just False?

-- |Pair constructor
cpair :: Lambda
cpair = lam ["l", "r", "s"] $ Var "s" `App` Var "l" `App` Var "r"

booleanPair :: Lambda
booleanPair = (App (App (Lam "l" (Lam "r" (Lam "s" (App (App (Var "s") (Var "l")) (Var "r"))))) 
                (Lam "t" (Lam "f" (Var "f")))) (Lam "t" (Lam "f" (Var "t"))))

oneThreePair :: Lambda
oneThreePair = (App (App (Lam "l" (Lam "r" (Lam "s" (App (App (Var "s") (Var "l")) (Var "r"))))) 
                 cone) cthree)             

complexPairLeft :: Lambda
complexPairLeft = (App (App (Lam "l" (Lam "r" (Lam "s" (App (App (Var "s") (Var "l")) (Var "r"))))) 
                booleanPair) ctwo)      

complexPairRight :: Lambda
complexPairRight = (App (App (Lam "l" (Lam "r" (Lam "s" (App (App (Var "s") (Var "l")) (Var "r"))))) 
                ctwo) booleanPair)                           

test_cpair = do 
    test "cpair simple 1" (App (App cpair (toChurchBool False)) (toChurchBool True)) booleanPair
    test "cpair simple 2" (App (App cpair (toNumeral 1)) (toNumeral 3)) oneThreePair
    test "cpair complex 3" (App (App cpair booleanPair) (toNumeral 2)) complexPairLeft
       

-- |Left of a pair
cleft :: Lambda
cleft = Lam "p" $ Var "p" `App` lam ["l", "r"] (Var "l")

test_cleft = do
    test "cleft booleanPair" (fromChurchBool $ normalize $ App cleft booleanPair) (Just False) 
    test "cleft oneThreePair" (fromNumeral $ normalize $ App cleft oneThreePair) (Just 1)
    test "cleft complexPairLeft 1" (normalize $ App cleft complexPairLeft) 
     (Lam "s1" (App (App (Var "s1") (Lam "t" (Lam "f1" (Var "f1")))) (Lam "t1" (Lam "f" (Var "t1")))))
    test "cleft complexPairLeft 2" (fromChurchBool $ normalize $ App cleft (App cleft complexPairLeft)) (Just False)

-- |Right of a pair
cright :: Lambda
cright = Lam "p" $ Var "p" `App` lam ["l", "r"] (Var "r")

test_cright =  do 
    test "cright booleanPair" (fromChurchBool $ normalize $ App cright booleanPair) (Just True) 
    test "cright oneThreePair" (fromNumeral $ normalize $ App cright oneThreePair) (Just 3)
    test "cright complexPairLeft 1" (normalize $ App cright complexPairRight) 
     (Lam "s1" (App (App (Var "s1") (Lam "t" (Lam "f1" (Var "f1")))) (Lam "t0" (Lam "f" (Var "t0")))))
    test "cright complexPairLeft 2" (fromChurchBool $ normalize $ App cright (App cright complexPairRight)) (Just True)

-- fixpoint combinator
cfix :: Lambda
cfix = Lam "f" $
                 (Lam "x" $ Var "f" `App` (Var "x" `App` Var "x")) 
           `App` (Lam "x" $ Var "f" `App` (Var "x" `App` Var "x"))

-- cfact :: Lambda
-- cfact = (Lam "f" (Lam "n" (App (App (App cifthen (Var "n")) (toNumeral 1)) (App (App ctimes (Var "n")) (App (Var "f") (App cpred (Var "n")))))))    

-- fact n = App cfix (App cfact n)

test_cfix = do
    test "cfix test 1" (App cfix (toNumeral 2)) 
     (App (Lam "f" (App (Lam "x" (App (Var "f") (App (Var "x") (Var "x")))) 
                        (Lam "x" (App (Var "f") (App (Var "x") (Var "x")))))) 
                    (Lam "s" (Lam "z" (App (Var "s") (App (Var "s") (Var "z"))))))

    test "cfix test 2" (stepNormal (App cfix (toNumeral 2)))
     (Just (App (Lam "x0" (App (Lam "s" (Lam "z" (App (Var "s") (App (Var "s") (Var "z"))))) 
                          (App (Var "x0") (Var "x0")))) 
                (Lam "x0" (App (Lam "s" (Lam "z" (App (Var "s") (App (Var "s") (Var "z"))))) 
                          (App (Var "x0") (Var "x0"))))))    

    test "cfix test 3" (step (stepNormal (App cfix (toNumeral 2))))
     (Just (App (Lam "s0" (Lam "z1" (App (Var "s0") (App (Var "s0") (Var "z1"))))) 
           (App (Lam "x0" (App (Lam "s" (Lam "z" (App (Var "s") (App (Var "s") (Var "z"))))) (App (Var "x0") (Var "x0")))) 
                (Lam "x0" (App (Lam "s" (Lam "z" (App (Var "s") (App (Var "s") (Var "z"))))) (App (Var "x0") (Var "x0")))))))                                  

allTests :: IO ()
allTests = do
    test_lam_app
    test_bools
    test_numerals
    test_csucc
    test_cpred
    test_cplus
    test_cminus
    test_ctimes
    test_cand
    test_cor
    test_cnot
    test_cifthen
    test_ciszero
    test_leq
    test_clt
    test_cgt
    test_ceq
    test_cpair
    test_cleft
    test_cright
    test_cfix

