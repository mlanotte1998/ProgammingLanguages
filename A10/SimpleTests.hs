{-# LANGUAGE LambdaCase #-}
{- |
Module      :  SimpleTests
Description :  Trivial machinery for unit tests.

Maintainer  :  Ferd <f.vesely@northeastern.edu>

A simple unit test library. Example use:

For example, given the following definition

> test_something :: IO ()
> test_something = do
>     beginTests
>     testSection "Some tests"
>     test "is it true?" (not False) True
>     test "successor" (10 + 1) 11
>     testSection "Some more tests"
>     test "reverse" (reverse [1, 2, 3]) [3, 2, 1]
>     test "this will fail" (1 + 1) 3
>     endTests

We get the following:

>>> test_something
=== Some tests
Test <is it true?>    passed
Test <successor>    passed
=== Some more tests
Test <reverse>    passed
Test <this will fail>   failed
   expected: 3
   actual: 2
------
Ran 4 tests: 3 passed, 1 failed

-}

module SimpleTests 
    ( test
    , testError
    , testErrorMsg
    , testStats
    , beginTests
    , endTests
    , testSection
    ) where

import qualified Control.Exception as E

import Data.IORef (IORef(), newIORef, modifyIORef', readIORef, writeIORef)
import System.IO.Unsafe (unsafePerformIO)

-- |Test whether the actual value matches the expected one, printing diagnostics.
--
-- Example:
--
-- >>> test "commutative" (5 + 3) (3 + 5)
-- Test <commutative>    passed
--
test :: (Eq a, Show a) => String -> a -> a -> IO ()
test label actual expected 
    | actual == expected = passed label ""
    | otherwise = printTestFail label expected actual

-- |Test test for an expected error.
testError :: Show a => String -> a -> IO ()
testError label actual = do
    let x = E.evaluate actual >> failed label "An error." (show actual)
    E.catch x $ \case 
      E.ErrorCallWithLocation msg _ -> passed label ("Error message was: " ++ msg) 
      -- e -> failed label "An error." ("An exception: " ++ E.displayException e)
    return ()

-- |Test test for an expected error with a specific message.
testErrorMsg :: Show a => String -> a -> String -> IO ()
testErrorMsg label actual expectedMsg = do
    let x = E.evaluate actual >> 
              failed label ("An error: " ++ expectedMsg) (show actual)
    E.catch x $ \case 
      E.ErrorCallWithLocation msg _ ->
          if msg == expectedMsg 
             then passed label "Got an error."
             else failed label ("Error message \"" ++ expectedMsg ++ "\"") msg
      ---e -> failed label "An error." ("An exception: " ++ E.displayException e)
    return ()

-- |Print the test stats.
testStats :: IO ()
testStats = do
    passedNo <- readIORef passedCount
    failedNo <- readIORef failedCount
    putStrLn "\n------"
    putStrLn $ 
        "Ran " ++ show (passedNo + failedNo) ++ " tests: " 
        ++ good (show passedNo ++ " passed") 
        ++ ", " 
        ++ bad (show failedNo ++ " failed")

-- |Set up a test batch.
-- Resets test counters to 0.
beginTests :: IO ()
beginTests = do
    writeIORef passedCount 0
    writeIORef failedCount 0

-- |End tests, print test stats.
endTests :: IO ()
endTests = 
    testStats

-- |Label a test section
testSection :: String -> IO ()
testSection s = putStrLn $ "=== " ++ s

-- Helpers

-- Count the number of passed tests
{-# NOINLINE passedCount #-}
passedCount :: IORef Int
passedCount = unsafePerformIO $ newIORef 0

-- Counte the number of failed tests
{-# NOINLINE failedCount #-}
failedCount :: IORef Int
failedCount = unsafePerformIO $ newIORef 0

upPassed, upFailed :: IO ()
upPassed = modifyIORef' passedCount (+ 1)
upFailed = modifyIORef' failedCount (+ 1)

-- |Print the failing test, the expected value and actual value
printTestFail :: Show a => String -> a -> a -> IO ()
printTestFail label expected actual =
    failed label (show expected) (show actual)

-- |Print the failing test, the expected outcome and actual outcome
failed :: String -> String -> String -> IO ()
failed label expected actual = do 
    upFailed
    putStrLn $ "Test <" ++ emph label ++ ">   " ++ bad "failed"
    putStrLn $ "   expected: " ++ good expected
    putStrLn $ "   actual: " ++ bad actual

-- |Print a passing test with an optional extra message
passed :: String -> String -> IO ()
passed label extra 
    | null extra = do 
        upPassed
        putStrLn msg
    | otherwise = do 
        upPassed
        putStrLn $ msg ++ " " ++ extra
  where
    msg = "Test <" ++ emph label ++ ">    " ++ good "passed"


-- |No colors.
bad, good, emph :: String -> String
bad = id 
good = id
emph = id



