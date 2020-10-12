{-# LANGUAGE LambdaCase #-}
{- |
Module      :  SimpleTests
Description :  Trivial machinery for unit tests.

Maintainer  :  Ferd <f.vesely@northeastern.edu>
-}

module SimpleTests 
    ( test
    , testError
    , testErrorMsg
    , testStats
    , beginTests
    , endTests
    ) where

import qualified Control.Exception as E

import Data.IORef (newIORef, modifyIORef', readIORef, writeIORef)
import System.IO.Unsafe (unsafePerformIO)

-- |Test whether the actual value matches the expected one, printing diagnostics.
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
    passed <- readIORef passedCount
    failed <- readIORef failedCount
    putStrLn $ 
        "Ran " ++ show (passed + failed) ++ " tests. " 
        ++ show passed ++ " passed, " ++ show failed ++ " failed."

-- |Set up a test batch.
-- Resets test counters to 0.
beginTests :: IO ()
beginTests = do
    writeIORef passedCount 0
    writeIORef failedCount 0

-- |End tests, print test stats.
endTests :: IO ()
endTests = do
    testStats

-- Helpers

-- Count the number of passed tests
{-# NOINLINE passedCount #-}
passedCount = unsafePerformIO $ newIORef 0

-- Counte the number of failed tests
{-# NOINLINE failedCount #-}
failedCount = unsafePerformIO $ newIORef 0

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
    putStrLn $ "Test <" ++ label ++ "> failed:"
    putStrLn $ "   expected: " ++ expected
    putStrLn $ "   actual: " ++ actual

-- |Print a passing test with an optional extra message
passed :: String -> String -> IO ()
passed label extra 
    | null extra = do 
        upPassed
        putStrLn $ msg                    
    | otherwise = do 
        upPassed
        putStrLn $ msg ++ " " ++ extra
  where
    msg = "Test <" ++ label ++ "> passed."
        
