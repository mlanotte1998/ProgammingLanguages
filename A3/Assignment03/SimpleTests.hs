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
    ) where

import qualified Control.Exception as E

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




-- Helpers


-- |Print the failing test, the expected value and actual value
printTestFail :: Show a => String -> a -> a -> IO ()
printTestFail label expected actual =
    failed label (show expected) (show actual)

-- |Print the failing test, the expected outcome and actual outcome
failed :: String -> String -> String -> IO ()
failed label expected actual = do 
    putStrLn $ "Test <" ++ label ++ "> failed:"
    putStrLn $ "   expected: " ++ expected
    putStrLn $ "   actual: " ++ actual

-- |Print a passing test with an optional extra message
passed :: String -> String -> IO ()
passed label extra | null extra = putStrLn $ msg 
                   | otherwise = putStrLn $ msg ++ " " ++ extra
  where
    msg = "Test <" ++ label ++ "> passed."
        
