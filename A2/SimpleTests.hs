{- |
Module      :  SimpleTests
Description :  Trivial machinery for unit tests.

Maintainer  :  Ferd <f.vesely@northeastern.edu>
-}

module SimpleTests where

-- A simple testing function
test :: (Eq a, Show a) => String -> a -> a -> IO ()
test label actual expected = 
  if actual == expected
     then do putStrLn $ "Test <" ++ label ++ "> passed"
     else do 
       putStrLn $ "Test <" ++ label ++ "> failed:"
       putStrLn $ "   expected: " ++ show expected
       putStrLn $ "   actual: " ++ show actual

