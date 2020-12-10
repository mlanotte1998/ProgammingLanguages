{-# OPTIONS_GHC -fno-cse -fno-full-laziness #-}
{-|
Module      : Gensym
Description : Fresh variable generator.
Copyright   : (c) Ferd, 2020
Maintainer  : f.vesely@northeastern

The code in this module is considered "unsafe". It should work ok in most circumstances, but there might be corner cases where it will cause trouble. Do reach out if you experience difficulties using this module.
-}

module Gensym (gensym) where

import Data.Unique
import System.IO.Unsafe (unsafePerformIO)

-- |Generate a fresh variable based on the given one. The resulting variable has the form
-- "x#n" where "#n" is a "uniqueness suffix".
--
-- Warning: This function relies on `unsafePerformIO` to avoid putting otherwise pure code 
-- into the IO monad.
--
-- Examples:
--
-- >>> gensym "X"
-- "X#2"
--
-- >>> gensym "X"
-- "X#3"
--
-- >>> gensym "Z"
-- "Z#4"
--
{-# NOINLINE gensym #-}
gensym :: String -> String
gensym = unsafePerformIO . gensym' . baseName
  where
    baseName :: String -> String
    baseName = takeWhile (/= '#')

gensym' :: String -> IO String
gensym' s = do
  u <- newUnique
  return $ s ++ "#" ++ show (hashUnique u)



