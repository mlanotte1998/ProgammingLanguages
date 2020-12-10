{-# OPTIONS_GHC -Wno-type-defaults #-}
{-|
Module      : Maps
Description : An implementation of maps as association lists
Copyright   : (c) Ferd, 2020
Maintainer  : f.vesely@northeastern

This module provides an implementation of maps as association lists. 

-}

module Maps 
    ( empty
    , get
    , set
    , keys
    , fromList
    , toList
    , Map
    , Maps.allTests
    ) where

import Data.List (nub)

import SimpleTests (test)

newtype Map k v = Map [(k, v)]
                deriving Eq

instance (Show k, Show v) => Show (Map k v) where
    show (Map m) = "fromList " ++ show m


-- |Empty map, that is, a map containing no bindings.
empty :: Map k v
empty = Map []

-- |Get a binding from a map.
get :: Eq k => Map k v -> k -> Maybe v
get (Map ((y, v) : m)) x 
    | x == y = Just v
    | otherwise = get (Map m) x
get (Map []) _ = Nothing

-- |Add a binding to the given map
set :: Map k v -> k -> v -> Map k v 
set (Map m) x v = Map $ (x, v) : m

-- |Return all the keys in a given map
keys :: Eq k => Map k v -> [k]
keys (Map m) = nub . map fst $ m

-- |Construct a map from the given list of key-value pairs
fromList :: [(k, v)] -> Map k v
fromList = Map

-- |Return a list of all key-value pairs
toList :: Map k v -> [(k, v)] 
toList (Map m) = m

allTests :: IO ()
allTests = do
    test "0" 
        (empty :: Map String Integer) 
        (fromList [])
    test "1" 
        (set empty "x" 12) 
        (fromList [("x", 12)])
    test "2" (set (set empty "x" 12) "y" 55) 
        (fromList [("y", 55), ("x", 12)])
    test "3" 
        (set (set (set empty "x" 12) "y" 55) "x" 14) 
        (fromList [("x", 14), ("y", 55), ("x", 12)])
    test "4" (get (empty :: Map String Integer) "x") Nothing
    test "5" (get (set empty "x" 12) "x") (Just 12)
    test "6" (get (set empty "x" 12) "y") Nothing
    test "7" (get (set (set empty "x" 12) "y" 55) "x") (Just 12)
    test "7" (get (set (set empty "x" 12) "y" 55) "y") (Just 55)
    test "8" (get (set (set (set empty "x" 12) "y" 55) "x" 14) "x") (Just 14)
    test "9" (get (set (set (set empty "x" 12) "y" 55) "x" 14) "y") (Just 55)
    test "10" (get (set (set (set empty "x" 12) "y" 55) "x" 14) "z") Nothing
    test "keys 1" 
        (keys $ 
            fromList [ ("x", 12), ("y", 13), ("z", 14), ("x", 11), ("z", 42)])
        [ "x", "y", "z" ]

