{-|
Module      : Maps
Description : An implementation of maps as association lists
Copyright   : (c) Ferd, 2020
Maintainer  : f.vesely@northeastern

This module provides an implementation of maps as association lists. 

-}


module Maps where

type Map k v = [(k, v)]

-- |Empty map, that is, a map containing no bindings.
empty :: Map k v
empty = []

-- |Get a binding from a map.
get :: Eq k => Map k v -> k -> Maybe v
get ((y, v) : m) x | x == y = Just v
                   | otherwise = get m x
get [] x = Nothing

-- |Add a binding to the given map
set :: Map k v -> k -> v -> Map k v 
set m x v = (x, v) : m


