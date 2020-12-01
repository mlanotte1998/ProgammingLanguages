{-|
Module      : Result
Description : The Result datatype
Copyright   : (c) Ferd, 2020
Maintainer  : f.vesely@northeastern

This module provides a type of results: either we have a value or we have a
failure with an error message. The type is a monad. Several helper functions are provided.
-}
module Result where


-- |Represents a successful result with a value or a failuer with an error 
-- message.
data Result a = Success a
              | Failure String
              deriving (Show, Read, Eq)

-- |Result is a functor and can be mapped over
instance Functor Result where
    -- fmap :: (a -> b) -> Result a -> Result b
    fmap f (Success x) = Success $ f x
    fmap _ (Failure s) = Failure s

-- |Result is also an applicative functor
instance Applicative Result where
    -- pure :: a -> Result a
    pure = Success

    -- (<*>) :: Result (a -> b) -> Result a -> Result b
    Success f <*> ra = f <$> ra
    Failure s <*> _  = Failure s

-- |Result is a monad.
instance Monad Result where
    -- return :: a -> Result a
    return = Success

    -- (>>=) :: Result a -> (a -> Result b) -> Result b
    Success x >>= f = f x
    Failure s >>= _ = Failure s

-- |Result can represent failure in a monadic context.
instance MonadFail Result where
    -- fail :: String -> Result a
    fail = Failure

-- |Convert from a Maybe to a Result, with a default error message for Nothing
fromMaybe :: Maybe a -> Result a
fromMaybe (Just x) = Success x
fromMaybe Nothing = Failure "Got Nothing"

-- |Convert from a Maybe to a Result, using the given error message for Nothing
fromMaybe' :: String -> Maybe a -> Result a
fromMaybe' _   (Just x) = Success x
fromMaybe' msg Nothing = Failure msg

-- |Convert a Result to a Maybe
toMaybe :: Result a -> Maybe a
toMaybe (Success x) = Just x
toMaybe (Failure _) = Nothing

-- |Convert a Result to IO
toIO :: Result a -> IO a
toIO (Success x) = return x
toIO (Failure s) = fail s

