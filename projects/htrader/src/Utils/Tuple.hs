{-# LANGUAGE MultiParamTypeClasses #-}

module Utils.Tuple where

class Tuple2 x a b where
    toTuple2   :: x -> (a,b)
    fromTuple2 :: (a,b) -> x

class Tuple3 x a b c where
    toTuple3   :: x -> (a,b,c)
    fromTuple3 :: (a,b,c) -> x

class Tuple4 x a b c d where
    toTuple4   :: x -> (a,b,c,d)
    fromTuple4 :: (a,b,c,d) -> x
