{-# LANGUAGE MultiParamTypeClasses #-}

module Money.Money where

import Data.Char (toUpper)
import Utils.Tuple

data Money     = Money Currency Double deriving (Show,Eq)
data Currency  = BTC | USD             deriving (Show,Read,Ord,Eq)
type Price     = Double

instance Read Money where
    readsPrec p s = do
        (c,s' ) <- readsPrec p $ toUpper s
        (v,s'') <- readsPrec p s'
        return (Money c v, restore s'')
        where
            toUpper   = map Data.Char.toUpper
            restore r = drop (length s - length r) s

instance Tuple2 Money Currency Double where
    toTuple2   (Money c v) = (c,v)
    fromTuple2 (c,v)  = Money c v
