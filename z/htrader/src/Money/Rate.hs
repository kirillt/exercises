{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances  #-}

module Money.Rate where

import Money.Money

import Data.Default
import Utils.Tuple
import Data.Char (toUpper)

data Pair = Pair {
    from :: Currency,
    to   :: Currency
} deriving (Show,Ord,Eq)

instance Default Pair where
    def = btc2usd

btc2usd :: Pair
btc2usd = Pair BTC USD

usd2btc :: Pair
usd2btc = Pair USD BTC

instance Read Pair where
    readsPrec i s = empty2def $ readsPrec'
        where
            readsPrec' = do
                (f,s' ) <- readsCurrency $ toUpper s
                (t,s'') <- readsCurrency s'
                return (Pair f t, restore $ s'')

            readsCurrency :: ReadS Currency
            readsCurrency = readsPrec i

            empty2def :: Default a => [(a, String)] -> [(a, String)]
            empty2def [] = [(def,s)]
            empty2def xs = xs

            toUpper   = map Data.Char.toUpper
            restore r = drop (length s - length r) s

data Rate = Rate {
    pair  :: Pair,
    price :: Price
} deriving (Show,Eq)

instance Read Rate where
    readsPrec i s = do
        (k,s' ) <- (readsPrec i :: ReadS Pair ) s
        (v,s'') <- (readsPrec i :: ReadS Price) s'
        return (Rate k v, s'')

instance Tuple2 Rate Pair Price where
    toTuple2   (Rate k v) = (k,v)
    fromTuple2 (k,v)  = Rate k v
