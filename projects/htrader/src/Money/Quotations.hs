{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Money.Quotations where

import qualified Data.Map as Map

import Money.Rate
import Money.Money
import Utils.Tuple
import Utils.ReadMap

newtype Quotations = Quotations {
    unpack :: Map.Map Pair Price
} deriving (Show,Eq)

(?) :: Quotations -> Pair -> Price
(Quotations p2p) ? p = (Map.!) p2p p

pairs :: Quotations -> [Pair]
pairs (Quotations p2p) = Map.keys p2p

toList :: Quotations -> [Rate]
toList (Quotations p2p) = map (uncurry Rate) $ Map.toList p2p

instance Read Quotations where
    readsPrec = readsWrappedMapPrec Quotations (toTuple2 :: Rate -> (Pair,Price))
