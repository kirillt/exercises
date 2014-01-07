{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Money.Wallet where

import Data.Map hiding (map)

import Money.Money
import Utils.Tuple
import Utils.ReadMap

newtype Wallet = Wallet {
    unpack :: Map Currency Double
} deriving (Show,Eq)

(&) :: Wallet -> Currency -> Double
(Wallet c2v) & c = c2v ! c

($$) :: Wallet -> Money -> Wallet
(Wallet c2v) $$ (Money c v) = Wallet $ insert c v c2v

currencies :: Wallet -> [Currency]
currencies (Wallet c2v) = keys c2v

toList :: Wallet -> [Money]
toList (Wallet c2v) = map (uncurry Money) $ Data.Map.toList c2v

instance Read Wallet where
    readsPrec = readsWrappedMapPrec Wallet (toTuple2 :: Money -> (Currency,Double))
