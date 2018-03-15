module Utils.Range where

import Data.Serialize
import Control.Applicative

data Range a = Range {
    low  :: a,
    high :: a
} deriving (Show, Eq)

toTuple :: Range a -> (a,a)
toTuple (Range l h) = (l,h)

fromTuple :: (a,a) -> Range a
fromTuple (l,h) = Range l h

instance (Ord a, Num a) => Ord (Range a) where
    l `compare` r = size l `compare` size r

instance Read a => Read (Range a) where
    readsPrec p = map convert . readsPrec p . map sugar
        where
            convert (x,rest) = (fromTuple x,rest)
            sugar '[' = '('
            sugar ']' = ')'
            sugar '<' = '('
            sugar '>' = ')'
            sugar  c  =  c

instance Serialize a => Serialize (Range a) where
    put r = put $ toTuple r
        where
    get   = fromTuple <$> get
        where

contain :: Ord a => Range a -> Range a -> Bool
contain (Range l r) (Range l' r') = l <= l' && r' <= r

size :: Num a => Range a -> a
size (Range l r) = r - l
