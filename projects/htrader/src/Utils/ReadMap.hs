module Utils.ReadMap where

import Utils.Tuple
import Data.Map hiding (map)

readsWrappedMapPrec :: (Read x, Ord k) => (Map k v -> y) -> (x -> (k,v)) -> Int -> ReadS y
readsWrappedMapPrec w t p s = do
    (result,rest) <- readsMapPrec t p s
    return (w result,rest)

readsMapPrec :: (Read x, Ord k) => (x -> (k,v)) -> Int -> ReadS (Map k v)
readsMapPrec toTuple2 p s = do
    (xs,rest) <- readsPrec p $ map sugar s
    let k2v = fromList $ map toTuple2 xs
    let n   = length xs
    let k   = size k2v
    case k /= n of
        True  -> fail "some keys are duplicates"
        False -> return (k2v,rest)
        where
            sugar '{' = '['
            sugar '}' = ']'
            sugar ':' = ' '
            sugar  c  =  c
