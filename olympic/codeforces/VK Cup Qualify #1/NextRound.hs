import Data.List

get :: IO [Int]
get = fmap ((map read) . words) getLine

main = do
    [_,k] <- get
    bs    <- get
    print $ length $ filter (> 0) $ (winners k) bs

winners k bs = winners' $ splitAt (k-1) bs where
    winners' (fs,bk:ks) = fs ++ bk:(takeWhile (==bk) ks)
