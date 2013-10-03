import Prelude hiding (filter)

--import System.IO
--import System.Random
--generateTest n = do
--    file <- openFile "test" WriteMode
--    hPrint file n
--    mapM_ (\t -> do; x <- rnd; hPutStr file $ show x ++ " ") [1..n]
--    hClose file
--rnd :: IO Int
--rnd = getStdRandom $ randomR (-1000,1000)

get :: IO [Int]
get = fmap ((map read) . words) getLine

main = do
    [n] <- get
    (ts,(minD,maxD)) <- fmap (scan n) get
    print $ maximum $  map (tryAll $ cycle ts) $ gen n minD maxD

-- 20000 - limit for n in problem
scan n ts = (ts,scan' 0 1 (n,0) ts) where
    scan' c i (minD,maxD)   []    = if   c > 1
                                    then (min minD i, max maxD i)
                                    else if   c == 1
                                         then (2,n)  -- a little dirty: should be 1
                                         else (1,0)  -- hack: to make next list empty
    scan' c i (minD,maxD)  (t:ts) = if   t < 0
                                    then scan' (c+1)   1  (min minD i, max maxD i) ts
                                    else scan'  c   (i+1) (    minD  ,     maxD  ) ts

gen n minD maxD = [ (k,m) | m <- 1:[minD..maxD], let k = n `div` m, n `mod` m == 0 && k > 2 ]

tryAll ts (k,m) = maximum $ map sum $ cycles ts (k,m)
cycles ts (k,m) = cycles' ts (k,m) m where
    cycles' _  (_,_) 0 = []
    cycles' ts (k,m) i = (take k $ filter ts m):(cycles' (tail ts) (k,m) $ i-1)

filter ts    1  = ts
filter ts    m  = filter' 0 ts m where
    filter' _ []     _ = []
    filter' 0 (t:ts) m = t:(filter'     1           ts m)
    filter' i (t:ts) m =    filter' ((i+1) `mod` m) ts m
