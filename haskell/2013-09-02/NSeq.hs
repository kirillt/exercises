main = print $ nseq 80

nseq :: Int -> [[Int]]
nseq = plain

plain n = work 0 n
    where
        work p n | p < n = do
            x  <- [(p+1)..n]
            xs <- work x (n-x)
            return $ x:xs
        work _ 0 = [[]]
        work _ _ = []

-- without options:
--     time of 3 launches:
--         0m0.000s 0m0.008s
--         0m5.524s 0m1.692s
--     profiling:
--         total time  =        2.19 secs   (2190 ticks @ 1000 us, 1 processor)
--         total alloc = 217,882,272 bytes  (excludes profiling overheads)
-- with -O3:
--     time of 3 launches:
--         0m0.008s 0m0.000s
--         0m3.412s 0m0.060s
--     profiling:
--         total time  =        0.94 secs   (941 ticks @ 1000 us, 1 processor)
--         total alloc = 129,358,772 bytes  (excludes profiling overheads)
