import Data.List (foldl')

main = do
    print $ sumfact 1800

sumfact = simple

simple n = sum' $ map fact [1..n]
    where
        fact k = product' [1..k]

        product' = foldl' (*) 1
        sum'     = foldl' (+) 0

-- without options:
--     time of 3 launches:
--         0m0.004s 0m0.000s
--         0m8.628s 0m0.164s
--     profiling:
--         total time  =        2.74 secs   (2744 ticks @ 1000 us, 1 processor)
--         total alloc = 1,160,125,816 bytes  (excludes profiling overheads)
-- with -O3:
--     time of 3 launches:
--         0m0.000s 0m0.004s
--         0m8.536s 0m0.144s
--     profiling:
--         total time  =        2.73 secs   (2731 ticks @ 1000 us, 1 processor)
--         total alloc = 1,160,017,684 bytes  (excludes profiling overheads)


cps n = run id n 0
    where
        run after 0 acc = after acc
        run after i acc = fact 1 i $ run after $ i - 1
            where
                fact acc' 0 after' =  after' $! acc' + acc
                fact acc' j after' = (fact   $! acc' *  j) (j - 1) after'

-- without options:
--     time of 3 launches:
--         0m0.000s 0m0.004s
--         0m13.048s 0m0.200s
--     profiling:
--         total time  =        4.21 secs   (4213 ticks @ 1000 us, 1 processor)
--         total alloc = 1,382,950,044 bytes  (excludes profiling overheads)
-- with -O3:
--     time of 3 launches:
--         0m0.000s 0m0.004s
--         0m8.568s 0m0.204s
--     profiling:
--         total time  =        2.76 secs   (2756 ticks @ 1000 us, 1 processor)
--         total alloc = 1,285,472,764 bytes  (excludes profiling overheads)


tailrecursive n = run n 0
    where
        run 0 acc = acc
        run i acc = fact 1 i
            where
                fact acc' 0 = run (i - 1) $! acc' + acc
                fact acc' j = (fact   $! acc' *  j) $ j - 1

-- without options:
--     time of 3 launches:
--         0m0.000s 0m0.004s
--         0m13.888s 0m0.248s
--     profiling:
--         total time  =        4.49 secs   (4491 ticks @ 1000 us, 1 processor)
--         total alloc = 1,415,317,644 bytes  (excludes profiling overheads)
-- with -O3:
--     time of 3 launches:
--         0m0.000s 0m0.004s
--         0m5.816s 0m2.964s
--     profiling:
--         total time  =        2.78 secs   (2781 ticks @ 1000 us, 1 processor)
--         total alloc = 1,285,429,564 bytes  (excludes profiling overheads)
