main = do
    print $ b 1000000

b = combinators

tailrecursive n = run n n
    where
        run acc 0 = acc
        run acc n = (run $! ((n - 1) + (1 / acc))) $! n - 1

-- > time ./QuasiGoldenRatio
--    real	0m1.939s
--    user	0m1.916s
--    sys	0m0.016s

-- without optimization:
--    total time  =        3.14 secs   (3143 ticks @ 1000 us, 1 processor)
--    total alloc = 268,075,712 bytes  (excludes profiling overheads)

-- with -O3:
--    total time  =        0.18 secs   (177 ticks @ 1000 us, 1 processor)
--    total alloc =      75,612 bytes  (excludes profiling overheads)

combinators n = foldl' cons n $! reverse [1..n]
    where
        cons acc n = (n - 1) + (1 / acc)

        -- Strict foldl
        foldl' _ acc    []  = acc
        foldl' f acc (x:xs) = (foldl' f $! f acc x) xs

-- > time ./QuasiGoldenRatio
--    real	0m2.567s
--    user	0m2.428s
--    sys	0m0.128s

-- without optimization:
--    total time  =        2.84 secs   (2841 ticks @ 1000 us, 1 processor)
--    total alloc = 268,075,912 bytes  (excludes profiling overheads)

-- with -O3:
--    total time  =        1.20 secs   (1202 ticks @ 1000 us, 1 processor)
--    total alloc = 116,075,776 bytes  (excludes profiling overheads)
