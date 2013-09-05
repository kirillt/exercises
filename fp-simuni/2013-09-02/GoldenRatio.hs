main = do
    print $ f 1000000

f = tailrecursive

naive 0 = 1
naive n = 1 + (1 / (naive $ n - 1))

-- Gives stack overflow on high parameters;
-- to change it run compiled program with "+RTS -K<size> -RTS" arguments.

-- > time ./GoldenRatio
--    real	0m3.589s
--    user	0m3.344s
--    sys	0m0.224s

-- without optimization:
--    total time  =        2.35 secs   (2347 ticks @ 1000 us, 1 processor)
--    total alloc = 176,075,936 bytes  (excludes profiling overheads)

-- with -O3:
--    total time  =        0.33 secs   (327 ticks @ 1000 us, 1 processor)
--    total alloc =   8,075,836 bytes  (excludes profiling overheads)


tailrecursive n = run 1 n
    where
        run acc 0 = acc
        run acc n = (run $! (1 + (1 / acc))) $! n - 1

-- > time ./GoldenRatio
--    real	0m1.625s
--    user	0m1.604s
--    sys	0m0.012s

-- without optimization:
--    total time  =        2.68 secs   (2683 ticks @ 1000 us, 1 processor)
--    total alloc = 192,075,944 bytes  (excludes profiling overheads)

-- with -O3:
--    total time  =        0.29 secs   (287 ticks @ 1000 us, 1 processor)
--    total alloc =   8,075,836 bytes  (excludes profiling overheads)
