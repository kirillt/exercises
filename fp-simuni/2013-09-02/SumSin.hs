main = do
    print $ sumsin 1000000

sumsin = cps

-- Don't know why, but these two functions have different precision.

simple n = (sin $! sum [1..n]) / (sum $! map sin [1..n])

-- In WinHugs `sum' is strict, so no stack overflows,
-- but in GHC `sum' is lazy, so you must set +RTS -K<size> -RTS for successful run.

-- > time ./SumSin
-- real	0m4.397s
-- user	0m4.204s
-- sys	0m0.168s

-- without optimization:
--    total time  =        2.38 secs   (2383 ticks @ 1000 us, 1 processor)
--    total alloc = 304,076,736 bytes  (excludes profiling overheads)

-- with O3:
--    total time  =        2.22 secs   (2218 ticks @ 1000 us, 1 processor)
--    total alloc = 304,076,468 bytes  (excludes profiling overheads)


cps n = sum_nums 0 n (\nums -> sum_sins 0 n (\sins -> (sin nums) / sins))
    where
        sum_nums acc 0 after = after acc
        sum_nums acc i after = ((sum_nums $! acc +      i ) $! i - 1) after

        sum_sins acc 0 after = after acc
        sum_sins acc i after = ((sum_sins $! acc + (sin i)) $! i - 1) after

-- Explicit tail recursive.

-- > time ./SumSin
--    real	0m2.057s
--    user	0m2.016s
--    sys	0m0.032s

-- without optimization:
--    total time  =        3.27 secs   (3265 ticks @ 1000 us, 1 processor)
--    total alloc = 320,075,824 bytes  (excludes profiling overheads)

-- with O3:
--    total time  =        0.25 secs   (251 ticks @ 1000 us, 1 processor)
--    total alloc =      76,040 bytes  (excludes profiling overheads)
