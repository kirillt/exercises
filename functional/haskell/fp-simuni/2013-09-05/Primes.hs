module Primes where

import Control.DeepSeq (deepseq)
import Control.Exception.Base (evaluate)

main = do
    evaluate $ foldr deepseq () $ map primes [1..2000]
    putStrLn "Done."

primes :: Integer -> [Integer]
primes n | n > 1 = 2 : sieve [3,5..n]
    where
        sieve    []  = []
        sieve (p:xs) = p : sieve (xs `minus` [p*p,p*p+2*p..n])

        minus []              _            =      []
        minus xs              []           =      xs
        minus    (x:xt)    (y:yt) | x == y =      xt `minus` yt
        minus xs@(x:xt)    (y:yt) | x >  y =      xs `minus` yt
        minus    (x:xt) ys@(y:yt) | x <  y = x : (xt `minus` ys)
primes n = []

-- without options:
--     time of 1 launches:
--         0m0.000s 0m0.004s
--         0m3.596s 0m0.008s
--     profiling:
--         total time  =        3.78 secs   (3783 ticks @ 1000 us, 1 processor)
--         total alloc = 274,903,772 bytes  (excludes profiling overheads)
-- with -O3:
--     time of 1 launches:
--         0m0.004s 0m0.000s
--         0m3.560s 0m0.032s
--     profiling:
--         total time  =        3.51 secs   (3506 ticks @ 1000 us, 1 processor)
--         total alloc = 274,909,212 bytes  (excludes profiling overheads)
-- with -threaded:
--     time of 1 launches:
--         0m0.000s 0m0.004s
--         0m3.580s 0m0.020s
--     profiling:
--         total time  =        3.52 secs   (3521 ticks @ 1000 us, 1 processor)
--         total alloc = 274,909,212 bytes  (excludes profiling overheads)
-- with -threaded -O3:
--     time of 1 launches:
--         0m0.000s 0m0.004s
--         0m3.544s 0m0.028s
--     profiling:
--         total time  =        3.51 secs   (3512 ticks @ 1000 us, 1 processor)
--         total alloc = 274,909,212 bytes  (excludes profiling overheads)
