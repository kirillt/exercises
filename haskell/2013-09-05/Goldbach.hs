import Control.DeepSeq
import Control.Exception.Base

import Primes (primes)

main = do
    evaluate $ foldr deepseq () $ map goldbach [1..2000]
    putStrLn "Done."

goldbach = simple'

simple  n = let ps = primes n
            in not $ null [ () | p <- ps, p < n `div` 2 + 1, p /= n - p, n-p `elem` ps ]

-- profiling:
--     total time  =        5.36 secs   (5361 ticks @ 1000 us, 1 processor)
--     total alloc = 285,300,276 bytes  (excludes profiling overheads)

-- tiny boost because of little heuristic (search from the end of primes)
simple' n = let ps  = primes n
                ps' = reverse [ p | p <- ps, p > n `div` 2 ]
            in not $ null [ () | p <- ps', p > n `div` 2, p /= n - p, n-p `elem` ps ]

-- profiling:
--     total time  =        5.11 secs   (5106 ticks @ 1000 us, 1 processor)
--     total alloc = 294,296,568 bytes  (excludes profiling overheads)
