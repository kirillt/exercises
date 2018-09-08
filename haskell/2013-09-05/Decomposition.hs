import Control.Monad (when)
import Control.DeepSeq (deepseq)
import Control.Exception.Base (evaluate)

import qualified Primes   as P (primes)
import qualified Data.Set as S
import qualified Data.Map as M

main = do
    evaluate $ foldr deepseq () $ map c [1..100]
    putStrLn "Done."

c = length . decompose

-- may be it is possible to implement simpler with just counting sum of any primes
decompose :: Integer -> [[Integer]]
decompose n | n > 1 = nseq
    where
        primes      = P.primes n
        isPrime   p = p `elem` primes

        -- should be optimized to produce every production only once =/
        productions = M.fromList $ map (\(m,ps) -> (m,S.fromList ps)) $ load 1 []
            where
                load m acc | m <= n = do
                    p  <- primes
                    (m,acc):(load (m*p) $ p:acc)
                load m acc = []

        nseq = work 0 n $ S.empty
            where
                work s n used | s < n = do
                    x  <- [(s+1)..n]
                    let ds = productions M.! x
                    when (not $ S.null $ ds `S.intersection` used) []
                    xs <- work x (n-x) $ ds `S.union`        used 
                    return $ x:xs
                work _ 0 _ = [[]]
                work _ _ _ = []
decompose 1 = [[1]]
decompose 0 = []

-- profiling:
--     with -O3:
--         total time  =       38.29 secs   (38292 ticks @ 1000 us, 1 processor)
--         total alloc = 1,524,267,460 bytes  (excludes profiling overheads)
--     with -threaded -O3 and -N2:
--         total time  =       19.21 secs   (38424 ticks @ 1000 us, 2 processors)
-- 	       total alloc = 1,524,267,780 bytes  (excludes profiling overheads)
