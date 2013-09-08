import Permutations8
import Data.List (splitAt)
import Control.Monad.Cont

main = putStrLn $ foldl (\_ _ -> "Done.") undefined $ map sort $ [1..1000] >>= (const permutations)

sort :: [Integer] -> [Integer]
sort = mergesort_cps_m

merge cmp       []        rs  = rs
merge cmp       ls        []  = ls
merge cmp ls@(l:lt) rs@(r:rt) =
    if l `cmp` r then r:(merge cmp ls rt)
                 else l:(merge cmp lt rs)


mergesort xs = work xs $ length xs
    where
        merge' = merge (>)

        work [ ] n = [ ]
        work [x] n = [x]
        work xs  n =
            let lsize   = n `div` 2
                rsize   = n - lsize
                (ls,rs) = splitAt lsize xs
            in merge' (work ls lsize) (work rs rsize)

-- without options:
--     time of 3 launches:
--         0m0.004s 0m0.000s
--         0m32.136s 0m2.372s
--     profiling:
--         total time  =        1.63 secs   (1632 ticks @ 1000 us, 1 processor)
--         total alloc = 596,173,024 bytes  (excludes profiling overheads)
-- with -O2:
--     time of 3 launches:
--         0m0.000s 0m0.004s
--         0m10.200s 0m0.124s
--     profiling:
--         total time  =        1.47 secs   (1467 ticks @ 1000 us, 1 processor)
--         total alloc = 466,592,968 bytes  (excludes profiling overheads)
-- with -O3:
--     time of 3 launches:
--         0m0.000s 0m0.004s
--         0m10.200s 0m0.112s
--     profiling:
--         total time  =        1.47 secs   (1466 ticks @ 1000 us, 1 processor)
--         total alloc = 466,592,968 bytes  (excludes profiling overheads)

strandsort xs = work [] xs []
    where
        merge' = merge (<)

        work []    []     acc  = reverse acc
        work ls    []     acc  = work [] (reverse $ merge' xs acc) []
        work ls (r:rs)     []  = work ls rs [r]
        work ls (r:rs) (a:acc) =
            if r > a then work ls rs $ a:acc
                     else work (a:ls) rs acc

-- without options:
--     time of 3 launches:
--         0m0.000s 0m0.004s
--         0m32.368s 0m2.204s
--     profiling:
--         total time  =        1.63 secs   (1630 ticks @ 1000 us, 1 processor)
--         total alloc = 596,173,024 bytes  (excludes profiling overheads)
-- with -O2:
--     time of 3 launches:
--         0m0.000s 0m0.004s
--         0m10.216s 0m0.112s
--     profiling:
--         total time  =        1.45 secs   (1453 ticks @ 1000 us, 1 processor)
--         total alloc = 466,592,968 bytes  (excludes profiling overheads)
-- with -O3:
--     time of 3 launches:
--         0m0.004s 0m0.000s
--         0m10.244s 0m0.088s
--     profiling:
--         total time  =        1.47 secs   (1469 ticks @ 1000 us, 1 processor)
--         total alloc = 466,592,968 bytes  (excludes profiling overheads)


merge_cps cmp after       []        rs  = after rs
merge_cps cmp after       ls        []  = after ls
merge_cps cmp after ls@(l:lt) rs@(r:rt) =
    if l `cmp` r then merge_cps cmp (after . (r:)) ls rt
                 else merge_cps cmp (after . (l:)) lt rs


mergesort_cps xs = work_cps id xs $ length xs
    where
        merge_cps' = merge_cps (>)

        work_cps after [ ] n = after [ ]
        work_cps after [x] n = after [x]
        work_cps after xs  n =
            let lsize   = n `div` 2
                rsize   = n - lsize
                (ls,rs) = splitAt lsize xs
            in work_cps (\ls' ->
                   work_cps (\rs' ->
                       merge_cps' after ls' rs'
                   ) rs rsize
               ) ls lsize

-- without options:
--     time of 3 launches:
--         0m0.004s 0m0.004s
--         0m45.892s 0m3.076s
--     profiling:
--         total time  =        2.39 secs   (2390 ticks @ 1000 us, 1 processor)
--         total alloc = 596,173,024 bytes  (excludes profiling overheads)
-- with -O2:
--     time of 3 launches:
--         0m0.008s 0m0.000s
--         0m14.308s 0m0.148s
--     profiling:
--         total time  =        2.09 secs   (2091 ticks @ 1000 us, 1 processor)
--         total alloc = 466,592,968 bytes  (excludes profiling overheads)
-- with -O3:
--     time of 3 launches:
--         0m0.008s 0m0.000s
--         0m11.820s 0m2.636s
--     profiling:
--         total time  =        2.09 secs   (2087 ticks @ 1000 us, 1 processor)
--         total alloc = 466,592,968 bytes  (excludes profiling overheads)

strandsort_cps xs = work [] xs []
    where
        merge_cps' = merge_cps (<)

        work []    []     acc  = reverse acc
        work ls    []     acc  = merge_cps' ((flip (work []) []) . reverse) xs acc
        work ls (r:rs)     []  = work ls rs [r]
        work ls (r:rs) (a:acc) =
            if r > a then work ls rs $ a:acc
                     else work (a:ls) rs acc

-- without options:
--     time of 3 launches:
--         0m0.008s 0m0.000s
--         0m44.380s 0m4.088s
--     profiling:
--         total time  =        2.29 secs   (2285 ticks @ 1000 us, 1 processor)
--         total alloc = 596,173,024 bytes  (excludes profiling overheads)
-- with -O2:
--     time of 3 launches:
--         0m0.004s 0m0.004s
--         0m14.348s 0m0.156s
--     profiling:
--         total time  =        2.09 secs   (2091 ticks @ 1000 us, 1 processor)
--         total alloc = 466,592,968 bytes  (excludes profiling overheads)
-- with -O3:
--     time of 3 launches:
--         0m0.008s 0m0.000s
--         0m14.316s 0m0.156s
--     profiling:
--         total time  =        2.08 secs   (2081 ticks @ 1000 us, 1 processor)
--         total alloc = 466,592,968 bytes  (excludes profiling overheads)


merge_cps_m cmp       []        rs  = return rs
merge_cps_m cmp       ls        []  = return ls
merge_cps_m cmp ls@(l:lt) rs@(r:rt) =
    if l `cmp` r
        then do
            processed <- merge_cps_m cmp ls rt
            return $ r:processed
        else do
            processed <- merge_cps_m cmp lt rs
            return $ l:processed


mergesort_cps_m xs = runCont (work_cps_m xs $ length xs) id
    where
        merge_cps_m' = merge_cps_m (>)

        work_cps_m [ ] n = return [ ]
        work_cps_m [x] n = return [x]
        work_cps_m xs  n =
            let lsize   = n `div` 2
                rsize   = n - lsize
                (ls,rs) = splitAt lsize xs
            in do ls' <- work_cps_m ls lsize
                  rs' <- work_cps_m rs rsize
                  merge_cps_m' ls' rs'

-- without options:
--     time of 3 launches:
--         0m0.008s 0m0.000s
--         0m46.232s 0m3.164s
--     profiling:
--         total time  =        2.33 secs   (2333 ticks @ 1000 us, 1 processor)
--         total alloc = 596,173,024 bytes  (excludes profiling overheads)
-- with -O2:
--     time of 3 launches:
--         0m0.004s 0m0.004s
--         0m14.432s 0m0.224s
--     profiling:
--         total time  =        2.10 secs   (2095 ticks @ 1000 us, 1 processor)
--         total alloc = 466,592,968 bytes  (excludes profiling overheads)
-- with -O3:
--     time of 3 launches:
--         0m0.004s 0m0.004s
--         0m14.512s 0m0.176s
--     profiling:
--         total time  =        2.10 secs   (2104 ticks @ 1000 us, 1 processor)
--         total alloc = 466,592,968 bytes  (excludes profiling overheads)

strandsort_cps_m xs = work [] xs []
    where
        merge_cps_m' = merge_cps_m (<)

        work []    []     acc  = reverse acc
        work ls    []     acc  = runCont (merge_cps_m' xs acc) $ (flip (work []) []) . reverse
        work ls (r:rs)     []  = work ls rs [r]
        work ls (r:rs) (a:acc) =
            if r > a then work ls rs $ a:acc
                     else work (a:ls) rs acc

-- without options:
--     time of 3 launches:
--         0m0.004s 0m0.000s
--         0m32.924s 0m2.184s
--     profiling:
--         total time  =        2.40 secs   (2395 ticks @ 1000 us, 1 processor)
--         total alloc = 596,173,024 bytes  (excludes profiling overheads)
-- with -O2:
--     time of 3 launches:
--         0m0.004s 0m0.004s
--         0m14.624s 0m0.144s
--     profiling:
--         total time  =        2.09 secs   (2089 ticks @ 1000 us, 1 processor)
--         total alloc = 466,592,968 bytes  (excludes profiling overheads)
-- with -O3:
--     time of 3 launches:
--         0m0.004s 0m0.004s
--         0m14.596s 0m0.180s
--     profiling:
--         total time  =        2.10 secs   (2100 ticks @ 1000 us, 1 processor)
--         total alloc = 466,592,968 bytes  (excludes profiling overheads)
