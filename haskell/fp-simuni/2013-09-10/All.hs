minlist (x:xs) = foldl min x xs

minsum xs@(x:xt) = minimum $ zipWith (+) xs xt

rev = foldl (flip (:)) []

check cond = foldl (acc x -> acc || cond x) False

checkDifferent :: (Eq a) => [a] -> Bool
checkDifferent = fst . (foldl checker (True,[]))
    where
        checker (result,looked) x =
            if not result
                then (False,undefined)
                else (not $ x `elem` looked,x:looked)
