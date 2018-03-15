



import qualified Test.World as World

main = testAll $ concat [World.cases]

testAll cases = if null result
              then putStrLn   "Ok."
              else putStrLn $ "Failed: " ++ show result
    where result = findFailed cases

findFailed xs = find' [] 1 (==False) xs where
    find' acc _ p [] = reverse acc
    find' acc i p (x:xs) = 
        if p x then find' (i:acc) (i+1) p xs
               else find'    acc  (i+1) p xs
