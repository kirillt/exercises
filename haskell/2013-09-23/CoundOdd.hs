countOdd  :: [Integer] -> Integer
countOdd  = foldr (\k s -> if k `mod` 2 == 1 then s + 1 else s) 0

countOdd1 :: [Integer] -> Integer
countOdd1 = sum . map (`mod` 2)
