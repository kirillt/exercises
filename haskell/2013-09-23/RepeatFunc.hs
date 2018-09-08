repeatFunc :: (a -> a) -> Integer -> (a -> a)
repeatFunc f n = foldl (\acc _ -> acc . f) id [1..n]
