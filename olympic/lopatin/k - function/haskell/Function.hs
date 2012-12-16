import Data.Map hiding (map)
import Prelude  hiding (lookup)

r :: Integer
r = 2^32

main :: IO ()
main = do
    argument <- fmap (read::String->Integer) $ readFile "function.in"
    writeFile "function.out" $ show $ solve argument

solve :: Integer -> Integer
solve n = f' n
    where
        cache = fromList [(x, f x) | x <- [1..n]]
        f' x  = cache ! x
        f  x  = if   x <= 2
                then 1
                else if   even x
                     then ((f' $ x-1        ) + (f' $ x-3        )) `mod` r
                     else ((f' $ 6*x `div` 7) + (f' $ 2*x `div` 3)) `mod` r