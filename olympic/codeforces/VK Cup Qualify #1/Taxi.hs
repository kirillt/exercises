get :: IO [Int]
get = fmap ((map read) . words) getLine

main = do
    _      <- get
    groups <- fmap (foldr f (0,0,0,0)) get
    print $ t groups

f 1 (n1,n2,n3,n4) = (n1+1,n2  ,n3  ,n4  )
f 2 (n1,n2,n3,n4) = (n1  ,n2+1,n3  ,n4  )
f 3 (n1,n2,n3,n4) = (n1  ,n2  ,n3+1,n4  )
f 4 (n1,n2,n3,n4) = (n1  ,n2  ,n3  ,n4+1)

t (n1,n2,n3,n4)   = n4 + if n1 >= n3 then n3 + t' (n1 - n3) n2 else n3 + n2
t' n1 n2          = half $ (half n1) + n2

half x = ceiling $ (fromIntegral x) / 2
