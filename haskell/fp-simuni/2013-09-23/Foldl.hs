myfoldl :: (a -> b -> a) -> a -> [b] -> a
myfoldl _ a    []  = a
myfoldl f a (x:xs) = myfoldl f (f a x) xs

myfoldr :: (b -> a -> a) -> a -> [b] -> a
myfoldr _ a    []  = a
myfoldr f a (x:xs) = f x (myfoldr f a xs)
