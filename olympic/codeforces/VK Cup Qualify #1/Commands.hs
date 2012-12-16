import Data.List (intersperse)

import System.IO

main = do
    n <- fmap read getLine
    interpret n [] []

split curr  ""          = curr
split curr (    '/':ts) = split       curr  ts
split curr ('.':'.':ts) = split (tail curr) ts
split curr           s  = let (h,ts) = break (=='/') s in split (h:curr) ts

path [] = "/"
path xs = '/':(concat $ reverse $ "/":(intersperse "/" xs))

interpret 0 _    output = mapM_ putStrLn $ reverse output
interpret n curr output = do
    (command:arg) <- fmap words getLine
    case command of
        "pwd" -> interpret (n-1) curr $ (path curr):output
        "cd"  -> let [path@(first:_)] = arg in
                 if   first == '/'
                 then interpret (n-1) (split []   path) output
                 else interpret (n-1) (split curr path) output
