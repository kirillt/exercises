import System.IO

main = do
    hSetBuffering stdin LineBuffering
    s <- getLine
    u <- getLine
    print $ distance s u

distance :: String -> String -> Int
distance s u = distance' (s, length s) (u, length u)
    where distance' (s,sl) (u,ul) = if sl > ul
                                    then distance'' (u,ul) (s,sl)
                                    else distance'' (s,sl) (u,ul)
          distance'' (s,sl) (u,ul) = if (sl < ul) then distance''' (ul - sl) (s++(replicate (ul - sl) 'a')) u
                                                  else distance''' 0 s u
          distance''' acc [] [] = acc
          distance''' acc (c:s) (d:u) = if c /= d then distance''' (acc+1) s u else distance''' acc s u

