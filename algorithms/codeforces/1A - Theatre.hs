import System.IO

getArgs :: IO [Double]
getArgs = do
	rawArgs <- (getLine >>= return.words)
	return $ map (\s -> read s :: Double) rawArgs

main = do
	[n,m,a] <- getArgs
	let na = ceiling (n / a)
	let ma = ceiling (m / a)
	print $ na*ma
