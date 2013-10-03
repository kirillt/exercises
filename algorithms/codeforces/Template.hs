import System.IO

getArgs :: IO [Integer]
getArgs = do
	rawArgs <- (getLine >>= return.words)
	return $ map (\s -> read s :: Integer) rawArgs

main = do
	as <- getArgs
	print as
