import System.IO

getArgs :: IO [Integer]
getArgs = do
	rawArgs <- (getLine >>= return.words)
	return $ map (\s -> read s :: Integer) rawArgs

main = do
	as <- getArgs
	print as

data Cell = Letters String Integer | Numbers Integer Integer

lengthBase base number = ceiling $ logBase base number

invert ls@(Letters _ _) = toNumbers ls
invert ls@(Numbers _ _) = toLetters ls
toLetters (Numbers rows cols) = undefined
toNumbers (Letters rows cols) = undefined
