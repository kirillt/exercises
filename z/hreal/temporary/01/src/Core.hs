import CommonConfig
import DefaultConfig
import TestModuleIface

main :: IO ()
main = main' defaultConfig

main' :: Config -> IO()
main' old@(Config path) = do
	putStrLn $ "===" ++ (show old) ++ "==="
	com <- getLine
	case com of
		"plug" ->  do
			newPath <- getLine
			main' (Config newPath)
		"quit" -> putStrLn "Bye."
		_      -> do
			testingFunction path
			main' old 
