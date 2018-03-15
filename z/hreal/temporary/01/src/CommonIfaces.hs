module CommonIfaces where

import System.Plugins

load' :: FilePath -> Symbol -> IO ()
load' p s = do
	r <- load p [] [] s
	case r of
		(LoadFailure e) -> putStrLn $ show e
		(LoadSuccess _m f) -> f
