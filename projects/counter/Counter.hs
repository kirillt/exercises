import Scanner

import System.Environment

main :: IO ()
main = do
  (file:opts) <- getArgs
  csv <- scan file opts
  print csv
