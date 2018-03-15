import Common

import Scanner
import Processor
import Output

import System.Environment

main :: IO ()
main = do
  (file:opts) <- getArgs
  csv <- scan opts file
  output opts $ process csv
