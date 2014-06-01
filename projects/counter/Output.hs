module Output where

import Common

import Data.Tree
import Data.Tree.Pretty
import Control.Applicative

output :: [String] -> Tree Stats -> IO ()
output opts result | "vertical" `elem` opts = draw drawVerticalTree result
output opts result                          = draw drawTree         result

draw :: Show a => (Tree String -> String) -> Tree a -> IO ()
draw drawer result = putStrLn $ drawer $ show <$> result
