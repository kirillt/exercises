module Output where

import Common
import Money (Money, num)
import Time.Time (fromUnixTime)

import Data.Text (pack)
import Data.Tree
import Data.Word
import Data.List
import Data.Maybe
import Data.Function
import Data.Foldable (foldMap)

import Data.Tree.Pretty
import Graphics.EasyPlot
import Control.Applicative

import Debug.Trace

output :: [String] -> Tree Stats -> IO ()
output opts result | "plot"     `elem` opts = draw    result
output opts result | "vertical" `elem` opts = output' drawVerticalTree result
output opts result                          = output' drawTree         result

output' :: (Tree String -> String) -> Tree Stats -> IO ()
output' drawer result = putStrLn $ drawer $ show <$> result

type Point = (Time,Money) -- x=time and y=money
type Desc  = (Name,Money) -- total money for color generation
type Fiber = (Desc,[Point])

draw :: Tree Stats -> IO ()
draw result = do
  let graphs = prepare result
  success <- plot' [Debug] (PNG "plot.png") graphs
  putStrLn $ "Plot building of " ++ show (length graphs) ++ " suceeded: " ++ show success
    where
      prepare :: Tree Stats -> [Graph2D Double Double]
      prepare = reverse . map graph . fibration

      graph :: Fiber -> Graph2D Double Double
      graph ((n,m),ps) = main $ map convert ps
        where
          main :: [(Double,Double)] -> Graph2D Double Double
          main ps = let ps' = sortBy (compare `on` fst) ps in
                    let r   = listToMaybe $ reverse ps' in
                    let l   = listToMaybe           ps' in
                    let range = case (l,r) of { (Just l', Just r') ->
                      [Range (fst l') (fst r')] ; _ -> [] }
                    in  Data2D [Style Lines, Title n, Color $ color n] range ps'

          color :: Name -> Color
          color n | n == "@all"      = RGB 192 192 192
          color n | n == "@positive" = RGB 64  192 128
          color n | n == "@negative" = RGB 192 64  128
          color _ = RGB r g b
            where
              norma :: Double -> Double
              norma x = x * 127 / 800000

              m' :: Double
              m' = num m

              r = min 255 $ max 0 $ round (128 + norma (negate m'))
              g = min 255 $ max 0 $ round (192 + norma m')
              b = (239 * length n) `mod` 255

          convert :: (Time,Money) -> (Double,Double)
          convert (t,m) = (fromIntegral $ fromUnixTime t, num m)

      fibration :: Tree Stats -> [Fiber]
      fibration = catMaybes . work [] . (:[])
        where
          work acc (t@(Node _ xs):ts) = work (fiber t : acc) $ xs ++ ts
          work acc [] = acc

      fiber :: Tree Stats -> Maybe Fiber
      fiber (Node (Nonterminal n m) xs) = Just ((n,m), concatMap (foldMap extract) xs)
        where
          extract :: Stats -> [Point]
          extract (Terminal _ m t) = [(t,m)]
          extract _ = []
      fiber _ = Nothing
