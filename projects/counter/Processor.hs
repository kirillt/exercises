module Processor where

import Common
import Money (Money(Zero), n, plus)

import Data.List
import Data.Tree
import Data.Function

import Data.Char
import Data.Text (pack, unpack, strip)

type Acc = (Forest Stats, Maybe (Name, Forest Stats))

process :: [Entry] -> Tree Stats
process = join "All" . work
  where
    work :: [Entry] -> Forest Stats
    work =
      raise . map plant .
      sortBy (compare `on` (\(_,x,_) -> x))

    plant :: Entry -> Tree Stats
    plant (d,n,m) = Node (Terminal n m d) []

    raise :: Forest Stats -> Forest Stats
    raise = finish . foldl' step base

    step :: Acc -> Tree Stats -> Acc
    step acc@(trees,curr) tree@(Node x _) =
      let new   = nonterminal (name x) in
      let fresh = Just (new,[tree])
      in  case curr of
            Nothing -> (trees, fresh)
            Just curr'@(old,xs) ->
              if old /= new then (finish acc, fresh)
                            else (trees, Just (old,tree:xs))

    base :: Acc
    base = ([], Nothing)

    join :: Name -> Forest Stats -> Tree Stats
    join name xs = Node (Nonterminal name $ total xs) xs

    finish :: Acc -> Forest Stats
    finish (trees, Nothing    ) = trees
    finish (trees, Just (n,xs)) = join n xs : trees

    total :: Forest Stats -> Money
    total = foldl' plus Zero . map (\(Node x _) -> amount x)

nonterminal :: Name -> Name
nonterminal = rules . unpack . strip . pack . map toLower
  where
    rules n = n
