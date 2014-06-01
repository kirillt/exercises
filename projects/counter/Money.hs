module Money where

import Data.Char
import Data.Text (pack, unpack, strip)

data Currency = USD | EUR | RUR
  deriving (Show,Eq)

instance Read Currency where
  readsPrec p = work . unpack . strip . pack . map toUpper
    where
      work (a:b:c:s) = work' (a:b:c:"") s
      work _ = []

      work' "RUR" s = [(RUR,s)]
      work' "USD" s = [(USD,s)]
      work' "EUR" s = [(EUR,s)]

currencies :: [String]
currencies = map show [USD,EUR,RUR]

data Money = Money {
  cur :: Currency,
  n   :: Double
} | Zero -- zero polymorphic on currency
  deriving (Show,Eq)

instance Read Money where
  readsPrec p s = do
    (n,s' ) <- readsPrec p s
    (c,s'') <- readsPrec p s'
    return (Money c n, s'')

cur2cur :: Money -> Currency -> Money
cur2cur (Money c1 d) c2 = Money c2 $ work c1 c2
  where
    work :: Currency -> Currency -> Double
    work RUR USD = d / 35
    work USD RUR = d * 35
    work RUR EUR = d / 47
    work EUR RUR = d * 47
    work EUR USD = d * 1.36
    work USD EUR = d / 1.36
    work x y | x == y = d
cur2cur Zero _ = Zero

plus :: Money -> Money -> Money
plus Zero r = r
plus l Zero = l
plus l r = Money (curOf l r) $ n l + n r
  where
    curOf :: Money -> Money -> Currency
    curOf (Money cl _) (Money cr _) | cl == cr = cl
