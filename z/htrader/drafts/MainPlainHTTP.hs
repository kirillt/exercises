import Data.HMAC
import Data.Word (Word8)
import Data.Digest.SHA512
import Numeric (showHex)

import Network.URI  hiding (query)
import Network.HTTP

import Secret

main = undefined

getInfo n = do
    result <- simpleHTTP $ btceRequest [getInfoKV, nonceKV n]
    print result

getInfoKV      = ("method","getInfo")
transHistoryKV = ("method","transHistory")
tradeHistoryKV = ("method","tradeHistory")
cancelOrderKV  = ("method","cancelOrder")
orderListKV    = ("method","orderList")
tradeKV        = ("method","trade")

nonceKV      n = ("nonce" , show n)

-- Request sending

btceRequest :: [(String,String)] -> Request String
btceRequest kvs = Request {
          rqURI     = uri {uriQuery = query kvs}
        , rqMethod  = POST
        , rqHeaders = btceHeaders kvs
        , rqBody    = "" }
    where
        btceHeaders kvs = [
              mkHeader HdrContentType "application/x-www-form-urlencoded"
            , mkHeader (HdrCustom "Key" ) apikey
            , mkHeader (HdrCustom "Sign") btceSign ]
        btceSign = encipher $ query kvs

-- Low-level details

uri :: URI
uri = URI "http:" (Just $ URIAuth "" "btc-e.com" "") "/tapi" "" ""

query :: [(String,String)] -> String
query = ('?':) . glue . (map entry)
    where
        glue   kvs  = concat $ (map (++"&") $ init kvs) ++ [last kvs]
        entry (k,v) = k ++ ('=':v)

headers :: [(String,String)] -> [Header]
headers = map (\(k,v) -> mkHeader (HdrCustom k) v)

encipher :: String -> String
encipher msg = bytes2string $ hmac (HashMethod hash 128) secret' msg'
    where
        toWord8 = map (fromIntegral . fromEnum)
        secret' = toWord8 secret
        msg'    = toWord8 msg

        bytes2string = concat . map (flip showHex "") 
