import Data.HMAC
import Data.Word (Word8)
import Data.Digest.SHA512
import Numeric (showHex)

import Prelude hiding (putStrLn)
import Data.ByteString (ByteString)
import qualified Data.ByteString as B (pack)
import Data.ByteString.Char8 (pack)
import Data.ByteString.Lazy.Char8 (putStrLn)

import Data.Conduit
import Network.HTTP.Conduit
import Network.HTTP.Types.Header
import Data.CaseInsensitive (CI, mk)
import Control.Monad.IO.Class (liftIO)

import Secret

main = undefined

getInfo :: Integer -> IO ()
getInfo n = runResourceT $ do
    manager <- liftIO $ newManager def
    result  <- httpLbs (btceRequest [getInfoKV, nonceKV n]) $ manager
    liftIO $ do
        print $ btceRequest [getInfoKV, nonceKV n]
        putStrLn $ responseBody result
        closeManager manager

getInfoKV      = ("method","getInfo")
transHistoryKV = ("method","transHistory")
tradeHistoryKV = ("method","tradeHistory")
cancelOrderKV  = ("method","cancelOrder")
orderListKV    = ("method","orderList")
tradeKV        = ("method","trade")

nonceKV      n = ("nonce" , show n)

btceRequest :: [(String,String)] -> Request m
btceRequest kvs = def {
          secure         = True
        , method         = pack $ "POST"
        , host           = pack $ "btc-e.com"
        , path           = pack $ "/tapi"
        , queryString    = pack $ query kvs
        , requestHeaders = btceHeaders kvs
        }
    where
        btceHeaders kvs = [ ( hContentType   , pack $ "application/x-www-form-urlencoded")
                          , ((hCustom "Key" ), pack $ apikey  )
                          , ((hCustom "Sign"), {-pack $-} btceSign)
                          ]
        btceSign = encipher $ query kvs
        hCustom  = mk . pack

        query :: [(String,String)] -> String
        query = ('?':) . glue . (map entry)
            where
                glue   kvs  = concat $ (map (++"&") $ init kvs) ++ [last kvs]
                entry (k,v) = k ++ ('=':v)

        encipher :: String -> ByteString --String
        encipher msg = bytes2string $ hmac (HashMethod hash 128) secret' msg'
            where
                toWord8 = map (fromIntegral . fromEnum)
                secret' = toWord8 secret
                msg'    = toWord8 msg

                bytes2string = B.pack --concat . map (flip showHex "") 
