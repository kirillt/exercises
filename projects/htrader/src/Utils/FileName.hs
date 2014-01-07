{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Utils.FileName where

import Data.Serialize         as Cereal
import Data.ByteString.Char8  as ByteString (pack, unpack)
import Data.ByteString.Base64 as Base64 (encode, decode)

class FileName a where
    toFileName   :: a -> FilePath
    fromFileName :: FilePath -> Maybe a

instance Serialize a => FileName a where
    toFileName = ByteString.unpack . Base64.encode . Cereal.encode
    fromFileName f = convert $ (Base64.decode $ ByteString.pack f) >>= Cereal.decode
        where
            convert (Left  _) = Nothing
            convert (Right x) = Just x
