{-# OPTIONS_GHC -O -Wall -fno-warn-orphans #-}
{-# LANGUAGE FlexibleInstances #-}
module HReal.Config where

import Network

import Data.Ratio
import Data.Maybe
import Data.Configurator
import Data.Configurator.Types

instance Configured a   => Configured [Maybe a] where
    convert (List   vs) = Just $ map convert vs
    convert _           = Nothing

instance Configured PortID where
    convert (Number  p) = Just $ PortNumber $ fromIntegral $ numerator p
    convert _           = Nothing  

lookupJust :: Configured a => Config -> Name -> IO (Maybe [a])
lookupJust  config name = do
    things <- Data.Configurator.lookup config name
    return $ things >>=
        Just . (map fromJust) . (filter isJust)
