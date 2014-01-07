{-# OPTIONS_GHC -O -Wall #-}
{-# LANGUAGE OverloadedStrings #-}

import Network
import HReal.Config ()
import Data.Configurator
import Prelude hiding (lookup)
import Thrift.Transport.Handle

import System (getArgs)
import HReal.Client.Protocols
import qualified HReal.Client.CLI     as CLI
import qualified HReal.Client.GUI.GUI as GUI

main :: IO ()
main = do
    (config,    _) <- autoReload autoConfig [Required "config"]
    Just worldPort <- lookup config "world" :: IO (Maybe (HostName, PortID))
    Just ctrlzPort <- lookup config "ctrlz" :: IO (Maybe (HostName, PortID))
    runClient      <- fmap (getMethod.head) getArgs
    world          <- fmap pack $ hOpen worldPort
    ctrlz          <- fmap pack $ hOpen ctrlzPort
    runClient world ctrlz
    where
        getMethod "cli" = CLI.runClient
        getMethod "gui" = GUI.runClient
        getMethod  _    = const $ const $
            putStrLn "Mode must be specified (`cli` or `gui`)."
