{-# OPTIONS_GHC -O -Wall #-}
{-# LANGUAGE OverloadedStrings #-}


import Network
import Thrift.Server

import Prelude           hiding (map, fail, lookup, catch)
import Data.Map                 (map, Map)
import Data.IORef
import Data.Configurator hiding (empty)

import Control.Exception
import Control.Concurrent

import HReal.Ifaces.World as WR
import HReal.Ifaces.CtrlZ as CZ
import HReal.Ifaces.World_Iface
import HReal.Ifaces.CtrlZ_Iface
import HReal.Ifaces.Ifaces_Types

import HReal.Config ()
import HReal.Core.World
import HReal.Core.History
import HReal.Server.Interpreter as I

import HReal.Core.Vertex        as CV
import HReal.Ifaces.Vertex      as IV

main :: IO ()
main = do
    (config, _)                 <- autoReload autoConfig  [Required "config"]
    Just (PortNumber worldPort) <- lookup config "world" :: IO (Maybe PortID)
    Just (PortNumber ctrlzPort) <- lookup config "ctrlz" :: IO (Maybe PortID)
    server <- newIORef clean >>= return . Server
    _      <- forkIO $ runBasicServer server WR.process worldPort
    _      <- forkIO $ runBasicServer server CZ.process ctrlzPort
    putStrLn $ "Server started on ports: " ++ show [worldPort,ctrlzPort]

data Server = Server {
    history :: IORef History
}

instance World_Iface Server where
    interpret _       Nothing    = fail "No input."
    interpret server (Just code) = do
        let hRef = history server
        interpretation <- I.interpret code
        case interpretation of
            Left  e -> fail $ show e
            Right f -> do
                h <- readIORef $ hRef
                r <- evaluate  $ f h
                case r of
                    Left  c -> fail $ show c
                    Right w -> do
                        writeIORef hRef ((code,w):h)
                        good $! idToVertex w
        `catch`
        (fail . show :: SomeException -> IO Response)

instance CtrlZ_Iface Server where
    back _       Nothing     = fail "No input."
    back server (Just steps) = do
        let hRef  = history server
        modifyIORef hRef $ drop' $ fromIntegral steps
        ((c,w):_) <- readIORef hRef
        good' ("Last interpreted code: " ++ c) $! idToVertex w
        `catch`
        (fail . show :: SomeException -> IO Response)
        where
            drop' n   = adjust . drop n
            adjust [] = clean
            adjust xs = xs

fail   ::       String                     -> IO Response
fail     s = return $ Response  Nothing       $ Just s

good   ::       Map Id CV.Vertex           -> IO Response
good       = good''   Nothing

good'  ::       String -> Map Id CV.Vertex -> IO Response
good'  s   = good'' $ Just s

good'' :: Maybe String -> Map Id CV.Vertex -> IO Response
good'' s m = return $ Response (Just $ map encode m) s
