{-# OPTIONS_GHC -O -Wall #-}

module HReal.Client.Protocols
       (
         pack
       , module HReal.Ifaces.Vertex
       , module HReal.Ifaces.World_Client
       , module HReal.Ifaces.CtrlZ_Client
       , module HReal.Ifaces.Ifaces_Types
       ) where

import Thrift.Protocol.Binary
import Thrift.Transport.Handle

import HReal.Ifaces.Vertex
import HReal.Ifaces.World_Client
import HReal.Ifaces.CtrlZ_Client
import HReal.Ifaces.Ifaces_Types

pack :: Transport t => t -> (BinaryProtocol t, BinaryProtocol t)
pack handle = (BinaryProtocol handle, BinaryProtocol handle)
