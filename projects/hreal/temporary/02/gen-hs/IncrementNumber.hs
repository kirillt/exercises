import System
import Network
import Data.Int
import Interfaces_Types
import Incrementor_Client
import Thrift.Transport.Handle
import Thrift.Protocol.Binary

ioProtocols handle = (BinaryProtocol handle, BinaryProtocol handle)

main = do
    arg:_ <- getArgs
    handle <- hOpen ("localhost", PortNumber 7911)
    res   <- inc (ioProtocols handle) (read arg :: Int32)
    putStrLn $ arg ++ " + 1 = " ++ (show res)
