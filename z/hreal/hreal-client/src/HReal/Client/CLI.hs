{-# OPTIONS_GHC -O -Wall -fno-warn-missing-signatures #-}
{-# LANGUAGE OverloadedStrings #-}
module HReal.Client.CLI where

import Data.Map (toList)
import HReal.Client.Protocols

runClient world ctrlz = do
    putStr "$ "
    line@(h:s) <- getLine
    let request = if   h == '~'
                  then if   null s
                       then back ctrlz 0
                       else back ctrlz $ read s
                  else interpret world   line
    Response d m <- request
    case m of
        Nothing -> return  ()
        Just  t -> putStrLn t
    case d of
        Nothing -> return  ()
        Just  t -> printMap t
    runClient world ctrlz
    where
        printMap m = do
            putStr "[Result:"
            mapM_ prettyPrint $ toList $ decodeMap m
            putStr "]\n"
        prettyPrint (k,v) = putStr $ "\n\t\t" ++ show k ++ " -> " ++ show v
