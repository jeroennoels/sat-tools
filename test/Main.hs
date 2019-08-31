module Main (main) where

import Tools

main :: IO ()
main = sequence_ $ map putStrLn result

