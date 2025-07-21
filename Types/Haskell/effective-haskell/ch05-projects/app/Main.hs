module Main where

import qualified MyLib (someFunc)

-- The entry point.
main :: IO ()
main = do
  putStrLn
     "Hello, Haskell!"
  MyLib.someFunc
