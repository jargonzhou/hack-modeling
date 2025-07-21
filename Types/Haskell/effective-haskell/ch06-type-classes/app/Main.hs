module Main where

import qualified MyLib (someFunc)
import qualified NaturalClass

main :: IO ()
main = do
  putStrLn "Hello, Haskell!"
  MyLib.someFunc

  print $ NaturalClass.add (1 :: Int) (2 :: Int)
