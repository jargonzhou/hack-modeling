-- |
-- This modules serves as a demonstration.
module MyLib (someFunc) where

{- |
A Function output something.

>>> someFunc
someFunc
-}
someFunc :: IO ()
someFunc = putStrLn "someFunc"
