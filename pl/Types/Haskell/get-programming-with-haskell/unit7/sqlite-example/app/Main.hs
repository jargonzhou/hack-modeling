module Main (main) where

import qualified Lib

-- Database actions
promptAndAddUser :: IO ()
promptAndAddUser = do
    putStrLn "Enter new user name"
    _userName <- getLine
    Lib.addUser _userName

promptAndCheckout :: IO ()
promptAndCheckout = do
    putStrLn "Enter the id of the user"
    _userId <- read <$> getLine
    putStrLn "Enter the id of the tool"
    _toolId <- read <$> getLine
    Lib.checkout _userId _toolId

promptAndCheckin :: IO ()
promptAndCheckin = do
    putStrLn "Enter the id of tool"
    _toolId <- read <$> getLine
    Lib.checkinAndUpdate _toolId

-- REPL
performCommand :: String -> IO ()
performCommand command
  | command == "users" = Lib.printUsers >> main
  | command == "tools" = Lib.printTools >> main
  | command == "adduser" = promptAndAddUser >> main
  | command == "checkout" = promptAndCheckout >> main
  | command == "checkin" = promptAndCheckin >> main
  | command == "in" = Lib.printAvailable >> main
  | command == "out" = Lib.printCheckedout >> main
  | command == "quit" = putStrLn "bye!"
  | otherwise = putStrLn "Sorry command not found" >> main

main :: IO ()
main = do
  putStr "> "
  command <- getLine
  performCommand command
