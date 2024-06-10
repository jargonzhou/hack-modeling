||| Invoke module Average.
module Main

import System.REPL -- repl
import Average


||| showAverage show average length of words in a string.
showAverage : String -> String
showAverage str = "The average word length is: " ++ show (average str) ++ "\n"

main : IO()
main = repl "Enter a string: " showAverage