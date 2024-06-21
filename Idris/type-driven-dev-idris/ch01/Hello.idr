-- Hello World of Idris.

module Main

main : IO ()
main = putStrLn "Hello, Idris World!"
-- main = putStrLn ?greeting -- holes: Main.greeting : String
-- main = putStrLn 'x' -- While processing right hand side of main. Can't find an implementation for FromChar String.
-- main = putStrLn (?convert 'x') -- Type At: Main.convert : Char -> String
-- Main> the String (cast 'x')
-- "x"
-- main = putStrLn (cast 'x') 
-- $ idris2 Hello.idr --exec main
-- x