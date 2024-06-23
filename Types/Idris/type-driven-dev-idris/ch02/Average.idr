||| Module Average support calculating the average length of 
||| words in a string.
module Average

import Data.String -- words
import Data.List -- length

||| Calculate the average length of words in a string.
||| @str a string containning words separated by whitespace.
export -- export function
average : (str : String) -> Double
average str = let numWords = wordCount str
                  totalLength = sum (allLengths (words str))
              in cast totalLength / cast numWords
  where
    wordCount : String -> Nat
    wordCount str = length (words str)

    allLengths : List String -> List Nat
    allLengths str = map length str