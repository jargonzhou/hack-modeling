module Lib
    ( isPalindrome
    , preProcess
    ) where

import qualified Data.Text as T
import Data.Char (isSpace, isPunctuation)

-- eta reduction
stripWhitespace :: T.Text -> T.Text
stripWhitespace = T.filter (not . isSpace)

stripPunctuation :: T.Text -> T.Text
stripPunctuation = T.filter (not . isPunctuation)

preProcess :: T.Text -> T.Text
preProcess = stripWhitespace . stripPunctuation . T.toLower

isPalindrome :: T.Text -> Bool
isPalindrome text = cleanText == T.reverse cleanText
    where cleanText = preProcess text
