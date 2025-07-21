-- |
-- A example type class for natural numbers.
module NaturalClass where

class Natural n where
    -- | Equality
    equal :: n -> n -> Bool
    -- | Addition
    add :: n -> n -> n
    -- | Multiplication
    multiply :: n -> n -> n
    -- | The unit element of addition
    additiveIdentity :: n
    -- | The unit element of multiplication
    multiplicativeIdentity :: n
    -- | The string representation
    displayAsString :: n -> String

instance Natural Int where
    equal = (==)
    add = (+)
    multiply = (*)
    additiveIdentity = 0
    multiplicativeIdentity = 1
    displayAsString = show
