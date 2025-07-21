import           Data.Char                 (isPunctuation)
import           Data.Text                 as T
import           Lib                       (isPalindrome, preProcess)
import           Test.QuickCheck           (Args (chatty, maxSuccess),
                                            quickCheck, quickCheckWith, stdArgs,
                                            verboseCheckWithResult, Result(output))
import           Test.QuickCheck.Instances

-- Assertion hepler function.
assert :: Bool -> String -> String -> IO ()
assert test passStmt failedStmt = if test
  then putStrLn passStmt
  else putStrLn failedStmt

-- Property Testing with Quickcheck
prop_punctuationInvariant :: T.Text -> Bool
prop_punctuationInvariant text =
  preProcess text == preProcess noPuncText
  where noPuncText = T.filter (not . isPunctuation) text

main :: IO ()
main = do
  putStrLn "Running tests..."
  assert (isPalindrome "racecar") "passed 'racecar'" "FAIL: 'racecar'"
  assert (isPalindrome "racecar!") "passed 'racecar!'" "FAIL: 'racecar!'"
  assert ((not . isPalindrome) "cat") "passed 'cat'" "FAIL: 'cat'"
  putStrLn "tests done!"

  putStrLn "Running QuickCheck..."
  quickCheck prop_punctuationInvariant
  -- https://hackage.haskell.org/package/QuickCheck-2.14.3/docs/Test-QuickCheck.html
  quickCheckWith stdArgs {maxSuccess = 3, chatty = True} prop_punctuationInvariant
  -- with test cases output
  checkResult <- verboseCheckWithResult stdArgs {maxSuccess = 3, chatty = True} prop_punctuationInvariant
  putStrLn $ output checkResult
  putStrLn "QuickCheck done!"
