import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "All tests"
  [ unitTests 
  , propertyTests
  ]

unitTests :: TestTree
unitTests = testGroup "Unit tests"
    [ testCase "2+2=4" $
        2+2 @?= 4
    ]

propertyTests :: TestTree
propertyTests = testGroup "Property tests"
    [ testProperty "even + odd = odd" propertyEvenOdd
    ]

propertyEvenOdd :: Int -> Int -> Property
propertyEvenOdd x y = even x && odd y ==> odd (x + y)
