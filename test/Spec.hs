import Control.Applicative
import Data.Char
import LambdaCalculusEssentials
import Parser
import Test.Hspec
import Test.Tasty
import Test.Tasty.QuickCheck

alpha               = ['a' .. 'z']
num                 = ['0' .. '9']
alphaNum            = alpha ++ num
apostrophe          = ['\'']
alphaNumApostrophe = alphaNum ++ apostrophe

acceptableVar :: Gen String
acceptableVar = liftA2 (:) (elements alpha) . listOf $ elements alphaNumApostrophe

instance Arbitrary LambdaTerm where
  arbitrary = oneof [ Var <$> acceptableVar
                    , liftA2 (:@:) arbitrary arbitrary
                    , liftA2 L acceptableVar arbitrary
                    ]

main :: IO ()
main = {-hspec $ do
    describe "Basic combinator tests" $ do
        it "SKK-combinator is I-combinator" $ do
            (reduce skk =@= i) `shouldBe` True-}
       defaultMain . testProperty "Test" . withMaxSuccess 5 $ \x -> parse (show x) == x
