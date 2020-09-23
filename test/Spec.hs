module Spec where

import Test.Hspec
import LambdaCalculusEssentials

main :: IO ()
main = hspec $ do
    describe "Basic combinator tests" $ do
        it "SKK-combinator is I-combinator" $ do
            (reduce skk =@= i) `shouldBe` True
