module Main where

import Test.HUnit
import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)

import Hack

main = defaultMain tests

tests :: [TF.Test]
tests
 =  [ testCase "1+1=2" (1+1 @?= 2)
    , testCase "hack" (hack @?= "hacking Flash.prism")
    ]
