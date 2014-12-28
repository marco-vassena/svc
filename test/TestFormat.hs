{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Main where

import Data.HList
import Format.Base
import Format.Combinator
import Format.Token
import Format.Parser
import Format.Parser.Naive

import System.Exit
import Test.HUnit.Base
import Test.HUnit.Text


-- Simple dummy formats

identifier :: Format m Char '[[Char]]
identifier = some letter

pIdentifier :: Parser Char String
pIdentifier = parse1 (mkParser identifier)

notIds :: [String]
notIds = ["", "1234", "abc1", "foo ", " bar", "~a"]

ids :: [String]
ids = ["a", "bc", "A", "foo", "bar"]

parse1 :: Parser i (HList '[ a ]) -> Parser i a
parse1 p = do
  (Cons x _) <- p
  return x

testTrueIds :: Test 
testTrueIds = TestLabel "True Identifiers" $ TestList $
  zipWith (~=?) (map Just ids) (map (parseM pIdentifier) ids)

hasFailed :: Counts -> Bool
hasFailed (Counts c t e f) = e > 0 || f > 0

main :: IO ()
main = do
  c <- runTestTT testTrueIds
  if hasFailed c
    then exitFailure
    else return ()
