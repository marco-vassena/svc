{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module Main where

import Prelude hiding ((>>=))
import Data.HList
import Format.Base
import Format.Combinator
import Format.Token
import Format.Parser
import Format.Parser.Naive
import Format.Printer
import Format.Printer.Naive

import System.Exit
import Test.HUnit.Base
import Test.HUnit.Text


-- An identifier is a non-empty sequence of letters
identifier :: (SatisfyChar c m, ManyChar c m) => Format c m Char '[[Char]]
identifier = some letter

parseId :: Parser Char String
parseId = parse1 (mkParser' identifier)

printId :: String -> Maybe String
printId s = mkPrinter' identifier (hsingleton s)

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
  zipWith (~=?) (map Just ids) (map (parseM parseId) ids) ++
  zipWith (~=?) (map Just ids) (map printId ids)

testFalseIds :: Test
testFalseIds = TestLabel "False Identifiers" $ TestList $
  zipWith (~=?) (repeat Nothing) (map (parseM parseId) notIds) ++
  zipWith (~=?) (repeat Nothing) (map printId notIds)

--------------------------------------------------------------------------------
-- 0 or more white space characters
spaces :: (SatisfyChar c m, ManyChar c m) => Format c m Char '[[Char]]
spaces = many space

parseSpaces :: Parser Char String
parseSpaces = parse1 (mkParser' spaces)

printSpaces :: String -> Maybe String
printSpaces s = mkPrinter' spaces (hsingleton s)

trueSpaces :: [String]
trueSpaces = ["", "\n\r", "\r\n", "\t", "\t\t ", " ", "  ", "\v\f"]

falseSpaces :: [String]
falseSpaces = ["a", "1", "§", "\f'", "\r+", " @!#", "##", "\n|", "\t-/\t"]

testTrueSpaces :: Test 
testTrueSpaces = TestLabel "True Spaces" $ TestList $
  zipWith (~=?) (map Just trueSpaces) (map (parseM parseSpaces) trueSpaces) ++
  zipWith (~=?) (map Just trueSpaces) (map printSpaces trueSpaces)

testFalseSpaces :: Test
testFalseSpaces = TestLabel "False Spaces" $ TestList $
  zipWith (~=?) (repeat Nothing) (map (parseM parseSpaces) falseSpaces) ++
  zipWith (~=?) (repeat Nothing) (map printSpaces falseSpaces)

--------------------------------------------------------------------------------
twoDigits :: (SatisfyChar c m, ManyChar c m) => Format c m Char '[[Char]]
twoDigits = count 2 digit

trueTwoDigits :: [String]
trueTwoDigits = [ x ++ y | x <- digs, y <- digs]
  where digs = map show [0 .. 9]

falseDigits :: [String]
falseDigits = ["", "a", " "] ++ [ show n | n <- [0 .. 9] ++ [100 .. 200] ++ [1000 .. 1100]]

parseTwoDigits :: Parser Char String
parseTwoDigits = parse1 (mkParser' twoDigits)

printTwoDigits :: String -> Maybe String
printTwoDigits s = mkPrinter' twoDigits (hsingleton s)

testTrueDigits :: Test
testTrueDigits = TestLabel "True Digits" $ TestList $
   zipWith (~=?) (map Just trueTwoDigits) (map (parseM parseTwoDigits) trueTwoDigits) ++
   zipWith (~=?) (map Just trueTwoDigits) (map printTwoDigits trueTwoDigits)

testFalseDigits :: Test
testFalseDigits = TestLabel "False Digits" $ TestList $
  zipWith (~=?) (repeat Nothing) (map (parseM parseTwoDigits) falseDigits) ++
  zipWith (~=?) (repeat Nothing) (map printTwoDigits falseDigits)

--------------------------------------------------------------------------------

-- Match 3 dots
dots :: (MatchChar c m, ManyC c m Char '[]) => Format c m Char '[]
dots = count 3 (char '.')

parseDots :: Parser Char (HList '[])
parseDots = mkParser' dots

printDots :: Maybe String
printDots = mkPrinter' dots Nil

trueDots :: String
trueDots = "..."

falseDots :: [String]
falseDots = ["", ".", "..", "...."]

testTrueDots :: Test
testTrueDots = TestLabel "True Dots" $ TestList $ [
 Just Nil ~=? parseM parseDots trueDots,
 Just trueDots ~=? printDots]

testFalseDots :: Test
testFalseDots = TestLabel "False Dots" $ TestList $
  zipWith (~=?) (repeat Nothing) (map (parseM parseDots) falseDots)

--------------------------------------------------------------------------------
-- Test Binding

-- Expect the char next to the first read
--formatCharSChar :: Format c m Char '[Char, Char]
--formatCharSChar = token >>= \(Cons c Nil) -> satisfy (== succ c)
--
--parseCharSChar :: Parser Char String
--parseCharSChar = do 
--  Cons c1 (Cons c2 _) <- mkParser' formatCharSChar
--  return [c1, c2]
--
--printCharSChar :: String -> Maybe String
--printCharSChar [c1, c2] = mkPrinter' formatCharSChar $ Cons c1 (Cons c2 Nil)
--printCharSChar _ = Nothing
--
--trueCharSChar :: [String]
--trueCharSChar = [ [c, succ c] | c <- ['0'..'z']]
--
--falseCharSChar :: [String]
--falseCharSChar =  [] : concat [ [[c], [c, c], [c, succ (succ c)], [c, pred c]] | c <- ['0'..'z']]
--
--testTrueBind :: Test
--testTrueBind = TestLabel "True Bind" $ TestList $
--  zipWith (~=?) (map Just trueCharSChar) (map (parseM parseCharSChar) trueCharSChar) ++
--  zipWith (~=?) (map Just trueCharSChar) (map printCharSChar trueCharSChar)
--
--testFalseBind :: Test
--testFalseBind = TestLabel "False Bind" $ TestList $ 
--  zipWith (~=?) (repeat Nothing) (map (parseM parseCharSChar) falseCharSChar) ++
--  zipWith (~=?) (repeat Nothing) (map printCharSChar falseCharSChar)

--------------------------------------------------------------------------------

comment :: (TokensChar c m, ManyChar c m, Use Seq c m Char '[String]) => SFormat c m Char String
comment = string "<!--" *> manyTill token (string "-->")

parseComment :: Parser Char String
parseComment = parse1 (mkParser' comment)

printComment :: String -> Maybe String
printComment = mkPrinter' comment . hsingleton

trueComments :: [String]
trueComments = [ start ++ cs ++ end | cs <- comments]
  where start = "<!--"
        end = "-->"

comments :: [String]
comments = ["", " ", "-", "foo--bar", "->", ">"]

falseComments :: [String]
falseComments = [ "", "<-->", "<!-->", "<!--foo", "<>", "-->", "<!-- foo-->bar"]

testTrueComment :: Test
testTrueComment = TestLabel "True Comments" $ TestList $
  zipWith (~=?) (map Just comments) (map (parseM parseComment) trueComments) ++
  zipWith (~=?) (map Just trueComments) (map printComment comments)

testFalseComment :: Test
testFalseComment = TestLabel "False Comments" $ TestList $
  zipWith (~=?) (repeat Nothing) (map (parseM parseComment) falseComments)
  -- printing never fails

--------------------------------------------------------------------------------

tests :: Test
tests = TestLabel "Format" $ TestList $ [
  TestLabel "Identifiers"  $ TestList [testTrueIds, testFalseIds],
  TestLabel "Spaces"       $ TestList [testTrueSpaces, testFalseSpaces],
  TestLabel "Digits"       $ TestList [testTrueDigits, testFalseDigits],
  TestLabel "Dots"         $ TestList [testTrueDots, testFalseDots],
--  TestLabel "Bind"         $ TestList [testTrueBind, testFalseBind],
  TestLabel "ManyTill"     $ TestList [testTrueComment, testFalseComment]
  ]

hasFailed :: Counts -> Bool
hasFailed (Counts c t e f) = e > 0 || f > 0

main :: IO ()
main = do
  c <- runTestTT tests
  if hasFailed c
    then exitFailure
    else return ()
