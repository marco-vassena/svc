{-# LANGUAGE FlexibleContexts #-}

-- Tests the NetPbm format with real examples.
-- In particular checks whether the parser is different from the printer.

module Main where

import Data.Functor.Identity
import Data.List
import Data.ByteString (ByteString)

import qualified Data.ByteString as B
import System.Directory
import System.Exit
import System.IO
import Test.HUnit

import Text.Parsec

import NetPbm hiding (main)
import Utility
import Debug.Trace

parse' :: Stream s Identity Char => Parsec s () a -> FilePath -> s -> a
parse' p name content =
 case parse p name content of
  Left s -> error (show s)
  Right a -> a

checkPbm :: Stream ByteString Identity Char => FilePath -> ByteString -> Test
checkPbm name content = expected ~=? actual
  where expected = parse' pbmParser name content
        printed = printWith pbmPrinter expected
        actual = parse' pbmParser "stdin" printed

getFileAndContent :: FilePath -> IO [(FilePath, ByteString)]
getFileAndContent dir = do
  files <- getDirectoryContents dir >>= return . map (dir ++) . filter (".pbm" `isSuffixOf`)
  contents <- mapM B.readFile files
  return (zip files contents)

mkTests :: IO Test
mkTests = do
  nc <- getFileAndContent "data/ascii-pbm/"
  return $ TestList [TestLabel name (checkPbm name content) | (name, content) <- nc]

main :: IO ()
main = do
  tests <- mkTests
  c <- runTestTT tests
  if hasFailed c
    then exitFailure
    else return ()
