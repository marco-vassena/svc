{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}

module NetPbm where

import Prelude hiding ((>>=), return)
import qualified Prelude as P
import Control.Isomorphism.Partial
import qualified Control.Applicative as A
import qualified Control.Monad as M
import Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as B
import Data.TypeList.HList
import Data.List
import Data.Word

import Format.Syntax hiding (fail)
import Format.Combinator
import Format.Token
import Format.Parser
import Format.Parser.GParser
import Format.Parser.Parsec
import Format.Printer.Naive

import Text.Parsec (Parsec, eof, parse)

whitespace :: (FormatC c m, AlternativeC c m Char) 
            => Format c m Char '[]
whitespace = some (char ' ' <|> tab  <|> newline <|> comment)

-- | Recognizes a comment and discards its value. 
comment :: (AlternativeC c m Char, FormatC c m)
        => Format c m Char '[]
comment = ignore (hsingleton []) <$> cm
  where cm = char '#' *> manyTill (satisfy (/= '\n')) newline

--------------------------------------------------------------------------------
data Pbm = Pbm Int Int [[Char]]
  deriving (Show, Eq)

-- | Partial isomorphism for 'Pbm'
pbm :: Iso '[Int, Int, [[Char]]] '[Pbm]
pbm = Iso (hsingleton . happly Pbm) f (SCons (SCons (SCons SNil))) (SCons SNil)
  where f :: HList '[Pbm] -> Maybe (HList '[Int, Int, [[Char]]])
        f (Cons (Pbm n m img) _) = Just $ Cons n (Cons m (Cons img Nil))
--------------------------------------------------------------------------------

-- | Format that targets the 'Pbm' data type.
pbmFormat :: (MonadC c m Char,
              FormatC      c m     ,
              AlternativeC c m Char) 
          => SFormat c m Char Pbm
pbmFormat = pbm <$> pbmRawFormat

-- | Format that recognizes the essential elements of a pbm image.
pbmRawFormat :: (MonadC c m Char,
                 FormatC      c m     ,
                 AlternativeC c m Char) 
             => Format c m Char '[Int, Int, [[Char]]]
pbmRawFormat = pbmHeader >>= \(Cons n (Cons m _)) -> img n m

-- | Recognizes the pbm header and the dimensions of the image
pbmHeader :: (AlternativeC c m Char, FormatC c m ) 
          => Format c m Char '[Int, Int]
pbmHeader = (string "P1" *> whitespace *> integer <* whitespace) <*> integer <* whitespace 

-- | Recognizes a table of space-separated bits 
img :: (FormatC c m, AlternativeC c m Char) 
    => Int -> Int -> SFormat c m Char [[Char]]
img n m = count n (count m (bit <* whitespace))
  where bit = oneOf "01"

--------------------------------------------------------------------------------

pbmParser :: Parsec ByteString () Pbm
pbmParser = hHead A.<$> (mkParser pbmFormat) A.<* eof

pbmPrinter :: Pbm -> Maybe ByteString
pbmPrinter = mkPrinter pbmFormat . hsingleton

-- | Parse the input and prints the resulting Pbm, then it serializes it again.
roundtrip :: ByteString -> IO ByteString
roundtrip s = do 
  case parse pbmParser "" s of
    Left e -> fail (show e) 
    Right p -> print p >> maybe (fail "Printer Failed") P.return (pbmPrinter p)

test :: String -> IO ()
test s = B.readFile s M.>>= roundtrip M.>>= B.putStrLn

main :: IO ()
main = M.forever $ getLine M.>>= test
