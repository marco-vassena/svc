-- This module contains an exmaple with arithmetic expressions
-- and variables.

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module Expr where

import Data.HList

import Format.Syntax hiding ((>>=), fail)
import Format.Combinator
import Format.Token.Char
import Format.Printer.Naive
import Format.Parser.UU
import qualified Format.Parser.Naive as N
import Format.Parser.Base

import qualified Control.Applicative as A
import Control.Monad
import Control.Isomorphism.Partial hiding (foldr)


import Text.ParserCombinators.UU.Utils
import Text.ParserCombinators.UU.BasicInstances
import Util

-------------------------------------------------------------------------------
data Expr = Var String
          | Lit Int
          | BinOp Expr Bop Expr
  deriving (Show, Eq)

data Bop = Plus
         | Times
  deriving (Show, Eq)

--------------------------------------------------------------------------------
-- Expr isomorphisms
--------------------------------------------------------------------------------
var :: CIso '[String] Expr 
var = iso (\(Cons s _) -> Var s) proj (SCons SNil)
  where proj (Var s) = Just $ Cons s Nil
        proj _ = Nothing

lit :: CIso '[Int] Expr 
lit = iso (\(Cons i _) -> Lit i) proj (SCons SNil)
  where proj (Lit i) = Just $ Cons i Nil
        proj _ = Nothing

binOp :: CIso '[Expr, Bop, Expr] Expr 
binOp = iso from to (SCons (SCons (SCons SNil)))
  where from :: HList '[Expr, Bop, Expr] -> Expr
        from (Cons e1 (Cons op (Cons e2 _))) = BinOp e1 op e2
        to (BinOp e1 op e2) = Just $ Cons e1 $ Cons op $ Cons e2 Nil
        to _ = Nothing

--------------------------------------------------------------------------------
-- Bop isomorphisms
--------------------------------------------------------------------------------
plus :: CIso '[] Bop 
plus = iso (\_ -> Plus) proj SNil
  where proj Plus = Just Nil
        proj _ = Nothing

times :: CIso '[] Bop 
times = iso (\_ -> Times) proj SNil
  where proj Times = Just Nil
        proj _ = Nothing


--------------------------------------------------------------------------------

-- | Prioritize the operators
priority :: Bop -> Int
priority Times = 1
priority Plus = 2

-- Format c that recognizes binary operators
bop :: (Use Help c m Char, Use Satisfy c m Char, AlternativeC c m Char) => SFormat c m Char Bop
bop = plus <$> char '+' <|> times <$> char '*'

-- | A format surrounded by parenthesis.
parens :: (Use Satisfy c m Char, AlternativeC c m Char, Use Help c m Char) 
       => Format c m Char xs -> Format c m Char xs
parens f = char '(' *> f <* char ')'


expr :: (Use Help c m Char, 
         Use Satisfy c m Char, AlternativeC c m Char) => SFormat c m Char Expr
expr = foldr gen fact [('+', plus), ('*', times)]

gen :: (AlternativeC c m Char, Use Satisfy c m Char, Use Help c m Char)
    => (Char, Iso '[] '[Bop]) -> SFormat c m Char Expr -> SFormat c m Char Expr
gen (c, i) f = chainl1 f (i <$> char c) checkBinOp 
  where checkBinOp = binOp <.> (identity (SCons SNil) *** iff i *** identity (SCons SNil))

-- FIX : loop when printing variables that are not consistent
-- with the grammar, e.g. Var "1".
-- Note this definition relies on arbitrary backtracking when parsing.
fact :: (Use Satisfy c m Char, 
         Use Help c m Char, 
         AlternativeC c m Char) => SFormat c m Char Expr
fact =  var <$> some letter
    <|> lit <$> int
    <|> parens expr                 -- When printing this may not terminate.

--------------------------------------------------------------------------------

parseExpr :: Parser Expr
parseExpr = hHead A.<$> mkParser expr

parseNExpr :: N.Parser Char Expr
parseNExpr = hHead A.<$> mkParser expr

printExpr :: Expr -> Maybe String
printExpr = mkPrinter expr . hsingleton

roundtrip :: String -> IO String
roundtrip s = do 
  let e = runParser "" parseExpr s
  print e 
  maybe (fail "Printer Failed") return (printExpr e)

main :: IO ()
main = forever $ getLine >>= roundtrip >>= putStrLn
