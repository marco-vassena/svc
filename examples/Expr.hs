-- This module contains an exmaple with arithmetic expressions
-- and variables.

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}

module Expr where

import Data.HList

import Format.Syntax hiding ((>>=), fail)
import Format.Combinator
import Format.Token.Char
import Format.Printer.Naive
import Format.Parser.Naive
import Format.Parser.Base

import qualified Control.Applicative as A
import Control.Monad
import Control.Isomorphism.Partial

import Util

-------------------------------------------------------------------------------
data Expr = Var String
          | Lit Int
          | BinOp Expr Bop Expr
  deriving Show

data Bop = Plus
         | Times
  deriving Show

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
bop :: (Use Satisfy c m Char, AlternativeC c m Char) => SFormat c m Char Bop
bop = plus <$> char '+' <|> times <$> char '*'

-- | A format surrounded by parenthesis.
parens :: (Use Satisfy c m Char, AlternativeC c m Char) 
       => Format c m Char xs -> Format c m Char xs
parens f = char '(' *> f <* char ')'

-- FIX : loop when printing variables that are not consistent
-- with the grammar, e.g. Var "1".
-- Note this definition relies on arbitrary backtracking when parsing.
expr :: (Use Satisfy c m Char, AlternativeC c m Char) => SFormat c m Char Expr
expr = exp 2
  where exp :: (Use Satisfy c m Char, AlternativeC c m Char) => Int -> SFormat c m Char Expr
        exp 0 =  var <$> some letter
             <|> lit <$> int
             <|> (parens expr)                 -- When printing this may not terminate.
        exp 1 = chainl1 (exp 0) bop (binOpPrio 1)
        exp 2 = chainl1 (exp 1) bop (binOpPrio 2)

-- | Succeeds only with the operators of the right priority.
binOpPrio :: Int -> Iso '[Expr, Bop, Expr] '[Expr]
binOpPrio n = binOp <.> subset s3 checkPrio
  where s3 = SCons (SCons (SCons SNil))
        checkPrio (Cons x (Cons op (Cons y _))) = priority op == n

--------------------------------------------------------------------------------

parseExpr :: Parser Char Expr
parseExpr = hHead A.<$> mkParser expr

printExpr :: Expr -> Maybe String
printExpr = mkPrinter expr . hsingleton

roundtrip :: String -> IO String
roundtrip s = do 
  e <- maybe (fail "Parser Failed") return (parseM parseExpr s)
  print e 
  maybe (fail "Printer Failed") return (printExpr e)

main :: IO ()
main = forever $ getLine >>= roundtrip >>= putStrLn
