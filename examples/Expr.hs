-- This module contains an exmaple with arithmetic expressions
-- and variables.

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Expr where

import Data.HList

import Format.Base
import Format.Combinator
import Format.Char
import Format.Parser.Naive
import Format.Printer.Naive

import Control.Isomorphism.Partial

import qualified Text.Parsec.Char as C
import qualified Control.Applicative as A
import qualified Text.Parsec.String as S
import qualified Text.Parsec.Prim as P
import Text.Parsec.Combinator (many1)
import qualified Text.Parsec.Combinator as PC

import Debug.Trace
import System.IO
import System.IO.Unsafe

-- Move this to char module
int :: SFormat m Char Int
int = i <$> some digit
  where i :: Iso '[String] '[Int] 
        i = Iso f g (SCons SNil) (SCons SNil)
          where f :: HList '[ String ] -> Maybe (HList '[Int])
                f (Cons s _) = Just . hsingleton $ read s
                g :: HList '[ Int ] -> Maybe (HList '[String])
                g (Cons n _) = Just . hsingleton $ show n
 

data Expr = Var String
          | Lit Int
          | BinOp Expr Bop Expr
  deriving Show

data Bop = Plus
         | Times
  deriving Show

-- Bop isomorphisms
plus :: CIso '[] Bop 
plus = iso (\_ -> Plus) proj SNil
  where proj Plus = Just Nil
        proj _ = Nothing

times :: CIso '[] Bop 
times = iso (\_ -> Times) proj SNil
  where proj Times = Just Nil
        proj _ = Nothing

-- Format that recognizes binary operators
bop :: SFormat m Char Bop
bop = plus <$> char '+' <|> times <$> char '*'

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

priority :: Bop -> Int
priority Times = 1
priority Plus = 2

parens :: Format m Char xs -> Format m Char xs
parens f = char '(' @> f <@ char ')'

-- FIX : printing lobop for variables that are not consistent
-- with the syntax, e.g. Var "1".
expr :: SFormat m Char Expr
expr = exp 2
  where exp 0 =  var <$> some letter
             <|> lit <$> int
             <|> (parens expr)                 -- When printing this may not terminate.
        exp 1 = chainl1 (exp 0) bop (binOpPrio 1)
        exp 2 = chainl1 (exp 1) bop (binOpPrio 2)

fTimes :: SFormat m Char Bop
fTimes = times <$> char '*'

binOpPrio :: Int -> Iso '[Expr, Bop, Expr] '[Expr]
binOpPrio n = binOp <.> subset s3 checkPrio
  where s3 = SCons (SCons (SCons SNil))
        checkPrio (Cons x (Cons op (Cons y _))) = priority op == n

input :: String
input = "1+2"

-- The same in plain parsec
pExpr :: S.Parser Expr
pExpr = exp 2 where
  exp 0 =   Var A.<$> many1 C.letter
     A.<|> (Lit . read A.<$> many1 C.digit)
     A.<|> (C.char '(' A.*> pExpr A.<* C.char ')')
  exp 1 = PC.chainl1 (exp 0) pPlus 
  exp 2 = PC.chainl1 (exp 1) pTimes

pPlus :: S.Parser (Expr -> Expr -> Expr)
pPlus = C.char '*' A.*> return (\e1 e2 -> BinOp e1 Times e2)
 
pTimes :: S.Parser (Expr -> Expr -> Expr)
pTimes = C.char '+' A.*> return (\e1 e2 -> BinOp e1 Plus e2)

--(P.try pBase) A.<|> pRec
-- where pBase = (Var A.<$> many1 C.letter)
--          A.<|> (Lit . read A.<$> many1 C.digit)
--       pRec = BinOp A.<$> pBase A.<*> pBop A.<*> pRec
--       paren = C.char '(' A.*> pExpr A.<* C.char ')' 

--pBop :: S.Parser Bop
--pBop = C.char '*' A.*> A.pure Times
--    A.<|> C.char '+' A.*> A.pure Plus
