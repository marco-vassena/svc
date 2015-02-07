{-# LANGUAGE TemplateHaskell #-}

module Main where

import Text.ParserCombinators.UU.Utils
import Expr (Expr(..), Bop(..), printExpr, parseExpr)
import Test.QuickCheck
import Control.Monad

instance Arbitrary Expr where
  arbitrary = exprGen 5 

  shrink (BinOp e1 _ e2) = [e1, e2]
  shrink  _ = []

instance Arbitrary Bop where
  arbitrary = elements [Plus, Times]

varGen :: Gen Expr
varGen = listOf1 (elements letters) >>= return . Var
  where letters = ['a'..'z'] ++ ['A'..'Z']

litGen :: Gen Expr
litGen = arbitrary >>= return . Lit

exprGen :: Int -> Gen Expr
exprGen 0 = oneof [varGen, litGen]
exprGen n | n > 0 = oneof [varGen, litGen, subExpr]
  where subExpr = liftM3 BinOp (exprGen m) arbitrary (exprGen m)
        m = n `div` 2

--------------------------------------------------------------------------------

-- Throws an error if the printer fails
unsafePrintExpr :: Expr -> String
unsafePrintExpr e = maybe (error msg) id (printExpr e)
  where msg = "Printer failed on: " ++ show e

-- What is printed can be parsed back and it is the same of the input value
prop_leftId :: Expr -> Bool
prop_leftId input = input == output
  where output = runParser "" parseExpr (unsafePrintExpr input)

main :: IO ()
main = return ()
