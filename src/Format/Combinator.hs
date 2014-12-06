{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

-- This module provides common combinators

module Format.Combinator where

import Format.Base
import Data.Functor.Identity (Identity)
import Text.Parsec.Char
import Text.Parsec.Combinator hiding ((<|>))
import Text.Parsec.Prim hiding ((<|>), many)
import Format.HList

int :: (StringLike i, Stream i Identity Char) => Format i '[ Int ]
int = Target

between :: (Fill l, Fill r) => Format i l -> Format i xs -> Format i r -> Format i xs
between l p r = l @> p <@ r


-- The unit format. The parser succeeds without consuming any input
-- and does not print nothing at all.
empty :: (Stream i Identity Char, StringLike i) => Format i '[]
empty = Meta ()

--------------------------------------------------------------------------------
-- Combinators for DFormat
--------------------------------------------------------------------------------

-- TODO fix associativity to avoid parenthesis
-- syntactic sugar
(<$>) :: Proj a args => (HList args -> a) -> Format i args -> DFormat i a
(<$>) = CFormat
(<|>) = Alt

-- Example with list

-- Constructors curried to work with list
nil :: HList '[] -> [ a ]
nil Nil = []

cons :: HList '[a , [a]] -> [ a ]
cons (Cons x (Cons xs Nil)) = x:xs

many :: (Stream i Identity Char, StringLike i) => Format i '[ a ] -> Format i '[ [ a ] ]
many p = DF $   nil  <$> empty 
           <|> (cons <$> (p <@> many p))
  
sepBy :: (Stream i Identity Char, StringLike i, Fill ys) => 
            Format i '[ a ] -> Format i ys -> Format i '[ [ a ] ]
sepBy p sep = DF $   nil  <$> empty
                <|>  (cons <$> (p <@> many (sep @> p)))

-- These instances can be automatically derived using TH
instance Proj [ a ] '[] where
  proj [] = Just Nil
  proj _ = Nothing

instance Proj [ a ] '[a , [a]] where
  proj (x:xs) = Just $ Cons x (Cons xs Nil)
  proj _ = Nothing
