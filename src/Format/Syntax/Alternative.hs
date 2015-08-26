{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}

-- Definition of alternative format combinators and their smart constructors.

module Format.Syntax.Alternative where

import Data.TypeList.HList
import Format.Syntax.Base 
import Format.Syntax.Applicative

data AlternativeS c (m :: * -> *) (i :: *) (xs :: [ * ]) where
  Choice :: (c m i a, c m i b, Reify (a m i)) 
         =>  a m i xs -> b m i xs -> AlternativeS c m i xs
  Empty :: SList xs -> AlternativeS c m i xs

-- | The constraints required to use alternative combinators
type AlternativeC c m i = (Use AlternativeS c m i, ApplicativeC c m i)


infixr 3 <|>

-- | Associative choice. 
-- Note that the specific parsing library
-- used determines whether this is greedy or symmetric choice.
-- The user must also check that the printing library used 
-- handles it accordingly.
(<|>) :: AlternativeC c m i => Format c m i xs -> Format c m i xs -> Format c m i xs
p <|> q = format (Choice p q)

-- The identity of @<|>@
empty :: (AlternativeC c m i, KnownSList xs) => Format c m i xs
empty = format (Empty slist)

instance Reify (AlternativeS c m i) where
  toSList (Choice a b) = toSList a
  toSList (Empty s) = s
