module Control.Isomorphism.Partial.Base where


import Data.HList
import Data.Maybe

-- | Convenient type synonym that encodes a partial
-- function between two typed 'HList'
type PFunction xs ys = HList xs -> Maybe (HList ys)

data Iso xs ys = Iso (PFunction xs ys) (PFunction ys xs) (SList xs) (SList ys)

