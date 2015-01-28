module Control.Isomorphism.Partial.Base where


import Data.HList
import Data.Maybe

-- | Convenient type synonym that encodes a partial
-- function between two typed 'HList'
type PFunction f xs ys = HList xs -> f (HList ys)

-- | It represents a partial isomorphism between 'HList'.
-- It includes values for the singleton types of the two parametrized
-- type-level lists.
data Iso f xs ys = Iso { apply    :: PFunction f xs ys,
                         unapply  :: PFunction f ys xs,
                         sapply   :: SList xs,
                         sunapply :: SList ys }

