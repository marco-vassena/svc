module Control.Isomorphism.Partial.Base where


import Data.TypeList.HList
import Data.Maybe

-- | It represents a partial isomorphism between 'HList', that 
-- consists of a pure function @apply@ and its partial inverse
-- @unapply@.
-- The data type includes also singleton types of the two indexes
-- necessary to conveniently manipulate them internally.
data Iso xs ys = Iso { apply    :: HList xs -> HList ys,
                       unapply  :: HList ys -> Maybe (HList xs),
                       sapply   :: SList xs,
                       sunapply :: SList ys }

