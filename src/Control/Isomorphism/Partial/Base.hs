module Control.Isomorphism.Partial.Base where


import Data.HList
import Data.Maybe

data Iso xs ys = Iso (HList xs -> Maybe (HList ys)) (HList ys -> Maybe (HList xs)) (SList xs) (SList ys)

