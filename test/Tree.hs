-- | This module defines a dummy data type used for testing partial isomorphism

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Tree where

import Control.Isomorphism.Partial
import Data.HList

data Tree = Branch Tree Tree
          | Leaf
  deriving (Show, Eq)

leaf :: CIso '[] Tree
leaf = iso (const Leaf) proj SNil
  where proj (Branch _ _) = Nothing
        proj Leaf         = Just Nil

branch :: CIso '[Tree, Tree] Tree
branch = iso (\(Cons b1 (Cons b2 _)) -> Branch b1 b2) proj (SCons (SCons SNil))
  where proj (Branch b1 b2) = Just $ Cons b1 (Cons b2 Nil)
        proj _ = Nothing

foldlTree :: Iso '[Tree, [Tree]] '[ Tree ]
foldlTree = foldl' (SCons SNil) branch


