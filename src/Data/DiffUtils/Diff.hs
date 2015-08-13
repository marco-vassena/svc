{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ConstraintKinds #-}

module Data.DiffUtils.Diff where

import Data.Proxy
import Data.Type.Equality
import Data.TypeList.DList

--------------------------------------------------------------------------------

--------------------------------------------------------------------------------

-- | A well-typed edit script that maps transforms xs values in ys values,
-- by means of insert, delete and update.
data ES xs ys where
  -- | Inserts something new in the tree
  Ins :: Metric a => F xs a -> ES ys (xs :++: zs) -> ES ys (a ': zs)
  -- | Removes something from the original tree
  Del :: Metric a => F xs a -> ES (xs :++: ys) zs -> ES (a ': ys) zs  
  -- | Replaces something in the original tree
  Upd :: Metric a => F xs a -> F ys a -> ES (xs :++: zs) (ys :++: ws) -> ES (a ': zs) (a ': ws)
  -- | Terminates the edit script
  End :: ES '[] '[]

--------------------------------------------------------------------------------
-- TODO probably we want to store the cost with the edit script
cost :: ES xs ys -> Int
cost End = 0
cost (Ins x xs) = 1 + cost xs
cost (Del x xs) = 1 + cost xs
cost (Upd f g xs) = distance f g + cost xs

-- Returns the best edit tree (least distance)
(&) :: ES xs ys -> ES xs ys -> ES xs ys
x & y = if cost x <= cost y then x else y

--------------------------------------------------------------------------------

-- Entry point, still needs type annotations for @f@.
gdiff :: (Metric a, Metric b) => a -> b -> ES '[ a ] '[ b ]
gdiff x y = getDiff $ diffT (toDList x) (toDList y)

diff :: DList xs -> DList ys -> ES xs ys
diff DNil DNil = End
diff (DCons (Node a as) xs) DNil = Del a $ diff (dappend as xs) DNil
diff DNil (DCons (Node b bs) ys) = Ins b $ diff DNil (dappend bs ys)
diff (DCons x@(Node a as) xs) (DCons y@(Node b bs) ys) =
  let i = Ins b $ diff (DCons x xs) (dappend bs ys) 
      d = Del a $ diff (dappend as xs) (DCons y ys) in 
  case decEq a b of
    Nothing -> i & d
    Just Refl -> i & d & u
      where u = Upd a b $ diff (dappend as xs) (dappend bs ys)

--------------------------------------------------------------------------------
-- Patch
--------------------------------------------------------------------------------

-- Return the target object, equivalent to patch
target :: ES xs ys -> DList ys
target (Ins x e) = insert x (target e)
target (Del x e) = target e
target (Upd x y e) = insert y (target e)
target End = DNil

-- Returns the source object
source :: ES xs ys -> DList xs
source (Ins x e) = source e
source (Del x e) = insert x (source e)
source (Upd x y e) = insert x (source e)
source End = DNil


insert :: Metric a => F xs a -> DList (xs :++: ys) -> DList (a ': ys)
insert f ds = DCons (Node f ds1) ds2
  where (ds1, ds2) = dsplit (reifyArgs f) ds

-------------------------------------------------------------------------------- 
-- Diff with memoization
--------------------------------------------------------------------------------

-- Memoization table
data EST xs ys where
  CC :: (Metric a, Metric b) => F xs a -> F ys b 
     -> ES (a ': zs) (b ': ws) 
     -> EST (a ': zs) (ys :++: ws)
     -> EST (xs :++: zs) (b ': ws)
     -> EST (xs :++: zs) (ys :++: ws)
     -> EST (a ': zs) (b ': ws)
  CN :: Metric a => F xs a -> ES (a ': ys) '[] 
     -> EST (xs :++: ys) '[]
     -> EST (a ': ys) '[]
  NC :: Metric b => F xs b -> ES '[] (b ': ys) 
     -> EST '[] (xs :++: ys) 
     -> EST '[] (b ': ys)
  NN :: ES '[] '[] -> EST '[] '[]

-- Returns the edit script contained in an EST table.
getDiff :: EST xs ys -> ES xs ys
getDiff (CC _ _ e _ _ _) = e
getDiff (CN _ e _) = e
getDiff (NC _ e _) = e
getDiff (NN e) = e

-- Memoized version of diff
diffT :: DList xs -> DList ys -> EST xs ys
diffT DNil DNil = NN End
diffT (DCons (Node a as) xs) DNil = CN a (Del a (getDiff d)) d 
  where d = diffT (dappend as xs) DNil
diffT DNil (DCons (Node b bs) ys) = NC b (Ins b (getDiff i)) i
  where i = diffT DNil (dappend bs ys)
diffT (DCons (Node a as) xs) (DCons (Node b bs) ys) = CC a b (best a b i d u) i d u
  where u = diffT (dappend as xs) (dappend bs ys)
        i = extendI a xs u
        d = extendD b ys u

best :: (Metric a, Metric b)
     => F as a -> F bs b
     -> EST (a ': xs) (bs :++: ys)
     -> EST (as :++: xs) (b ': ys)
     -> EST (as :++: xs) (bs :++: ys)
     -> ES (a ': xs) (b ': ys)
best f g i d c = 
  case decEq f g of
    Just Refl -> ab & (Upd f g (getDiff c))
    Nothing -> ab
  where a = Del f $ getDiff d
        b = Ins g $ getDiff i
        ab = a & b

--------------------------------------------------------------------------------
-- Auxiliary functions and datatypes used in diffT.
--------------------------------------------------------------------------------

-- TODO swap names

data IES b xs ys where
  IES :: F zs b -> ES xs (b ': ys) -> EST xs (zs :++: ys) -> IES b xs ys

data DES a xs ys where
  DES :: F zs a -> ES (a ': xs) ys -> EST (zs :++: xs) ys -> DES a xs ys

extractI :: EST xs (b ': ys) -> IES b xs ys
extractI (NC f e i) = IES f e i
extractI (CC f g e i _ _) = IES g e i

extractD :: EST (a ': xs) ys -> DES a xs ys
extractD (CN g e i) = DES g e i
extractD (CC f g e _ i _) = DES f e i

extendI :: Metric a
        => F xs a -> DList ys -> EST (xs :++: ys) zs -> EST (a ': ys) zs
extendI f _ d@(NN e) = CN f (Del f e) d
extendI f _ d@(CN _ e _) = CN f (Del f e) d
extendI f _ d@(NC _ _ _) = 
  case extractI d of
    IES g e c -> CC f g (best f g i d c) i d c
      where i = extendI f undefined c
extendI f _ d@(CC _ _ _ _ _ _) = 
  case extractI d of
    IES g e c -> CC f g (best f g i d c) i d c
      where i = extendI f undefined c


extendD :: Metric a
        => F xs a -> DList ys -> EST zs (xs :++: ys) -> EST zs (a ': ys)
extendD f _ i@(NN e) = NC f (Ins f e) i
extendD f _ i@(NC _ e _) = NC f (Ins f e) i 
extendD f _ i@(CN _ _ _) = 
  case extractD i of
    DES g e c -> CC g f (best g f i d c) i d c
      where d = extendD f undefined c
extendD f _ i@(CC _ _ _ _ _ _) = 
  case extractD i of
    DES g e c -> CC g f (best g f i d c) i d c
      where d = extendD f undefined c

--------------------------------------------------------------------------------

instance Show (ES xs ys) where
  show End = "End"
  show (Ins x xs) = "Ins " ++ string x ++ " $ " ++ show xs
  show (Del x xs) = "Del " ++ string x ++ " $ " ++ show xs
  show (Upd f g xs) = "Upd " ++ string f ++ " " ++ string g ++ " $ " ++ show xs
