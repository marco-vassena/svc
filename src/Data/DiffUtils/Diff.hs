{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}

module Data.DiffUtils.Diff where

import Data.Proxy
import Data.Type.Equality
import Data.TypeList.DList

--------------------------------------------------------------------------------

-- Represents the fact that a type a belongs to a particular
-- family of mutually recursive data-types
class Metric f where
  -- Laws:
  --  d x y = d y x             (symmetry)
  --  d x y >= 0                (non-negativity)
  --  d x x = 0                 (identity)
  --  d x z <= d x y + d y z    (triangle inequality)
  distance :: f xs a -> f ys a -> Int

--------------------------------------------------------------------------------

-- | A well-typed edit script that maps transforms xs values in ys values,
-- by means of insert, delete and update.
data ES f xs ys where
  -- | Inserts something new in the tree
  Ins :: (a :<: f) => f xs a -> ES f ys (xs :++: zs) -> ES f ys (a ': zs)
  -- | Removes something from the original tree
  Del :: (a :<: f) => f xs a -> ES f (xs :++: ys) zs -> ES f (a ': ys) zs  
  -- | Replaces something in the original tree
  Upd :: (a :<: f) => f xs a -> f ys a -> ES f (xs :++: zs) (ys :++: ws) -> ES f (a ': zs) (a ': ws)
  -- | Terminates the edit script
  End :: ES f '[] '[]

--------------------------------------------------------------------------------
-- TODO probably we want to store the cost with the edit script
cost :: Metric f => ES f xs ys -> Int
cost End = 0
cost (Ins x xs) = 1 + cost xs
cost (Del x xs) = 1 + cost xs
cost (Upd f g xs) = distance f g + cost xs

-- Returns the best edit tree (least distance)
(&) :: Metric f => ES f xs ys -> ES f xs ys -> ES f xs ys
x & y = if cost x <= cost y then x else y

--------------------------------------------------------------------------------

-- Entry point, still needs type annotations for @f@.
gdiff :: (Family f, Metric f, a :<: f, b :<: f) => a -> b -> ES f '[ a ] '[ b ]
gdiff x y = getDiff $ diffT Proxy (DCons x DNil) (DCons y DNil)

diff :: (Family f, Metric f) 
     => Proxy f -> DList f xs -> DList f ys -> ES f xs ys
diff _ DNil DNil = End
diff p (DCons x xs) DNil = 
  case view p x of 
    View f ys -> Del f $ diff p (dappend ys xs) DNil
diff p DNil (DCons y ys) =
  case view p y of
    View g xs -> Ins g $ diff p DNil (dappend xs ys)
diff p (DCons x xs) (DCons y ys) =
  case (view p x, view p y) of
    (View f fs, View g gs) -> 
      let i = Ins g $ diff p (DCons x xs) (dappend gs ys) 
          d = Del f $ diff p (dappend fs xs) (DCons y ys) in 
      case decEq f g of
        Nothing -> i & d
        Just Refl -> i & d & u
          where u = Upd f g $ diff p (dappend fs xs) (dappend gs ys)

--------------------------------------------------------------------------------
-- Patch
--------------------------------------------------------------------------------

-- TODO if we used DTree and DList we could make patch safe
-- TODO with an auxiliary function patch' we can avoid the proxy.
patch :: Family f => Proxy f -> ES f xs ys -> DList f xs -> DList f ys
patch p (Ins x e)   = insert x . patch p e
patch p (Del x e)   =            patch p e . delete p x
patch p (Upd x y e) = insert y . patch p e . delete p x
patch p End         = id

-- Safe alternative to patch
target :: Family f => ES f xs ys -> DList f ys
target (Ins x e) = insert x (target e)
target (Del x e) = target e
target (Upd x y e) = insert y (target e)
target End = DNil

source :: Family f => ES f xs ys -> DList f xs
source (Ins x e) = source e
source (Del x e) = insert x (source e)
source (Upd x y e) = insert x (source e)
source End = DNil


insert :: (Family f, a :<: f) => f xs a -> DList f (xs :++: ys) -> DList f (a ': ys)
insert f ds = DCons (build f ds1) ds2
  where (ds1, ds2) = dsplit (reifyArgs f) ds

stringOf :: (Family f, a :<: f) => Proxy f -> a -> String
stringOf p a = case view p a of
                  View g _ -> string g

delete :: Family f => Proxy f -> f xs a -> DList f (a ': ys) -> DList f (xs :++: ys)
delete p f (DCons x ys) = 
  case unbuild f x of
    Just xs -> dappend xs ys
    Nothing -> error $ "delete: Expecting " ++ string f ++ ", found " ++ stringOf p x

-------------------------------------------------------------------------------- 
-- Diff with memoization
--------------------------------------------------------------------------------

-- Memoization table
data EST f xs ys where
  CC :: (a :<: f, b :<: f) => f xs a -> f ys b 
     -> ES f (a ': zs) (b ': ws) 
     -> EST f (a ': zs) (ys :++: ws)
     -> EST f (xs :++: zs) (b ': ws)
     -> EST f (xs :++: zs) (ys :++: ws)
     -> EST f (a ': zs) (b ': ws)
  CN :: (a :<: f) => f xs a -> ES f (a ': ys) '[] 
     -> EST f (xs :++: ys) '[]
     -> EST f (a ': ys) '[]
  NC :: (b :<: f) => f xs b -> ES f '[] (b ': ys) 
     -> EST f '[] (xs :++: ys) 
     -> EST f '[] (b ': ys)
  NN :: ES f '[] '[] -> EST f '[] '[]

-- Returns the edit script contained in an EST table.
getDiff :: EST f xs ys -> ES f xs ys
getDiff (CC _ _ e _ _ _) = e
getDiff (CN _ e _) = e
getDiff (NC _ e _) = e
getDiff (NN e) = e

-- Memoized version of diff
diffT :: (Family f, Metric f) => Proxy f -> DList f xs -> DList f ys -> EST f xs ys
diffT _ DNil DNil = NN End
diffT p (DCons x xs) DNil = 
  case view p x of
    View f fs -> CN f (Del f (getDiff d)) d 
        where d = diffT p (dappend fs xs) DNil
diffT p DNil (DCons y ys) = 
  case view p y of
    View g gs -> NC g (Ins g (getDiff i)) i
      where i = diffT p DNil (dappend gs ys)
diffT p (DCons x xs) (DCons y ys) =
  case (view p x, view p y) of
    (View f fs, View g gs) -> 
       let c = diffT p (dappend fs xs) (dappend gs ys)
           i = extendI f xs c
           d = extendD g ys c in 
           CC f g (best f g i d c) i d c

best :: (Metric f, Family f, a :<: f, b :<: f)
     => f as a -> f bs b
     -> EST f (a ': xs) (bs :++: ys)
     -> EST f (as :++: xs) (b ': ys)
     -> EST f (as :++: xs) (bs :++: ys)
     -> ES f (a ': xs) (b ': ys)
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

data IES f b xs ys where
  IES :: f zs b -> ES f xs (b ': ys) -> EST f xs (zs :++: ys) -> IES f b xs ys

data DES f a xs ys where
  DES :: f zs a -> ES f (a ': xs) ys -> EST f (zs :++: xs) ys -> DES f a xs ys

extractI :: EST f xs (b ': ys) -> IES f b xs ys
extractI (NC f e i) = IES f e i
extractI (CC f g e i _ _) = IES g e i

extractD :: EST f (a ': xs) ys -> DES f a xs ys
extractD (CN g e i) = DES g e i
extractD (CC f g e _ i _) = DES f e i

extendI :: (Metric f, Family f, a :<: f) 
        => f xs a -> DList f ys -> EST f (xs :++: ys) zs -> EST f (a ': ys) zs
extendI f _ d@(NN e) = CN f (Del f e) d
extendI f _ d@(CN _ e _) = CN f (Del f e) d
extendI f _ d@(NC _ e _) = 
  case extractI d of
    IES g e c -> CC f g (best f g i d c) i d c
      where i = extendI f undefined c
extendI f _ d@(CC _ _ e _ _ _) = 
  case extractI d of
    IES g e c -> CC f g (best f g i d c) i d c
      where i = extendI f undefined c

extendD :: (Metric f, Family f, a :<: f) 
        => f xs a -> DList f ys -> EST f zs (xs :++: ys) -> EST f zs (a ': ys)
extendD f _ i@(NN e) = NC f (Ins f e) i
extendD f _ i@(NC _ e _) = NC f (Ins f e) i 
extendD f _ i@(CN _ e _) = 
  case extractD i of
    DES g e c -> CC g f (best g f i d c) i d c
      where d = extendD f undefined c
extendD f _ i@(CC _ _ e _ _ _) = 
  case extractD i of
    DES g e c -> CC g f (best g f i d c) i d c
      where d = extendD f undefined c

--------------------------------------------------------------------------------

instance Family f => Show (ES f xs ys) where
  show End = "End"
  show (Ins x xs) = "Ins " ++ string x ++ " $ " ++ show xs
  show (Del x xs) = "Del " ++ string x ++ " $ " ++ show xs
  show (Upd f g xs) = "Upd " ++ string f ++ " " ++ string g ++ " $ " ++ show xs
