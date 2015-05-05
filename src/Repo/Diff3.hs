{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Repo.Diff3 where

import Data.Proxy
import Data.HList
import Data.Type.Equality

-- TODO use this in Data.HList instead of :++:
type (:++:) = Append

-- TODO for the ES datatype we could
-- 1) Include Cpy (a special case of Upd), which might make the code for diff3 easier.

-- | A well-typed edit script that maps transforms xs values in ys values,
-- by means of insert, delete and update.
data ES f xs ys where
  -- | Inserts something new in the tree
  Ins :: (a :<: f, KnownSList xs) => f xs a -> ES f ys (xs :++: zs) -> ES f ys (a ': zs)
  -- | Removes something from the original tree
  Del :: (a :<: f, KnownSList xs) => f xs a -> ES f (xs :++: ys) zs -> ES f (a ': ys) zs  
  -- | Replaces something in the original tree
  Upd :: (a :<: f, KnownSList xs, KnownSList ys) 
      => f xs a -> f ys a -> ES f (xs :++: zs) (ys :++: ws) -> ES f (a ': zs) (a ': ws)
  -- | Terminates the edit script
  End :: ES f '[] '[]

-- Entry point, still needs type annotations for @f@.
gdiff :: (Family f, Metric f, a :<: f, b :<: f) => a -> b -> ES f '[ a ] '[ b ]
gdiff x y = getDiff $ diffT Proxy (DCons x DNil) (DCons y DNil)

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

-- A @'View' f a@ deconstructs a value, producing a 
-- witness @f xs a@ of its constructor, with a list 
-- containing its fields.
data View f a where
  View :: KnownSList xs => f xs a -> DList f xs -> View f a

--------------------------------------------------------------------------------

data DList f xs where
  DNil :: DList f '[]
  DCons :: (x :<: f) => x -> DList f xs -> DList f (x ': xs)

dappend :: DList f xs -> DList f ys -> DList f (xs :++: ys)
dappend DNil ys = ys
dappend (DCons x xs) ys = DCons x (dappend xs ys)

--------------------------------------------------------------------------------

-- Represents the fact that a type a belongs to a particular
-- family of mutually recursive data-types
class a :<: f where
  view :: Proxy f -> a -> View f a

diff :: (Family f, Metric f) => Proxy f -> DList f xs -> DList f ys -> ES f xs ys
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

dsplit :: SList xs -> DList f (xs :++: ys) -> (DList f xs, DList f ys)
dsplit SNil ds = (DNil, ds)
dsplit (SCons s) (DCons x ds) = (DCons x ds1, ds2)
  where (ds1, ds2) = dsplit s ds

insert :: (Family f, a :<: f, KnownSList xs) => f xs a -> DList f (xs :++: ys) -> DList f (a ': ys)
insert f ds = DCons (build f ds1) ds2
  where (ds1, ds2) = dsplit slist ds

stringOf :: (Family f, a :<: f) => Proxy f -> a -> String
stringOf p a = case view p a of
                  View g _ -> string g

delete :: Family f => Proxy f -> f xs a -> DList f (a ': ys) -> DList f (xs :++: ys)
delete p f (DCons x ys) = 
  case unbuild f x of
    Just xs -> dappend xs ys
    Nothing -> error $ "delete: Expecting " ++ string f ++ ", found " ++ stringOf p x

patch :: Family f => Proxy f -> ES f xs ys -> DList f xs -> DList f ys
patch p (Ins x e)   = insert x . patch p e
patch p (Del x e)   =            patch p e . delete p x
patch p (Upd x y e) = insert y . patch p e . delete p x
patch p End         = id

-------------------------------------------------------------------------------- 
-- Memoization
--------------------------------------------------------------------------------

-- Memoization table
data EST f xs ys where
  CC :: (a :<: f, b :<: f, KnownSList xs, KnownSList ys) => f xs a -> f ys b 
     -> ES f (a ': zs) (b ': ws) 
     -> EST f (a ': zs) (ys :++: ws)
     -> EST f (xs :++: zs) (b ': ws)
     -> EST f (xs :++: zs) (ys :++: ws)
     -> EST f (a ': zs) (b ': ws)
  CN :: (a :<: f, KnownSList xs) => f xs a -> ES f (a ': ys) '[] 
     -> EST f (xs :++: ys) '[]
     -> EST f (a ': ys) '[]
  NC :: (b :<: f, KnownSList xs) => f xs b -> ES f '[] (b ': ys) 
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

best :: (Metric f, Family f, a :<: f, b :<: f, KnownSList bs, KnownSList as)
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

extendI :: (Metric f, Family f, a :<: f, KnownSList xs) 
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

extendD :: (Metric f, Family f, a :<: f, KnownSList xs) 
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

-- TODO better names
data InsES f b xs ys where
  IES :: KnownSList zs => f zs b -> ES f xs (b ': ys) -> EST f xs (zs :++: ys) -> InsES f b xs ys

data DelES f a xs ys where
  DES :: KnownSList zs => f zs a -> ES f (a ': xs) ys -> EST f (zs :++: xs) ys -> DelES f a xs ys

extractI :: EST f xs (b ': ys) -> InsES f b xs ys
extractI (NC f e i) = IES f e i
extractI (CC f g e i _ _) = IES g e i

extractD :: EST f (a ': xs) ys -> DelES f a xs ys
extractD (CN g e i) = DES g e i
extractD (CC f g e _ i _) = DES f e i

--------------------------------------------------------------------------------
-- Diff3 
--------------------------------------------------------------------------------
-- TODO move split in different modules

-- An edit script @ES3 f xs ys zs@ represents is an edit scripts
-- that represents changes from @xs@ to @ys@ and from @xs@ to @zs@.
data ES3 f xs ys where
  -- | Inserts something new in the tree
  Ins3 :: f xs a -> ES3 f ys (xs :++: zs) -> ES3 f ys (a ': zs)
  -- | Removes something from the original tree
  Del3 :: f xs a -> ES3 f (xs :++: ys) zs -> ES3 f (a ': ys) zs  
  -- | Replaces something in the original tree
  Upd3 :: f xs a -> f ys a -> ES3 f (xs :++: zs) (ys :++: ws) -> ES3 f (a ': zs) (a ': ws)
  -- | A conflict between the two edit script
  Cnf3 :: Conflict f -> ES3 f xs ys -> ES3 f zs ws
  -- | Terminates the edit script
  End3 :: ES3 f '[] '[]

-- Represents what kind of conflict has been detected.
data Conflict f where
  InsIns :: f xs a -> f ys b -> Conflict f
  UpdDel :: f xs a -> f ys b -> Conflict f
  DelUpd :: f xs a -> f ys b -> Conflict f
  UpdUpd :: f xs a -> f ys b -> Conflict f

-- Given an ES3 if no conflicts are present build the merged version, otherwise returns
-- a list of the conflicts found in the edit script.
patch3 :: (Family f, Metric f) => ES3 f xs ys -> DList f xs -> Either [Conflict f] (DList f ys)
patch3 (Ins3 x e) hs = undefined
patch3 End3 hs = undefined

-- We can update a value, when the other is copied, 
-- only if they have the same fields.
agreeCpyUpd :: f xs a -> f ys a -> Maybe (xs :~: ys)
agreeCpyUpd = undefined

agreeDelCpy1 :: f xs a -> SList zs -> SList ys -> SList ws -> ES f (xs :++: ys) zs -> ES f (xs :++: ys) (xs :++: ws) -> Maybe ((a ': zs) :~: ws)
agreeDelCpy1 = undefined

sSplit :: SList xs -> SList (xs :++: ys) -> SList ys
sSplit = undefined

instance Reify2 (ES f) where
  toSList2 = undefined

agreeIns2 :: f xs a -> SList zs -> SList ws -> Maybe (a ': zs :~: ws)
agreeIns2 = undefined

getTail2 :: ES f xs (ys :++: zs) -> SList ys -> SList zs
getTail2 = undefined

-- Merges two ES scripts in an ES3 script.
diff3 :: (Family f, Metric f) => ES f xs ys -> ES f xs zs -> ES3 f xs ys
diff3 (Upd o x xs) (Upd o' y ys) = 
  case aligned o o' of
    (Refl, Refl) -> 
      case (o =?= x, o' =?= y, x =?= y) of
          (Just (Refl, Refl), _, _) -> 
            case agreeCpyUpd x y of
              Just Refl -> Upd3 o y (diff3 xs ys)
              Nothing -> Cnf3 (UpdUpd x y) (diff3 xs ys)
          (_, Just (Refl, Refl), _) -> Upd3 o x (diff3 xs ys)
          (_, _, Just (Refl, Refl)) -> Upd3 o x (diff3 xs ys) -- False positive, the scripts agree
          (_, _, _                ) -> Cnf3 (UpdUpd x y) (diff3 xs ys)
diff3 (Upd o x xs) (Del o' ys) =
  case aligned o o' of
    (Refl, Refl) -> 
      case o =?= x of
        Just (Refl, Refl) -> Del3 o undefined -- (diff ys zs)
--          let (xs', yws') = toSList2 xs
--              ws' = sSplit undefined yws'
--              (_, zs') = toSList2 ys in undefined
--           case agreeDelCpy1 o undefined undefined undefined xs ys of
--              Just Refl -> undefined -- Del3 o (diff3 ys xs)
--              Nothing -> Cnf3 (DelUpd x o) (diff3 xs ys)
        _ -> Cnf3 (UpdDel x o) (diff3 xs ys)
diff3 (Del o xs) (Upd o' y ys) =
  case aligned o o' of
    (Refl, Refl) -> 
      case o' =?= y of
        Just (Refl, Refl) -> Del3 o (diff3 xs ys)
        _ -> Cnf3 (DelUpd o y) (diff3 xs ys)
diff3 (Del x xs) (Del y ys) =
  case aligned x y of
    (Refl, Refl) -> Del3 x (diff3 xs ys)
diff3 (Ins x xs) (Ins y ys) = 
  case x =?= y of
    Just (Refl, Refl) -> Ins3 x (diff3 xs ys)
    _ -> Cnf3 (InsIns x y) (diff3 xs ys)
diff3 (Ins x xs) ys = Ins3 x (diff3 xs ys) 
diff3 xs (Ins y ys) =
  let (s1, s2) = toSList2 ys 
      (s3, s4) = toSList2 xs in
  case agreeIns2 y s4 (getTail2 ys) of
    Just Refl -> Ins3 y (diff3 ys xs)
    Nothing -> Cnf3 undefined (diff3 xs ys)
diff3 End End = End3

-- Checks whether the two witnesses are the same,
-- and fails if this is not the case.
aligned :: Family f => f xs a -> f ys b -> (xs :~: ys , a :~: b)
aligned a b =
  case a =?= b of
    Just (Refl, Refl) -> (Refl, Refl)
    _ -> error $ "Scripts not aligned: " ++ string a ++ " <-> " ++ string b

--------------------------------------------------------------------------------
-- TODO: remove
conflict :: Family f => f xs a -> f ys b -> t
conflict x y = error $ "Value conflict: " ++ string x ++ " " ++ string y

removedAndUpdated :: Family f => f xs a -> f ys b -> t
removedAndUpdated o x = error msg 
  where msg = "Shape conflict: " ++ removed ++ " <-> " ++ updated
        removed = "removed " ++ string o
        updated = "updated to " ++ string x
----------------------------------------------------------------------------------

class Family f where
  -- TODO better name
  decEq :: f xs a -> f ys b -> Maybe (a :~: b)
  
  -- Succeds only if the singleton types represents exactly the same constructor
  (=?=) :: Family f => f xs a -> f ys b -> Maybe ( a :~: b , xs :~: ys )

  string :: f xs a -> String
  build :: f xs a -> DList f xs -> a
  unbuild :: f xs a -> a -> Maybe (DList f xs)

class Metric f where
  -- Laws:
  --  d x y = d y x             (symmetry)
  --  d x y >= 0                (non-negativity)
  --  d x x = 0                 (identity)
  --  d x z <= d x y + d y z    (triangle inequality)
  distance :: f xs a -> f ys a -> Int

--------------------------------------------------------------------------------

instance Family f => Show (ES f xs ys) where
  show End = "End"
  show (Ins x xs) = "Ins " ++ string x ++ " $ " ++ show xs
  show (Del x xs) = "Del " ++ string x ++ " $ " ++ show xs
  show (Upd f g xs) = "Upd " ++ string f ++ " " ++ string g ++ " $ " ++ show xs

instance Family f => Show (ES3 f xs ys) where
  show End3 = "End3"
  show (Ins3 x xs) = "Ins3 " ++ string x ++ " $ " ++ show xs
  show (Del3 x xs) = "Del3 " ++ string x ++ " $ " ++ show xs
  show (Upd3 x y xs) = "Upd3 " ++ string x ++ " " ++ string y ++ " $ " ++ show xs
  show (Cnf3 x xs) = "Cnf " ++ show x ++ " $ " ++ show xs

instance Family f => Show (Conflict f) where
  show (InsIns a b) = "InsIns " ++ string a ++ " " ++ string b
  show (UpdDel a b) = "UpdDel " ++ string a ++ " " ++ string b
  show (DelUpd a b) = "DelUpd " ++ string a ++ " " ++ string b
  show (UpdUpd a b) = "UpdUpd " ++ string a ++ " " ++ string b
