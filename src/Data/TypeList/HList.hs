{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}

-- This module defines typed heterogeneous lists
-- and few basic functions to deal with them.

module Data.TypeList.HList (
    module Data.TypeList.Core
  , module Data.TypeList.SList
  , HList(..)
  , HApply(..)
  , SameLength(..)
  , hsingleton
  , hHead
  , hTail
  , happend
  , split
  , hzip
  , hunzip
  , hfoldr
  , hfoldl
  , hunfoldr
  , hunfoldl
  , proxyList
  , appendAssociative
  , mapPreservesLength
  , leftIdentityAppend
  , rightIdentityAppend
  ) where

import GHC.TypeLits
import Data.Proxy
import Data.Type.Equality
import Data.TypeList.Core
import Data.TypeList.SList
import Control.Applicative

-- Heterogeneous list, indexed by a type level list that
-- mantains the types of the elements contained.
data HList (xs :: [ * ]) where
  Nil :: HList '[]
  Cons :: x -> HList xs -> HList (x ': xs)

-- Appends two heterogeneous lists
happend :: HList xs -> HList ys -> HList (xs :++: ys)
happend Nil ys = ys
happend (Cons x xs) ys = Cons x (happend xs ys)

-- map for heterogeneous lists
hmap :: (forall a . a -> f a) -> HList xs -> HList (Map f xs)
hmap f Nil = Nil
hmap f (Cons x xs) = Cons (f x) (hmap f xs)

hmap' :: SList xs -> (forall a . f a -> f a) -> HList (Map f xs) -> HList (Map f xs)
hmap' SNil f Nil = Nil
hmap' (SCons s) f (Cons x xs) = Cons (f x) (hmap' s f xs)

--------------------------------------------------------------------------------
-- Folding HList as if they were normal lists.
-- This functions convert the argument HList to a plain list 
-- and then fold/unfold it.
--------------------------------------------------------------------------------

-- TODO quickcheck test : foldl/unfoldl not being inverse lead to subtle bugs

hfoldr :: SList xs -> (HList xs -> b -> b) -> b -> HList (Map [] xs) -> b
hfoldr s f z hs = foldr f z (toList s hs)

-- | Note that the base element is defined only if the unfolded list
-- is finite.
hunfoldr :: SList xs -> (b -> Maybe (HList xs, b))
                      -> b -> (b, HList (Map [] xs))
hunfoldr s f z = (e, unList s hs)
  where (e, hs) = unfoldr f z

hfoldl :: SList xs -> (b -> HList xs -> b) -> b -> HList (Map [] xs) -> b
hfoldl s f z hs = foldl f z (toList s hs)

hunfoldl :: SList xs -> (b -> Maybe (b, HList xs)) -> b -> (b, HList (Map [] xs))
hunfoldl s f z = (e, unList s hs)
  where (e, hs) = unfoldl f z

unfoldl :: (b -> Maybe (b, a)) -> b -> (b, [a])
unfoldl f z = go z []
  where go e xs = 
          case f e of
            Just (e', x) -> go e' (x:xs)
            Nothing      -> (e, xs)

-- Custom unfoldr because we need also the "zero" element
-- Note that unlike the correspondent function from Data.List
-- it will fail terminate only if the unfolded list is finite
-- (as it happens for unfoldl).
unfoldr :: (b -> Maybe (a, b)) -> b -> (b, [a])
unfoldr f b = go b []
  where go b acc =
          case f b of
            Just (a, b') -> go b' (a:acc)
            Nothing      -> (b, reverse acc)


--------------------------------------------------------------------------------
-- Returns a singleton 'HList'
hsingleton :: a -> HList '[ a ]
hsingleton a = Cons a Nil

hHead :: HList (x ': xs) -> x
hHead (Cons x _) = x

hTail :: HList (x ': xs) -> HList xs
hTail (Cons x hs) = hs

--------------------------------------------------------------------------------
instance Reify HList where
  toSList Nil = SNil
  toSList (Cons x xs) = SCons (toSList xs)

instance Reify2 f => Reify (f xs) where
  toSList = snd . toSList2

instance Eq (HList '[]) where
  Nil == Nil = True

instance (Eq x, Eq (HList xs)) => Eq (HList (x ': xs)) where
  Cons x xs == Cons y ys = x == y && xs == ys 

--------------------------------------------------------------------------------

-- Concats a list of 'HList' in a single 'HList'.
-- The values contained in the input list are collected in a list.
--
-- > unList (SCons (SCons SNil)) [Cons 1 (Cons 'a' Nil), Cons 2 (Cons 'b' Nil)]
-- > Cons [1,2] (Cons "ab" Nil)
--
unList :: SList xs -> [HList xs] -> HList (Map [] xs)
unList SNil _ = Nil
unList (SCons s) [] = Cons [] (unList s [])
unList s (x:xs) = foldr (merge s) (hmap (const []) x) (x:xs)

-- | Converts an 'HList' of lists in a list of 'HList'
-- each one containing a single element of the original lists.
-- The lists in the 'HList' are supposed to have the same length,
-- if this is not the case only the number of values of the shortest
-- will be retained.
--
-- > toList (SCons (SCons SNil)) (Cons [1,2] (Cons "ab" Nil))
-- > [Cons 1 Cons 'a' Nil,Cons 2 Cons 'b' Nil]
--
-- > toList (SCons (SCons SNil)) (Cons [1] (Cons "ab" Nil))
-- > [Cons 1 Cons 'a' Nil]
--
toList :: SList xs -> HList (Map [] xs) -> [HList xs]
toList SNil Nil = [Nil] -- TODO also [] would work, distinguish between Many and Some
toList (SCons SNil) (Cons xs Nil) = zipWith Cons xs (repeat Nil)
toList (SCons s) (Cons xs xss) = zipWith Cons xs (toList s xss)

-- | Partial version of 'toList'.
-- Contrary to @'toList'@ if the lists have different length,
-- the whole operation fails.
--
-- > toListMaybe (SCons (SCons SNil)) (Cons [1,2] (Cons "ab" Nil))
-- > Just [Cons 1 Cons 'a' Nil,Cons 2 Cons 'b' Nil]
--
-- > toListMaybe (SCons (SCons SNil)) (Cons [1] (Cons "ab" Nil))
-- > Nothing
--
toListMaybe :: SList xs -> HList (Map [] xs) -> Maybe [HList xs]
toListMaybe SNil Nil = Just [Nil] -- TODO also [] would work, distinguish between Many and Some
toListMaybe (SCons SNil) (Cons xs Nil) = Just $ zipWith Cons xs (repeat Nil)
toListMaybe (SCons s) (Cons xs xss) = toListMaybe s xss >>= zipWithMaybe Cons xs 


-- Partial version of @'zipWith'@. It fails if the lists have different lengths.
zipWithMaybe :: (a -> b -> c) -> [a] -> [b] -> Maybe [c]
zipWithMaybe f [] [] = Just []
zipWithMaybe f (x:xs) (y:ys) = (f x y :) <$> zipWithMaybe f xs ys
zipWithMaybe f _ _ = Nothing

-- | 'merge s xs xss' is equivalent to 'zipWith (:) xs xss' for normal lists
--
-- > merge (SCons (SCons SNil)) (Cons 1 (Cons 'a' Nil)) (Cons [2,3] (Cons "bc" Nil))
-- > Cons [1,2,3] Cons "abc" Nil
--
merge :: SList xs -> HList xs -> HList (Map [] xs) -> HList (Map [] xs)
merge SNil Nil Nil = Nil
merge (SCons s) (Cons x xs) (Cons ys yss) = Cons (x : ys) (merge s xs yss)
  
-- Splits an hlist in two sub-hlists, according to the given index as 'SList'.
split :: SList xs -> SList ys -> HList (xs :++: ys) -> (HList xs, HList ys)
split SNil s hs = (Nil, hs)
split (SCons s1) s2 (Cons h hs) = (Cons h hs1, hs2)
  where (hs1, hs2) = split s1 s2 hs

-- @'HFun' xs c@ is the type of a function taking @xs@ arguments
-- and returning something of type @c@.
-- For instance 
-- HFun '[a, b] c = a -> b -> c
type family HFun (xs :: [ * ]) (c :: *) :: * where
  HFun '[] c = c
  HFun (x ': xs) c = x -> HFun xs c

-- Simplify function application for values contained in 'HList',
-- hiding the list unpacking.
class HApply xs c where
  happly :: HFun xs c -> HList xs -> c

instance HApply '[] c where
  happly c _ = c

instance HApply xs c => HApply (x ': xs) c where
  happly f (Cons x xs) = happly (f x) xs

--------------------------------------------------------------------------------
-- Proof that two 'HList' have the same length.
data SameLength (xs :: [ * ]) (ys :: [ * ]) where
  Zero :: SameLength '[] '[]
  One :: SameLength xs ys -> SameLength (x ': xs) (y ': ys)

-- @'zipWith'@ generalises @'zip'@ by zipping with the function given 
-- as the first argument, instead of a tupling function.
-- Corresponds to @zipWith f xs ys@ for normal lists, however
-- the proof @'SameLength' xs ys@ ensures that the two lists
-- have the same length, thus no elements are discarded. 
hZipWith :: SameLength xs ys -> (forall a b . a -> b -> f a b) 
         -> HList xs -> HList ys -> HList (ZipWith f xs ys)
hZipWith Zero f Nil Nil = Nil
hZipWith (One p) f (Cons x xs) (Cons y ys) = Cons (f x y) (hZipWith p f xs ys)

-- | Zips two 'HList' of the same length, in pairs.
-- Corresponds to @zip xs ys@ for normal lists, however
-- the proof @'SameLength' xs ys@ ensures that the two lists
-- have the same length, thus no elements are discarded. 
hzip :: SameLength xs ys -> HList xs -> HList ys -> HList (ZipWith (,) xs ys)
hzip p xs ys = hZipWith p (,) xs ys

-- | Unzip a zipped list in two distinct 'HList'.
hunzip :: SameLength xs ys -> HList (ZipWith (,) xs ys) -> (HList xs, HList ys)
hunzip Zero Nil = (Nil, Nil)
hunzip (One p) (Cons (a, b) xs) =
  case hunzip p xs of
    (as, bs) -> (Cons a as, Cons b bs)

-- The property 'SameLength' is symmetric.
-- We can switch the two indexed lists freely.
sameLengthSym :: SameLength xs ys -> SameLength ys xs
sameLengthSym Zero = Zero
sameLengthSym (One p) = One (sameLengthSym p)

-- | Proof that type-level Map does not change the length of a type level list:
-- @length as = length ('Map' f xs)@, which is encoded by a value of type 
-- @'SameLength' as ('Map' f as)@.
-- This function is lazy in the function f, which is needed only to fix the type @f@.
mapPreservesLength :: Proxy f -> SList as -> SameLength as (Map f as)
mapPreservesLength _ SNil = Zero
mapPreservesLength p (SCons s) = One (mapPreservesLength p s)

-- A proxy that fix the functor to list [].
proxyList :: Proxy []
proxyList = Proxy

instance Reify2 SameLength where
  toSList2 Zero = (SNil, SNil)
  toSList2 (One p) =
    case toSList2 p of
      (s1, s2) -> (SCons s1, SCons s2)

-- | Proof that append is associative.
appendAssociative :: SList xs -> SList ys -> SList zs 
                -> HList (xs :++: (ys :++: zs)) :~: HList ((xs :++: ys) :++: zs)
appendAssociative SNil s2 s3 = Refl
appendAssociative (SCons s1) s2 s3 =
  case appendAssociative s1 s2 s3 of
    Refl -> Refl

leftIdentityAppend :: SList xs -> '[] :++: xs :~: xs
leftIdentityAppend SNil = Refl
leftIdentityAppend (SCons s) = 
  case leftIdentityAppend s of
    Refl -> Refl

rightIdentityAppend :: SList xs -> xs :++: '[] :~: xs
rightIdentityAppend SNil = Refl
rightIdentityAppend (SCons s) = 
  case rightIdentityAppend s of
    Refl -> Refl

--------------------------------------------------------------------------------
-- Debugging
instance Show (HList '[]) where
  show Nil = "Nil"

instance (Show x, Show (HList xs)) => Show (HList (x ': xs)) where
  show (Cons x xs) = unwords ["Cons", show x, show xs]
