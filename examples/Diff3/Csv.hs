{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Csv where

import Data.HList
import Repo.Diff
import Repo.Diff3
import Data.Proxy
import Data.Type.Equality

type Csv = [[Int]]

c0, c1, c2 :: Csv
c0 = [[1,2,3],
      [4,5,6],
      [7,8,9]]

c1 = map (0:) c0

c2 = [[1,2,3],
      [4,5,9],
      [7,8,15]]

c3 = [[1,2,6],
      [4,5,18],
      [7,8,30]]


d01, d02, d03 :: ES CsvF '[Csv] '[Csv]
d01 = gdiff c0 c1
d02 = gdiff c0 c2
d03 = gdiff c0 c3

d012 :: ES3 CsvF '[Csv] '[Csv]
d012 = diff3 d01 d02

c4 :: Csv
c4 = case patch3 Proxy d012 (DCons c0 DNil) of
        (DCons x DNil) -> x

d013 :: ES3 CsvF '[Csv] '[Csv]
d013 = diff3 d02 d03

c1' :: Csv
c1' = case patch Proxy d01 (DCons c0 DNil) of
        DCons x DNil -> x
        
c2PatchFail :: Csv
c2PatchFail = case patch Proxy d02 (DCons c1 DNil) of
            DCons x DNil -> x

--------------------------------------------------------------------------------
data CsvF xs a where
  Int' :: Int -> CsvF '[] Int
  NilRow' :: CsvF '[] [[Int]]
  ConsRow' :: CsvF '[[Int], [[Int]]] [[Int]]
  NilInt' :: CsvF '[] [Int]
  ConsInt' :: CsvF '[Int, [Int]] [Int]

instance Family CsvF where
  unbuild (Int' i) _ = Just DNil
  unbuild NilRow' [] = Just DNil
  unbuild NilInt' [] = Just DNil
  unbuild ConsRow' (x:xs) = Just $ DCons x (DCons xs DNil)
  unbuild ConsInt' (x:xs) = Just $ DCons x (DCons xs DNil)
  unbuild _ _ = Nothing

  build (Int' i) _ = i
  build NilRow' _ = []
  build NilInt' _ = []
  build ConsRow' (DCons x (DCons xs DNil)) = x : xs
  build ConsInt' (DCons x (DCons xs DNil)) = x : xs

  decEq (Int' _) (Int' _) = Just Refl
  decEq NilRow' NilRow' = Just Refl
  decEq NilRow' ConsRow' = Just Refl
  decEq ConsRow' NilRow' = Just Refl
  decEq ConsRow' ConsRow' = Just Refl
  decEq ConsInt' ConsInt' = Just Refl
  decEq ConsInt' NilInt' = Just Refl
  decEq NilInt' NilInt' = Just Refl
  decEq NilInt' ConsInt' = Just Refl
  decEq _ _ = Nothing

  string (Int' i) = show i
  string NilRow' = "[]"
  string ConsRow' = "(:)"
  string NilInt' = "[]"
  string ConsInt' = "(:)"
  
  (Int' x) =?= (Int' y) = if (x == y) then Just (Refl, Refl) else Nothing
  NilRow'  =?= NilRow' = Just (Refl, Refl)
  ConsRow' =?= ConsRow' = Just (Refl, Refl)
  NilInt'  =?= NilInt' = Just (Refl, Refl)
  ConsInt' =?= ConsInt' = Just (Refl, Refl)
  _ =?= _ = Nothing

  reifyF (Int' _) = slist
  reifyF NilRow' = slist
  reifyF NilInt' = slist
  reifyF ConsRow' = slist
  reifyF ConsInt' = slist
instance Metric CsvF where
  distance (Int' x) (Int' y) = if x == y then 0 else 1
  distance NilRow'  NilRow' = 0
  distance ConsRow' ConsRow' = 0
  distance NilInt'  NilInt' = 0
  distance ConsInt' ConsInt' = 0
  distance _ _ = 1

instance Csv :<: CsvF where
  view _ [] = View NilRow' DNil
  view _ (x:xs) = View ConsRow' (DCons x (DCons xs DNil))
 
instance [Int] :<: CsvF where
  view _ [] = View NilInt' DNil
  view _ (x:xs) = View ConsInt' (DCons x (DCons xs DNil))

instance Int :<: CsvF where
  view _ i = View (Int' i) DNil
