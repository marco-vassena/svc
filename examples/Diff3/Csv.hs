{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Csv where

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

d01, d02 :: ES CsvF '[Csv] '[Csv]
d01 = gdiff c0 c1
d02 = gdiff c0 c2

--------------------------------------------------------------------------------
data CsvF xs a where
  Int' :: Int -> CsvF '[] Int
  NilRow' :: CsvF '[] [[Int]]
  ConsRow' :: CsvF '[[Int], [[Int]]] [[Int]]
  NilInt' :: CsvF '[] [Int]
  ConsInt' :: CsvF '[Int, [Int]] [Int]

instance Family CsvF where
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
  
  (Int' _) =?= (Int' _) = Just (Refl, Refl)
  NilRow'  =?= NilRow' = Just (Refl, Refl)
  ConsRow' =?= ConsRow' = Just (Refl, Refl)
  NilInt'  =?= NilInt' = Just (Refl, Refl)
  ConsInt' =?= ConsInt' = Just (Refl, Refl)
  _ =?= _ = Nothing

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
