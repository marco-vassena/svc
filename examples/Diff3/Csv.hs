{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Csv where

--import Data.TypeList.HList
import Data.TypeList.DList
import Data.DiffUtils.Diff
import Data.DiffUtils.Diff3
import Data.Proxy
import Data.Type.Equality

type Row = [Int]

r0, r1, r2 :: Row
r0 = [1,2,3,4,5,6]
r1 = [1,4,5,2,3,6]
r2 = [1,2,4,5,3,6]

r01, r02 :: ES CsvF '[Row] '[Row]
r01 = gdiff r0 r1
r02 = gdiff r0 r2

-- Same UpdUpd conflicts detected (but slightly different from GNU diff3).
-- The reason is that since we are dealing with arbitary tree, (rather than plain lists as
-- text files are), we match nodes with nodes (embedding), rather than trying to squeeze and
-- shuffle subtrees around.
-- [1,4, 4 <-> 5, 2 <-> 5, 3, 6]
--r012, r021 :: ES CsvF '[Row] '[Row]
--r012 = diff3 r01 r02
--r021 = diff3 r02 r01

--------------------------------------------------------------------------------

type Csv = [Row]

c0, c1, c2, c3, c4 :: Csv
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

c4 = [[1,0,0,2,3],
      [4,9,9,5,6],
      [7,3,3,8,9]]

d01, d02, d03 :: ES CsvF '[Csv] '[Csv]
d01 = gdiff c0 c1
d02 = gdiff c0 c2
d03 = gdiff c0 c3

-- Patching
c1' :: Csv
c1' = case patch Proxy d01 (DCons c0 DNil) of
        DCons x DNil -> x
        
c2PatchFail :: Csv
c2PatchFail = case patch Proxy d02 (DCons c1 DNil) of
            DCons x DNil -> x

--------------------------------------------------------------------------------
-- Diff3 

-- TODO update examples, choose which interface to follow: diff3 or merge3?

-- returns the merged object if the merge is successful,
-- otherwise fails with error printing the conflicts.
diff3Target :: (Family f, Metric f, a :<: f, b :<: f)
            => b -> a -> b -> DList f '[ b ]
diff3Target x o y = 
  case diff3 x o y of
    Left errs -> error (show errs)
    Right e -> target e

mergeCsv :: Csv -> Csv -> Csv -> DList CsvF '[Csv]
mergeCsv = diff3Target 

c012 :: Csv
c012 = dHead $ mergeCsv c1 c0 c2 
 

c023 :: Csv
c023 = dHead $ mergeCsv c2 c0 c3
   
-- Changes merged with no conflicts
--d012 :: ES3 CsvF '[Csv] '[Csv]
--d012 = diff3 d01 d02
--
--c012 :: Csv
--c012 = case patch Proxy d012 (DCons c0 DNil) of
--        (DCons x DNil) -> x
--
--d021 :: ES3 CsvF '[Csv] '[Csv]
--d021 = diff3 d02 d01
--
--c021 :: Csv
--c021 = case patch Proxy d021 (DCons c0 DNil) of
--        (DCons x DNil) -> x
--
---- Example with UpdUpd conflicts
--d013 :: ES3 CsvF '[Csv] '[Csv]
--d013 = diff3 d02 d03
--
--d034 :: ES3 CsvF '[Csv] '[Csv]
--d034 = diff3 d03 d04
--  where d03 = gdiff c0 c3
--        d04 = gdiff c0 c4
--
--c034 :: Csv
--c034 = case patch Proxy d034 (DCons c0 DNil) of
--          DCons x DNil -> x

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

  argsTy NilRow' = tlist
  argsTy ConsRow' = tlist
  argsTy NilInt' = tlist
  argsTy ConsInt' = tlist
  argsTy (Int' _) = tlist
  
  outputTy NilRow' = tlist
  outputTy ConsRow' = tlist
  outputTy NilInt' = tlist
  outputTy ConsInt' = tlist
  outputTy (Int' _) = tlist

instance Metric CsvF where
  distance (Int' x) (Int' y) = if x == y then 0 else 1
  distance NilRow'  NilRow' = 0
  distance ConsRow' ConsRow' = 0
  distance NilInt'  NilInt' = 0
  distance ConsInt' ConsInt' = 0
  distance _ _ = 1

type instance TypesOf CsvF = '[Int, [Int], [[Int]]]

instance Csv :<: CsvF where
  view _ [] = View NilRow' DNil
  view _ (x:xs) = View ConsRow' (DCons x (DCons xs DNil))

  getElem _ = inject

  stringOfTy _ _ = "Csv"

instance [Int] :<: CsvF where
  view _ [] = View NilInt' DNil
  view _ (x:xs) = View ConsInt' (DCons x (DCons xs DNil))

  getElem _ = inject

  stringOfTy _ _ = "[Int]"

instance Int :<: CsvF where
  view _ i = View (Int' i) DNil
  
  getElem _ = inject

  stringOfTy _ _ = "Int"
