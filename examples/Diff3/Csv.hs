{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Csv where

import Data.DiffUtils.Diff
import Data.DiffUtils.Diff3
import Data.Proxy
import Data.Type.Equality

type Row = [Int]

r0, r1, r2 :: Row
r0 = [1,2,3,4,5,6]
r1 = [1,4,5,2,3,6]
r2 = [1,2,4,5,3,6]

r01, r02 :: ES '[Row] '[Row]
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

d01, d02, d03 :: ES '[Csv] '[Csv]
d01 = gdiff c0 c1
d02 = gdiff c0 c2
d03 = gdiff c0 c3

--------------------------------------------------------------------------------
-- Diff3 

-- TODO update examples, choose which interface to follow: diff3 or merge3?

-- returns the merged object if the merge is successful,
-- otherwise fails with error printing the conflicts.
diff3Target :: (Diff a, Diff b) => b -> a -> b -> DList '[ b ]
diff3Target x o y = 
  case diff3 x o y of
    Left errs -> error (show errs)
    Right e -> target e

mergeCsv :: Csv -> Csv -> Csv -> Csv
mergeCsv x o y = fromDTree (dHead d)
  where d :: DList '[Csv] 
        d = diff3Target x o y

mergeRow :: Row -> Row -> Row -> Row
mergeRow x o y = fromDTree (dHead d)
  where d :: DList '[Row]
        d = diff3Target x o y

c012 :: Csv
c012 = mergeCsv c1 c0 c2 

c023 :: Csv
c023 = mergeCsv c2 c0 c3
   
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
-- List instance

data ListF xs a where
  Nil :: ListF '[] [a]
  Cons :: ListF '[ a, [a] ] [a]

instance Diff a => Diff [a] where
  type FamilyOf [a] = ListF
  
  string Nil = "[]"
  string Cons = "(:)"
 
  Nil =?= Nil = Just Refl
  Cons =?= Cons = Just Refl
  _ =?= _ = Nothing

  fromDTree (Node Nil DNil) = []
  fromDTree (Node Cons (DCons x (DCons xs DNil))) = fromDTree x : fromDTree xs

  toDTree [] = Node Nil DNil
  toDTree (x:xs) = Node Cons ds 
    where ds = DCons (toDTree x) $ DCons (toDTree xs) DNil

  argsTy Nil = tlist
  argsTy Cons = tlist
 
  distance Nil Nil = 0
  distance Cons Cons = 0
  distance _ _ = 1

--------------------------------------------------------------------------------
-- Int instances

data IntF xs a where
  Int' :: Int -> IntF '[] Int

instance Diff Int where
  type FamilyOf Int = IntF

  string (Int' i) = show i

  (Int' x) =?= (Int' y) = if x == y then Just Refl else Nothing

  fromDTree (Node (Int' n) DNil) = n
  
  toDTree n = Node (Int' n) DNil
  
  argsTy (Int' _) = TNil

  distance (Int' x) (Int' y) = if x == y then 0 else 1
