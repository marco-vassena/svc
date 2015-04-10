{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}

module Repo.Head where

import Data.Hashable
import GHC.Exts
import GHC.Prim
import Generics.Instant.GDiff
import Repo.Path
import Debug.Trace

-- Abstract data type that tracks the diff of an object in a Path and 
-- maintain the latest version of the object
data Head a = Head a (Path a)
  deriving Show

-- Smart constructor that creates an Head out of a path.
mkHead :: GDiff a => Path a -> Head a
mkHead r@(Root z) = Head z r
mkHead n@(Node p d e) = Head x n
  where x = patch' e (value (mkHead p))
mkHead m@(Merge p q d e) = mkHeadFromLca (lca p q) k
  where k h =  Head (patch' e (value h)) m

mkHeadFromLca :: GDiff a => Lca a -> (Head a -> Head a) -> Head a
mkHeadFromLca (One r)     k = k (mkHead r)
mkHeadFromLca (Two r0 r1) k = mkHeadFromLca (lca r0 r1) k

-- Calls error if patch fails.
patch' :: GDiff a => EditScript -> a -> a
patch' e x = 
  case patch e x of
    Just y -> y
    Nothing -> error "patch': patch failed"

value :: Head a -> a
value (Head x p) = x

path :: Head a -> Path a
path (Head x p) = p

-- Used to intuitively track the history of changes
-- Adds a new version
add :: GDiff a => a -> Head a -> Head a
add x (Head y p) = Head x (node p d)
  where d = diff y x

mergeHeads :: GDiff a => a -> Head a -> Head a -> Head a
mergeHeads x (Head _ p) (Head _ q) = Head x (mergeWith x p q)

-- Maybe this should be the default smart constructor for
-- merge rather than merge.
mergeWith :: GDiff a => a -> Path a -> Path a -> Path a
mergeWith x p1 p2 = merge p1 p2 (diff v x)
  where v = value h 
        h = mkHeadFromLca (lca p1 p2) id

-- An edit script produced by diff3
data EDiff3 = Cons Edit EDiff3
            | Conflict [Edit] [Edit] EDiff3 -- TODO use single Edit rather than list
            | End
  deriving Show

toEDiff3 :: [Edit] -> EDiff3
toEDiff3 = foldr Cons End

append :: EDiff3 -> EDiff3 -> EDiff3
append End ys = ys
append (Cons x xs) ys = Cons x (append xs ys)
append (Conflict c1 c2 xs) ys = Conflict c1 c2 (append xs ys)

-- TODO probably the interface should be :
--    diff3 :: GDiff a => a -> a -> a -> EDiff3
-- TODO here I should check if one or both are actually the same as the ancestor
diff3 :: EditScript -> EditScript -> EDiff3
diff3 (ES _ xs) (ES _ ys) = diff3' xs ys  

hashOf :: Edit -> Int
hashOf (Cpy x) = hash x
hashOf (Ins x) = hash x
hashOf (Del x) = hash x

-- * I don't think that this can work properly when we have actually
--   structured data. The script is flat (list).
-- * I don't have any guarantee that the script produced will be applicable
--   to the original
diff3' :: [Edit] -> [Edit] -> EDiff3
diff3' []     []     = End
diff3' []     xs     = Conflict [] xs End
diff3' xs     []     = Conflict xs [] End
diff3' (x:xs) (y:ys) | hash x == hash y = Cons x (diff3' xs ys)
diff3' (Ins x : xs) (Ins y : ys) = Conflict [Ins x] [Ins y] (diff3' xs ys)
diff3' (Ins x : xs) (Cpy y : ys) = Cons (Ins x) (diff3' xs (Cpy y : ys))
diff3' (Cpy x : xs) (Ins y : ys) = Cons (Ins y) (diff3' (Cpy x : xs) ys)
diff3' a@(Del x : xs) b@(Cpy y : ys) =
  case span (\e -> hash e /= hash (Ins x)) a of
    (_, []) -> Conflict a b End
    (ps, _:ss) -> 
      case align ss ys of
        ([], [], as, bs) -> toEDiff3 ps `append` Cons (Ins x) (diff3' as bs)
        (c1, c2, as, bs) -> toEDiff3 ps `append` Cons (Ins x) (Conflict c1 (map cpy2Ins c2) (diff3' as bs))
diff3' (Cpy x : xs) (Del y : ys) = diff3' (Del y : ys) (Cpy x : xs)
diff3' a b = error $ "woops " ++ show a ++ " " ++ show b

--align :: [Edit] -> [Edit] -> 
align xs ys = go [] [] xs ys
  where go c1 c2 a@(Cpy x : xs) b@(Cpy y : ys) | hash x == hash y = (reverse c1, reverse c2, a, b)
        go c1 c2 a@(Cpy x:xs) (y:ys) = go c1 (y:c2) a ys
        go c1 c2 (x:xs) (y:ys) = go (x:c1) (y:c2) xs ys
        go c1 c2 xs     []     = (reverse c1, reverse c2, xs, [])
        go c1 c2 []     ys     = (reverse c1, reverse c2, [], ys)


-- TODO what should happen for Ins / Del

cpy2Ins :: Edit -> Edit
cpy2Ins (Cpy x) = Ins x
cpy2Ins e       = e

data Strategy = Their
              | Mine
  deriving (Show, Eq)

solveWithStrategy :: Strategy -> EDiff3 -> [Edit]
solveWithStrategy s e = go e
  where go End = []
        go (Cons e es) = e : go es
        go (Conflict mine their es) = 
          case s of 
            Mine -> mine ++ go es
            Their -> their ++ go es

es :: [Edit] -> EditScript
es xs = ES l xs
  where !(I# l) = length xs

a,o,b :: [Int]
o = [1,2,3,4,5,6]
a = [1,4,5,2,3,6]
b = [1,2,4,5,3,6]

cb = [1,4,5,2,4,5,3,6]
ca = [1,4,5,2,3,6]
co = [1,4,5,2,3,4,5,6]

oa = diff o a
ob = diff o b
oab = diff3 oa ob

ocb = diff o cb
oca = diff o ca
oco = diff o co


--------------------------------------------------------------------------------

x,y,z :: [Int]
x = [1,2,3,4,5,6,7]
y = [1,4,5,2,3,6,9,7]
z = [1,2,4,5,3,6,8,7]

xy = diff x y
xz = diff x z

prettyDiff :: EditScript -> EditScript -> String
prettyDiff (ES _ xs) (ES _ ys) = unlines $ f xs ys
  where f :: [Edit] -> [Edit] -> [String]
        f xs [] = map show xs
        f [] ys = zipWith (++) (repeat (spcs 0)) (map show ys)
        f (x:xs) (y:ys) = (show x ++ spcs (length (show x)) ++ show y) : f xs ys
        spcs n = replicate (50 - n) ' '
--diff x y
-- ES 9 [Cpy [1,2,3,4],Cpy 1,Cpy [2,3,4],Cpy 2,Cpy [3,4],Del 3,Del [4],Cpy 4,Cpy []]

-- diff x z
-- ES 12 [Cpy [1,2,3,4],Cpy 1,Cpy [2,3,4],Del 2,Ins 4,Cpy [3,4],Del 3,Ins 5,Cpy [4],Del 4,Ins 2,Cpy []]

--dxyz :: EditScript
--dxyz = ES l xs
--  where !(ES l1 xy) = diff x y
--        !(ES l2 xz) = diff x z
--        xs = take 11 xz ++ drop 4 xy
--        !(I# l) = length xs

--xs = [cpy [1,2,3,4],cpy 1,cpy [2,3,4],del 2,ins 4,cpy [3,4],del 3,ins 5,cpy [4],del 4,ins 2,
--              cpy [3,4],del 3,del [4],cpy 4,cpy []]

cpy :: GDiff a => a -> Edit
cpy = Cpy . Ex

ins :: GDiff a => a -> Edit
ins = Ins . Ex

del :: GDiff a => a -> Edit
del = Del . Ex

--a, o, b :: [Int]
--a = [1,4,5,2,3,6]
--o = [1,2,3,4,5,6]
--b = [1,2,4,5,3,6]
--
--ao = diff o a
--bo = diff o b

