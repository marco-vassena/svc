module HList where

open import Data.List
open import Data.Product using (_×_ ; _,_)

data HList : List Set -> Set where
  [] : HList []
  _∷_ : ∀ {A xs} -> A -> HList xs -> HList (A ∷ xs)

append : ∀ {xs ys} -> HList xs -> HList ys -> HList (xs ++ ys)
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

hmap : ∀ {xs} -> {F : Set -> Set} -> (f :  {A : Set} -> A -> F A ) -> HList xs -> HList (map F xs)
hmap f [] = []
hmap f (x ∷ xs) = (f x) ∷ (hmap f xs)

hmap' : ∀ {xs} -> {F : Set -> Set} -> (f :  {A : Set} -> F A -> F A ) -> HList (map F xs) -> HList (map F xs)
hmap' {[]} f [] = []
hmap' {_ ∷ _} f (x ∷ xs) = (f x) ∷ (hmap' f xs)

hfoldr : ∀ {xs} {B : Set} -> ({A : Set} -> A -> B -> B) -> B -> HList xs -> B
hfoldr f e [] = e
hfoldr f e (x ∷ xs) = f x (hfoldr f e xs)

hmap2List : ∀ {xs} {B : Set} -> (f : {A : Set} -> A -> B) -> HList xs -> List B
hmap2List f [] = []
hmap2List f (x ∷ xs) = f x ∷ hmap2List f xs 
                                           
convert : ∀ {xs} -> List (HList xs) -> HList (map List xs)
convert {[]} _ = []
convert {A ∷ As} [] = [] ∷ (convert [])
convert {A ∷ As} (x ∷ xs) = hmap' reverse (foldr merge (hmap [_] x) xs)
  where merge : ∀ {As} -> HList As -> HList (map List As) -> HList (map List As)
        merge {[]} [] [] = []
        merge {A ∷ As} (x ∷ xs) (ys ∷ yss) = (x ∷ ys) ∷ (merge xs yss)

hcons : ∀ {A As} -> A -> HList As -> HList (A ∷ As) 
hcons = _∷_

-- The opposite of convert 
unpack : ∀ {As} -> HList (map List As) -> List (HList As)
unpack {[]} [] = [] ∷ [] -- Here I need to repeat Nil as many time as necessary
unpack {A ∷ As} (xs ∷ xss) = zipWith hcons xs (unpack xss)

split : ∀ {xs ys} -> HList (xs ++ ys) -> HList xs × HList ys  
split {[]} hs = [] , hs
split {x ∷ xs} (h ∷ hs) with split {xs} hs
split {x ∷ xs} (h ∷ hs) | hs₁ , hs₂ = (h ∷ hs₁) , hs₂

hHead : ∀ {x xs} -> HList (x ∷ xs) -> x
hHead (x ∷ _) = x

data SameLength {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} : List A -> List B -> Set where
  base : SameLength [] []
  rec : ∀ {a b as bs} -> SameLength as bs -> SameLength (a ∷ as) (b ∷ bs)

hunzip : ∀ {As Bs} -> SameLength As Bs -> HList (zipWith _×_ As Bs) -> (HList As × HList Bs)
hunzip {[]} {[]} p [] = [] , []
hunzip {[]} {x ∷ Bs} () hs
hunzip {x ∷ As} {[]} () hs
hunzip {A ∷ As} {B ∷ Bs} (rec p) (h ∷ hs) with hunzip p hs
hunzip {A ∷ As} {B ∷ Bs} (rec p) ((a , b) ∷ hs) | as , bs = (a ∷ as) , (b ∷ bs)

hZipWith : ∀ {As Bs F} -> SameLength As Bs -> (∀ {A B} -> A -> B -> F A B) -> HList As -> HList Bs -> HList (zipWith F As Bs)
hZipWith base f [] [] = []
hZipWith (rec p) f (a ∷ as) (b ∷ bs) = f a b ∷ hZipWith p f as bs

hzip : ∀ {As Bs} -> SameLength As Bs -> HList As -> HList Bs -> HList (zipWith _×_ As Bs)
hzip p = hZipWith p _,_
