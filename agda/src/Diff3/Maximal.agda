module Diff3.Maximal where

open import Diff3.Core
open import EditScript.Mapping

open import Data.List

--------------------------------------------------------------------------------

-- We define maximality in terms of the transormations involved.
-- Maximal e₁ e₂ e₃ is satisfied when they are all empty edit scripts (Nil).
-- Maximiality is also retained when one of the two transformations of e₁ and e₂ is identity (Id₁ and Id₂)
-- in which case maximality is preserved adding the other transformation to e₃.
-- Adding the same transformation to all of them preserves maximality (Idem)
data Maximal : ∀ {xs ys zs} -> ES xs ys -> ES xs zs -> ES₃ xs -> Set₁ where
  Nil : Maximal [] [] []
  Id₁ : ∀ {as bs cs ds xs ys zs} {v : Val as bs} {w : Val cs ds}
          {e₁ : ES (as ++ xs) (as ++ ys)} {e₂ : ES (as ++ xs) (cs ++ zs)} {e₃ : ES₃ (as ++ xs) } 
          (f : v ~> v) (g : v ~> w) -> Maximal e₁ e₂ e₃ -> Maximal (f ∷ e₁) (g ∷ e₂) (g ∷ e₃)
  Id₂ : ∀ {as bs cs ds xs ys zs} {v : Val as bs} {w : Val cs ds}
          {e₁ : ES (as ++ xs) (cs ++ ys)} {e₂ : ES (as ++ xs) (as ++ zs)} {e₃ : ES₃ (as ++ xs) } 
          (f : v ~> w) (g : v ~> v) -> Maximal e₁ e₂ e₃ -> Maximal (f ∷ e₁) (g ∷ e₂) (f ∷ e₃)
  Idem : ∀ {as bs cs ds xs ys zs} {u : Val as bs} {v : Val cs ds} 
           {e₁ : ES (as ++ xs) (cs ++ ys)} {e₂ : ES (as ++ xs) (cs ++ zs)} {e₃ : ES₃ (as ++ xs) } 
           (f : u ~> v) -> Maximal e₁ e₂ e₃ -> Maximal (f ∷ e₁) (f ∷ e₂) (f ∷ e₃)
 
--------------------------------------------------------------------------------

-- It means that diff3 must propagate all the changes from e1 and e2
Diff₃-maximal : ∀ {xs ys zs} {e₁ : ES xs ys} {e₂ : ES xs zs} {{p : e₁ ⋎ e₂}} {e₃ : ES₃ xs} -> 
                  Diff₃ e₁ e₂ e₃ -> NoCnf e₃ -> Maximal e₁ e₂ e₃
Diff₃-maximal nil [] = Nil
Diff₃-maximal (merge (Id₁ f g v≠w) d) (.g ∷ q) = Id₁ f g (Diff₃-maximal d q)
Diff₃-maximal (merge (Id₂ f g v≠w) d) (.f ∷ q) = Id₂ f g (Diff₃-maximal d q)
Diff₃-maximal (merge (Idem f) d) (.f ∷ q) = Idem f (Diff₃-maximal d q)

Merged₃-maximal : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {{p : e₁ ⋎ e₂}} {e₃ : ES xs ws} -> 
                    Merged₃ e₁ e₂ e₃ -> Maximal e₁ e₂ ⌞ e₃ ⌟
Merged₃-maximal m = Diff₃-maximal (Merged₃-Diff₃ m) (ES-NoCnf _)
