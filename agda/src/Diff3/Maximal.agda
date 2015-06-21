module Diff3.Maximal where

open import Diff3.Core
open import EditScript.Mapping

open import Data.List

--------------------------------------------------------------------------------

-- It is possible to pattern match directly on this data type.
-- When edit script are involved, first patter match on the edit script (or some auxilairy datatype such as Diff₃)
-- and then on Maximal.
-- For inj₁ and inj₂ we do not enforce that they must be insert.
-- Since we are focusing on maximality alone, we don't really care about what kind of edit is used.
data Maximal : Mapping -> Mapping -> Mapping -> Set₁ where
  stop : Maximal [] [] []
  inj₁ : ∀ {xs ys zs v w} -> (x : v ~> w) (p : Maximal xs ys zs) -> Maximal (x ∷ xs) ys (x ∷ zs)
  inj₂ : ∀ {xs ys zs v w} -> (y : v ~> w) (p : Maximal xs ys zs) -> Maximal xs (y ∷ ys) (y ∷ zs)
  inj₁₂ : ∀ {xs ys zs a b c d} {x : a ~> b} {y : a ~> c} {z : a ~> d} ->
            (m : z ≔ x ⊔ y) (p : Maximal xs ys zs) -> Maximal (x ∷ xs) (y ∷ ys) (z ∷ zs)
 
--------------------------------------------------------------------------------
-- It means that diff3 must propagate all the changes from e1 and e2
maximal : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} -> 
           Diff₃ e₁ e₂ e₃ -> Maximal (mapping e₁) (mapping e₂) (mapping e₃)
maximal End = stop
maximal (InsIns x d) = inj₁₂ (Idem (Ins x)) (maximal d)
maximal (Ins₁ x d) = inj₁ (Ins x) (maximal d)
maximal (Ins₂ x d) = inj₂ (Ins x) (maximal d)
maximal (DelDel x d) = inj₁₂ (Idem (Del x)) (maximal d)
maximal (DelCpy x d) = inj₁₂ (Id₂ (Del x) (Upd x x) (λ ())) (maximal d)
maximal (CpyDel x d) = inj₁₂ (Id₁ (Upd x x) (Del x) (λ ())) (maximal d)
maximal (UpdUpd x y d) = inj₁₂ (Idem (Upd x y)) (maximal d)
