module Diff3.Maximal where

open import Diff3.Core
open import EditScript.Mapping

open import Data.List

--------------------------------------------------------------------------------

-- It is possible to pattern match directly on this data type.
-- When edit script are involved, first patter match on the edit script (or some auxilairy datatype such as Diff₃)
-- and then on Maximal.
data Maximal : Mapping -> Mapping -> Mapping -> Set where
  stop : Maximal [] [] []
  inj₁ : ∀ {xs ys zs v w} -> (x : v ~> w) -> (p : Maximal xs ys zs) -> Maximal (x ∷ xs) ys (x ∷ zs)
  inj₂ : ∀ {xs ys zs v w} -> (y : v ~> w) (p : Maximal xs ys zs) -> Maximal xs (y ∷ ys) (y ∷ zs)
  inj₁₂ : ∀ {xs ys zs a b c d e f} {x : a ~> b} {y : c ~> d} {z : e ~> f} ->
            (m : z ≔ x ⊔ y) (p : Maximal xs ys zs) -> Maximal (x ∷ xs) (y ∷ ys) (z ∷ zs)
 
--------------------------------------------------------------------------------
-- It means that diff3 must propagate all the changes from e1 and e2
maximal : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} -> 
           Diff₃ e₁ e₂ e₃ -> Maximal (mapping e₁) (mapping e₂) (mapping e₃)
maximal End = stop
maximal (InsIns x d) = inj₁₂ (Same (Ins x)) (maximal d)
maximal (Ins₁ x d) = inj₁ (Ins x) (maximal d)
maximal (Ins₂ x d) = inj₂ (Ins x) (maximal d)
maximal (DelDel x d) = inj₁₂ (Same (Del x)) (maximal d)
maximal (DelCpy x d) = inj₁₂ (Change₁ (Del x) (Cpy x)) (maximal d)
maximal (CpyDel x d) = inj₁₂ (Change₂ (Cpy x) (Del x)) (maximal d)
maximal (CpyCpy x d) = inj₁₂ (Same (Cpy x)) (maximal d)
maximal (CpyUpd x y d) = inj₁₂ (Change₂ (Cpy x) (Upd x y)) (maximal d)
maximal (UpdCpy x y d) = inj₁₂ (Change₁ (Upd x y) (Cpy x)) (maximal d)
maximal (UpdUpd x y d) = inj₁₂ (Same (Upd x y)) (maximal d)
