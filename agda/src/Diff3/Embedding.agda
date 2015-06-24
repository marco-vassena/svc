module Diff3.Embedding where

open import Data.DTree hiding ([_])
open import EditScript.Embedding
open import Diff.Safety
open import Diff3.Safety

open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Data.Empty using (⊥-elim)

diff3-⊏₁ : ∀ {as bs cs ds es fs gs hs xs ys zs ws} {u : Val as bs} {v : Val cs ds} {w : Val es fs} {z : Val gs hs}
            {f : u ~> v} {g : w ~> z} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} -> 
            {{c₁ : Change f}} {{c₂ : Change g}} -> e₁ ⊢ₑ f ⊏ g -> Merged₃ e₁ e₂ e₃ -> e₃ ⊢ₑ f ⊏ g
diff3-⊏₁ {{c₁ = IsChange v≠w}} (here f o) (cons (Id₁ .f g₁ v≠w₁) q) = ⊥-elim (v≠w refl)
diff3-⊏₁ (here f o) (cons (Id₂ .f g₁ v≠w) q) = here f {!!}
diff3-⊏₁ (here f o) (cons (Idem .f) q) = here f {!o!}
diff3-⊏₁ (there a p) (cons m q) = there _ (diff3-⊏₁ p q)

-- diff3-⊏₁ (here (Ins x) o) (InsIns .x q) = here (Ins x) (noBackOutChanges₁ o q)
-- diff3-⊏₁ (here (Ins x) o) (Ins₁ .x q) = here (Ins x) (noBackOutChanges₁ o q)
-- diff3-⊏₁ (here (Ins x) o) (Ins₂ y q) = there (Ins y) (diff3-⊏₁ (here (Ins x) o) q)
-- diff3-⊏₁ (here (Del x) o) (Ins₂ y q) = there (Ins y) (diff3-⊏₁ (here (Del x) o) q)
-- diff3-⊏₁ (here (Del x) o) (DelDel .x q) = here (Del x) (noBackOutChanges₁ o q)
-- diff3-⊏₁ (here (Del x) o) (DelCpy .x q) = here (Del x) (noBackOutChanges₁ o q)
-- diff3-⊏₁ (here (Upd x y) o) (Ins₂ z q) = there (Ins z) (diff3-⊏₁ (here (Upd x y) o) q)
-- diff3-⊏₁ (here (Upd x .x) o) (CpyDel .x q) with x =?= x
-- diff3-⊏₁ {{()}} (here (Upd x .x) o) (CpyDel .x q) | yes refl
-- diff3-⊏₁ (here (Upd x .x) o) (CpyDel .x q) | no ¬p = ⊥-elim (¬p refl)
-- diff3-⊏₁ (here (Upd x y) o) (UpdUpd .x .y q) = here (Upd x y) (noBackOutChanges₁ o q)
-- diff3-⊏₁ (there (Ins x) p) (InsIns .x q) = there (Ins x) (diff3-⊏₁ p q)
-- diff3-⊏₁ (there (Ins x) p) (Ins₁ .x q) = there (Ins x) (diff3-⊏₁ p q)
-- diff3-⊏₁ (there (Ins x) p) (Ins₂ y q) = there (Ins y) (diff3-⊏₁ (there (Ins x) p) q)
-- diff3-⊏₁ (there (Del x) p) (Ins₂ y q) = there (Ins y) (diff3-⊏₁ (there (Del x) p) q)
-- diff3-⊏₁ (there (Del x) p) (DelDel .x q) = there (Del x) (diff3-⊏₁ p q)
-- diff3-⊏₁ (there (Del x) p) (DelCpy .x q) = there (Del x) (diff3-⊏₁ p q)
-- diff3-⊏₁ (there (Upd x y) p) (Ins₂ z q) = there (Ins z) (diff3-⊏₁ (there (Upd x y) p) q)
-- diff3-⊏₁ (there (Upd x .x) p) (CpyDel .x q) = there (Del x) (diff3-⊏₁ p q)
-- diff3-⊏₁ (there (Upd x y) p) (UpdUpd .x .y q) = there (Upd x y) (diff3-⊏₁ p q)

-- diff3-⊏₂ : ∀ {as bs cs ds es fs gs hs xs ys zs ws} 
--             {c : Edit as bs cs ds} {d : Edit es fs gs hs} {{c₁ : change c}} {{c₂ : change d}}
--             {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws}
--             -> e₂ ⊢ₑ c ⊏ d -> Merged₃ e₁ e₂ e₃ -> e₃ ⊢ₑ c ⊏ d
-- diff3-⊏₂ p d = diff3-⊏₁ p (Merged₃-sym d)

--------------------------------------------------------------------------------

open import EditScript.Mapping
open import Diff.Embedding
open import Data.Sum

-- Merged₃↦ : ∀ {xs ys zs ws as bs a b} {x : DList xs} {y : DList ys} {z : DList zs}
--            {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} {α : View as a} {β : View bs b} ->
--            Diff x y e₁ -> Diff x z e₂ -> Merged₃ e₁ e₂ e₃ -> x ⊢ α ⊏ β -> e₃ ↦ α ⊏ β
-- Merged₃↦ {e₃ = e₃} d₁ d₂ d₃ p rewrite
--   trans (mkDiff⟪ d₁ ⟫) (sym (Merged₃⟪ d₃ ⟫)) = Diff↦ (mkDiff e₃) p

-- -- Since e₃ is maximal, it includes all the changes from e₁ and e₂ therefore e₃ ↤ α ⊏ β 
-- -- holds as the inserts cases cover when α and β comes from e₁ or e₂. 
-- Merged₃↤ : ∀ {xs ys zs ws as bs a b} {x : DList xs} {y : DList ys} {z : DList zs}
--            {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} {α : View as a} {β : View bs b} ->
--            Diff x y e₁ -> Diff x z e₂ -> Merged₃ e₁ e₂ e₃ -> ⟦ e₃ ⟧ ⊢ α ⊏ β -> e₃ ↤ α ⊏ β 
-- Merged₃↤ {e₃ = e₃} d₁ d₂ d₃ p = Diff↤ (mkDiff e₃) p
