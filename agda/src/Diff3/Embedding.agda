module Diff3.Embedding where

open import Data.DTree hiding ([_])
open import EditScript.Embedding
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Diff.Safety
open import Diff3.Safety


-- TODO move this to another module just for Diff₃ lemmas
diff3-⊏₁ : ∀ {as bs cs ds es fs gs hs xs ys zs ws} 
            {c : Edit as bs cs ds} {d : Edit es fs gs hs} {{c₁ : change c}} {{c₂ : change d}}
            {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws}
            -> e₁ ⊢ₑ c ⊏ d -> Diff₃ e₁ e₂ e₃ -> e₃ ⊢ₑ c ⊏ d
diff3-⊏₁ (here (Ins x) o) (InsIns .x q) = here (Ins x) (noBackOutChanges₁ o q)
diff3-⊏₁ (here (Ins x) o) (Ins₁ .x q) = here (Ins x) (noBackOutChanges₁ o q)
diff3-⊏₁ (here (Ins x) o) (Ins₂ y q) = there (Ins y) (diff3-⊏₁ (here (Ins x) o) q)
diff3-⊏₁ (here (Del x) o) (Ins₂ y q) = there (Ins y) (diff3-⊏₁ (here (Del x) o) q)
diff3-⊏₁ (here (Del x) o) (DelDel .x q) = here (Del x) (noBackOutChanges₁ o q)
diff3-⊏₁ (here (Del x) o) (DelCpy .x q) = here (Del x) (noBackOutChanges₁ o q)
diff3-⊏₁ {{c₁ = ()}} (here (Cpy x) o) q
diff3-⊏₁ (here (Upd x y) o) (Ins₂ z q) = there (Ins z) (diff3-⊏₁ (here (Upd x y) o) q)
diff3-⊏₁ (here (Upd x y) o) (UpdCpy .x .y q) = here (Upd x y) (noBackOutChanges₁ o q)
diff3-⊏₁ (here (Upd x y) o) (UpdUpd .x .y q) = here (Upd x y) (noBackOutChanges₁ o q)
diff3-⊏₁ {{c₁ = ()}} (here End o) q
diff3-⊏₁ (there (Ins x) p) (InsIns .x q) = there (Ins x) (diff3-⊏₁ p q)
diff3-⊏₁ (there (Ins x) p) (Ins₁ .x q) = there (Ins x) (diff3-⊏₁ p q)
diff3-⊏₁ (there (Ins x) p) (Ins₂ y q) = there (Ins y) (diff3-⊏₁ (there (Ins x) p) q)
diff3-⊏₁ (there (Del x) p) (Ins₂ y q) = there (Ins y) (diff3-⊏₁ (there (Del x) p) q)
diff3-⊏₁ (there (Del x) p) (DelDel .x q) = there (Del x) (diff3-⊏₁ p q)
diff3-⊏₁ (there (Del x) p) (DelCpy .x q) = there (Del x) (diff3-⊏₁ p q)
diff3-⊏₁ (there (Cpy x) p) (Ins₂ y q) = there (Ins y) (diff3-⊏₁ (there (Cpy x) p) q)
diff3-⊏₁ (there (Cpy x) p) (CpyDel .x q) = there (Del x) (diff3-⊏₁ p q)
diff3-⊏₁ (there (Cpy x) p) (CpyCpy .x q) = there (Cpy x) (diff3-⊏₁ p q)
diff3-⊏₁ (there (Cpy x) p) (CpyUpd .x y q) = there (Upd x y) (diff3-⊏₁ p q)
diff3-⊏₁ (there (Upd x y) p) (Ins₂ z q) = there (Ins z) (diff3-⊏₁ (there (Upd x y) p) q)
diff3-⊏₁ (there (Upd x y) p) (UpdCpy .x .y q) = there (Upd x y) (diff3-⊏₁ p q)
diff3-⊏₁ (there (Upd x y) p) (UpdUpd .x .y q) = there (Upd x y) (diff3-⊏₁ p q)
diff3-⊏₁ (there End p) q = diff3-⊏₁ p q

diff3-⊏₂ : ∀ {as bs cs ds es fs gs hs xs ys zs ws} 
            {c : Edit as bs cs ds} {d : Edit es fs gs hs} {{c₁ : change c}} {{c₂ : change d}}
            {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws}
            -> e₂ ⊢ₑ c ⊏ d -> Diff₃ e₁ e₂ e₃ -> e₃ ⊢ₑ c ⊏ d
diff3-⊏₂ p d = diff3-⊏₁ p (Diff₃-sym d)
