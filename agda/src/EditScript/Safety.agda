module EditScript.Safety where

open import EditScript.Core public

open import Relation.Binary.PropositionalEquality
open import Data.List

∈-⟦⟧ :  ∀ {xs ys bs cs ds es} {e : ES xs ys} {c : Edit bs cs ds es} {o : output c} -> c ∈ₑ e -> ⌜ c ⌝ ∈ ⟦ e ⟧
∈-⟦⟧ q = aux refl q
  where aux : ∀ {xs ys bs cs ds es} {e : ES xs ys} {c : Edit bs cs ds es}
                {{o : output c}} {α : View (outputArgs c) (outputTy c)} -> ⌜ c ⌝ ≡ α -> c ∈ₑ e -> α ∈ ⟦ e ⟧
        aux refl (here c) = ∈-here-⟦⟧ c
        aux eq (there d p) = ∈-there-⟦⟧ d (aux eq p)

--------------------------------------------------------------------------------

∈-⟪⟫ :  ∀ {xs ys bs cs ds es} {e : ES xs ys} {c : Edit bs cs ds es} {i : input c} -> c ∈ₑ e -> ⌞ c ⌟ ∈ ⟪ e ⟫
∈-⟪⟫ p = aux refl p
  where aux : ∀ {xs ys bs cs ds es} {e : ES xs ys} {c : Edit bs cs ds es} {{i : input c}} 
                {α : View (inputArgs c) (inputTy c)} -> ⌞ c ⌟ ≡ α -> c ∈ₑ e -> α ∈ ⟪ e ⟫
        aux refl (here c) = ∈-here-⟪⟫ c
        aux eq (there d q) = ∈-there-⟪⟫ d (aux eq q)

--------------------------------------------------------------------------------
-- High-level description of Safety properties using Mapping.

open import EditScript.Mapping
open import Data.Unit

targetOrigin : ∀ {v xs ys as a} {e : ES xs ys} {α : View as a} -> e ⊢ₑ v ~> ⟨ α ⟩ -> α ∈ ⟦ e ⟧
targetOrigin (Cpy α x) = ∈-⟦⟧ x
targetOrigin (Upd α β x) = ∈-⟦⟧ x
targetOrigin (Ins α x) = ∈-⟦⟧ x

sourceOrigin : ∀ {v xs ys as a} {e : ES xs ys} {α : View as a} -> e ⊢ₑ ⟨ α ⟩ ~> v -> α ∈ ⟪ e ⟫
sourceOrigin (Cpy α x) = ∈-⟪⟫ x
sourceOrigin (Upd α β x) = ∈-⟪⟫ x
sourceOrigin (Del α x) = ∈-⟪⟫ x

--------------------------------------------------------------------------------
