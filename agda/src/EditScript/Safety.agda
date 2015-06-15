module EditScript.Safety where

open import EditScript.Core public

open import Relation.Binary.PropositionalEquality
open import Data.List

∈-⟦⟧' : ∀ {xs ys bs cs ds es} {e : ES xs ys} {c : Edit bs cs ds es}
          {{o : output c}} {α : View (outputArgs c) (outputTy c)} -> ⌜ c ⌝ ≡ α -> c ∈ₑ e -> α ∈ ⟦ e ⟧
∈-⟦⟧' refl (here c) = ∈-here-⟦⟧ c
∈-⟦⟧' eq (there d p) = ∈-there-⟦⟧ d (∈-⟦⟧' eq p)

∈-⟦⟧ :  ∀ {xs ys bs cs ds es} {e : ES xs ys} {c : Edit bs cs ds es} {{o : output c}} -> c ∈ₑ e -> ⌜ c ⌝ ∈ ⟦ e ⟧
∈-⟦⟧ p = ∈-⟦⟧' refl p

--------------------------------------------------------------------------------

∈-⟪⟫' : ∀ {xs ys bs cs ds es} {e : ES xs ys} {c : Edit bs cs ds es}
          {{i : input c}} {α : View (inputArgs c) (inputTy c)} -> ⌞ c ⌟ ≡ α -> c ∈ₑ e -> α ∈ ⟪ e ⟫
∈-⟪⟫' refl (here c) = ∈-here-⟪⟫ c
∈-⟪⟫' eq (there d p) = ∈-there-⟪⟫ d (∈-⟪⟫' eq p)

∈-⟪⟫ :  ∀ {xs ys bs cs ds es} {e : ES xs ys} {c : Edit bs cs ds es} {{i : input c}} -> c ∈ₑ e -> ⌞ c ⌟ ∈ ⟪ e ⟫
∈-⟪⟫ p = ∈-⟪⟫' refl p

--------------------------------------------------------------------------------
-- High-level description of Safety properties using Mapping.

open import EditScript.Mapping
open import Data.Unit

noTargetErase : ∀ {v xs ys as a} {e : ES xs ys} {α : View as a} -> e ⊢ₑ v ~> ⟨ α ⟩ -> α ∈ ⟦ e ⟧
noTargetErase (Cpy α x) = ∈-⟦⟧ {{o = tt}} x
noTargetErase (Upd α β x) = ∈-⟦⟧ {{o = tt}} x
noTargetErase (Ins α x) = ∈-⟦⟧ {{o = tt}} x

noSourceErase : ∀ {v xs ys as a} {e : ES xs ys} {α : View as a} -> e ⊢ₑ ⟨ α ⟩ ~> v -> α ∈ ⟪ e ⟫
noSourceErase (Cpy α x) = ∈-⟪⟫ {{i = tt}} x
noSourceErase (Upd α β x) = ∈-⟪⟫ {{i = tt}} x
noSourceErase (Del α x) = ∈-⟪⟫ {{i = tt}} x
