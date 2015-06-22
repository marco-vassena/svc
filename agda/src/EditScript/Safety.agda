module EditScript.Safety where

open import EditScript.Core public

open import Relation.Binary.PropositionalEquality
open import Data.List
  
∈-⟦⟧ : ∀ {xs ys as a bs cs} {v : Val bs cs} {α : View as a} {e : ES xs ys} {c : v ~> ⟨ α ⟩} -> c ∈ₑ e -> α ∈ ⟦ e ⟧ 
∈-⟦⟧ (here c) = ∈-here-⟦⟧ c
∈-⟦⟧ (there d p) = ∈-there-⟦⟧ d (∈-⟦⟧ p)

--------------------------------------------------------------------------------

∈-⟪⟫ : ∀ {xs ys as a bs cs} {v : Val bs cs} {α : View as a} {e : ES xs ys} {c : ⟨ α ⟩ ~> v} -> c ∈ₑ e -> α ∈ ⟪ e ⟫
∈-⟪⟫ (here c) = ∈-here-⟪⟫ c
∈-⟪⟫ (there d p) = ∈-there-⟪⟫ d (∈-⟪⟫ p)

--------------------------------------------------------------------------------
-- High-level description of Safety properties using Mapping.

open import EditScript.Mapping
open import Data.Unit

targetOrigin : ∀ {xs ys as a bs cs} {v : Val bs cs} {e : ES xs ys} {α : View as a} -> e ⊢ₑ v ~> ⟨ α ⟩ -> α ∈ ⟦ e ⟧
targetOrigin (Upd α β x) = ∈-⟦⟧ x
targetOrigin (Ins α x) = ∈-⟦⟧ x

sourceOrigin : ∀ {xs ys as a bs cs} {v : Val bs cs} {e : ES xs ys} {α : View as a} -> e ⊢ₑ ⟨ α ⟩ ~> v -> α ∈ ⟪ e ⟫
sourceOrigin (Upd α β x) = ∈-⟪⟫ x
sourceOrigin (Del α x) = ∈-⟪⟫ x

--------------------------------------------------------------------------------
