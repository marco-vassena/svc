-- This module explicits the mapping between nodes induced by an edit script

module Mapping where

open import Diff
open import View
open import Data.List
open import Data.Unit
open import Relation.Binary.PropositionalEquality hiding ([_])

data Val : Set₁ where
  ⊥ : Val
  ⟨_⟩ : ∀ {a as} -> View as a -> Val

data _⊢ₑ_~>_  {xs ys} (e : ES xs ys) : Val -> Val -> Set₁ where
  Cpy : ∀ {as a} (α : View as a) -> Cpy α ∈ₑ e -> e ⊢ₑ ⟨ α ⟩ ~> ⟨ α ⟩
  Upd : ∀ {as bs a} (α : View as a) (β : View bs a) -> Upd α β ∈ₑ e -> e ⊢ₑ ⟨ α ⟩ ~> ⟨ β ⟩ 
  Del : ∀ {as a} (α : View as a) -> Del α ∈ₑ e -> e ⊢ₑ ⟨ α ⟩ ~> ⊥
  Ins : ∀ {as a} (α : View as a) -> Ins α ∈ₑ e -> e ⊢ₑ ⊥ ~> ⟨ α ⟩

infixr 3 _⊢ₑ_~>_

--------------------------------------------------------------------------------

-- TODO this part actually belongs to Embedding ... here to avoid recompiling all the other proofs
open import Embedding
open import Diff3
open import DTree
open import Data.List


open import Function
open import Data.Sum
import Data.Sum as S
open import Data.Empty hiding (⊥)
open import Safety

-- Edit scripts preserve ⊏ relation.
data _↦_⊏_ {xs ys as a bs b} (e : ES xs ys) (α : View as a) (β : View bs b) : Set₁ where
  Del₁ : e ⊢ₑ ⟨ α ⟩ ~> ⊥ -> e ↦ α ⊏ β
  Del₂ : e ⊢ₑ ⟨ β ⟩ ~> ⊥ -> e ↦ α ⊏ β
  Map₂ : ∀ {cs ds c d} {γ : View cs c} {φ : View ds d} 
             -> e ⊢ₑ ⟨ α ⟩ ~> ⟨ γ ⟩ -> e ⊢ₑ ⟨ β ⟩ ~> ⟨ φ ⟩ -> ⟦ e ⟧ ⊢ γ ⊏ φ -> e ↦ α ⊏ β
 
data Mapˢ {xs ys as a bs cs ds es} (e : ES xs ys) (α : View as a) (c : Edit bs cs ds es) : Set₁ where
  source~> : ∀ {i : input c} {o : output c} -> e ⊢ₑ ⟨ α ⟩ ~> ⟨ ⌞ c ⌟ ⟩ -> Mapˢ e α c

there~> : ∀ {xs ys as bs cs ds} {v₁ v₂ : Val} (c : Edit as bs cs ds) {e : ES (as ++ xs) (bs ++ ys)}
                -> e ⊢ₑ v₁ ~> v₂ -> c ∻ e ⊢ₑ v₁ ~> v₂
there~> c (Cpy α x) = Cpy α (there c x)
there~> c (Upd α β x) = Upd α β (there c x)
there~> c (Del α x) = Del α (there c x)
there~> c (Ins α x) = Ins α (there c x)

thereMapˢ : ∀ {xs ys as a bs cs ds es fs gs hs is} {e : ES (fs ++ xs) (gs ++ ys)} {α : View as a} {c : Edit bs cs ds es} 
            (d : Edit fs gs hs is) -> Mapˢ e α c -> Mapˢ (d ∻ e) α c
thereMapˢ d (source~> {i = i} {o = o} x) = source~> {i = i} {o = o} (there~> d x)

--------------------------------------------------------------------------------
-- These functions convert an edit that belongs to an edit script, 
-- e ⊢ₑ_~>_ statement.

-- If the edit script has an input then, that value is either deleted, or there
-- is a value to which it is mapped.
∈⟨⟩~> : ∀ {xs ys as bs cs ds} {e : ES xs ys} {d : Edit as bs cs ds} 
         {{i : input d }} 
         -> d ∈ₑ e -> (e ⊢ₑ ⟨ ⌜ d ⌝ ⟩ ~> ⊥) ⊎ (Mapˢ e ⌜ d ⌝ d)
∈⟨⟩~> {{i = ()}} (here (Ins x))
∈⟨⟩~> (here (Del x)) = inj₁ (Del x (here (Del x)))
∈⟨⟩~> (here (Cpy x)) = inj₂ (source~> (Cpy x (here (Cpy x))))
∈⟨⟩~> (here (Upd x y)) = inj₂ (source~> (Upd x y (here (Upd x y))))
∈⟨⟩~> {{i = ()}} (here End)
∈⟨⟩~> (there d p) = S.map (there~> d) (thereMapˢ d) (∈⟨⟩~> p)

-- If the edit script has an output then, that value is either inserted or there
-- is a value from which it was generated.
-- ∈~>⟨⟩

-- Final lemma:
-- If ⟪ e ⟫ ⊢ α ⊏ β then e ↦ α ⊏ β, which means that either:  
--   1) α is deleted
--   2) β is deleted
--   3) ∃ γ , φ . e ⊢ₑ ⟨ α ⟩ ~> ⟨ γ ⟩ and e ⊢ₑ ⟨ β ⟩ ~> ⟨ φ ⟩ and ⟦ e ⟧ ⊢ γ ⊏ φ 
preserve-⊏ : ∀ {xs ys as bs a b} {e : ES xs ys}  
              {α : View as a} {β : View bs b}
              (p : ⟪ e ⟫ ⊢ α ⊏ β) -> e ↦ α ⊏ β 
preserve-⊏ {e = e} p with diff-⊏ˢ p (mkDiff e)
preserve-⊏ p | source-⊏ {c = c} x  with ∈⟨⟩~> (⊏ₑ-∈₁ x)
preserve-⊏ p | source-⊏ {c = c} x | inj₁ a = Del₁ a
preserve-⊏ p | source-⊏ {c = c} {d = d} x | inj₂ m with ∈⟨⟩~> (⊏ₑ-∈₂ x)
preserve-⊏ p | source-⊏ x | inj₂ m | inj₁ b = Del₂ b
preserve-⊏ p | source-⊏ {c = c} {d = d} x | inj₂ (source~> f) | inj₂ (source~> g) 
  = Map₂ f g (⟦⟧-⊏ c d x) 
