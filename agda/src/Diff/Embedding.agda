module Diff.Embedding where

open import Data.DTree hiding ([_])
open import EditScript.Embedding
open import EditScript.Mapping
open import Diff.Safety

open import Data.Sum
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

-- TODO move this to EditScript.Embedding
-- The proofs here should follow from the fact that Diff x y e <=> Diff ⟪ e ⟫ ⟦ e ⟧ e

data _⊢ˢ_⊏_ {xs ys} (e : ES xs ys) : ∀ {as bs a b} -> View as a -> View bs b -> Set₁ where
  source-⊏ : ∀ {as bs cs ds es fs gs hs}
           {c : Edit as bs cs ds} {d : Edit es fs gs hs} {i₁ : input c} {i₂ : input d} -> e ⊢ₑ c ⊏ d 
           -> e ⊢ˢ ⌞ c ⌟ ⊏ ⌞ d ⌟

-- Source  ⊏ 
diff-⊏ˢ : ∀ {xs ys as bs a b} {α : View as a} {β : View bs b} {x : DList xs} {y : DList ys} {e : ES xs ys} 
        -> x ⊢ α ⊏ β -> Diff x y e -> e ⊢ˢ α ⊏ β
diff-⊏ˢ (here α x) (Del .α q) with noEraseˢ q x
diff-⊏ˢ (here α x) (Del .α q) | source-∈ {i = i} p = source-⊏ {i₂ = i} (here (Del α) p)
diff-⊏ˢ (here α x) (Upd .α y q) with noEraseˢ q x
diff-⊏ˢ (here α x) (Upd .α y q) | source-∈ {i = i} p = source-⊏ {i₂ = i} (here (Upd α y) p)
diff-⊏ˢ (here α x) (Cpy .α q) with noEraseˢ q x
diff-⊏ˢ (here α x) (Cpy .α q) | source-∈ {i = i} p = source-⊏ {i₂ = i} (here (Cpy α) p)
diff-⊏ˢ (here α x) (Ins y q) with diff-⊏ˢ (here α x) q
diff-⊏ˢ (here ._ x) (Ins y q) | source-⊏ {i₁ = i₁} {i₂ = i₂} p = source-⊏ {i₁ = i₁} {i₂ = i₂} (there (Ins y) p)
diff-⊏ˢ (there p) (Del z q) with diff-⊏ˢ p q
diff-⊏ˢ (there p) (Del z q) | source-⊏ {i₁ = i₁} {i₂ = i₂} x = source-⊏ {i₁ = i₁} {i₂ = i₂} (there (Del z) x)
diff-⊏ˢ (there p) (Upd z y q) with diff-⊏ˢ p q
diff-⊏ˢ (there p) (Upd z y q) | source-⊏ {i₁ = i₁} {i₂ = i₂} x = source-⊏ {i₁ = i₁} {i₂ = i₂} (there (Upd z y) x)
diff-⊏ˢ (there p) (Cpy z q) with diff-⊏ˢ p q
diff-⊏ˢ (there p) (Cpy z q) | source-⊏ {i₁ = i₁} {i₂ = i₂} x = source-⊏ {i₁ = i₁} {i₂ = i₂} (there (Cpy z) x)
diff-⊏ˢ (there p) (Ins y q) with diff-⊏ˢ (there p) q
diff-⊏ˢ (there p) (Ins y q) | source-⊏ {i₁ = i₁} {i₂ = i₂} x = source-⊏ {i₁ = i₁} {i₂ = i₂} (there (Ins y) x)

--------------------------------------------------------------------------------

data _⊢ᵗ_⊏_ : ∀ {xs ys as bs a b} -> ES xs ys -> View as a -> View bs b -> Set₁ where
  target-⊏ : ∀ {as bs cs ds es fs gs hs xs ys} {e : ES xs ys}
           {c : Edit as bs cs ds} {d : Edit es fs gs hs} {o₁ : output c} {o₂ : output d} -> e ⊢ₑ c ⊏ d 
           -> e ⊢ᵗ ⌜ c ⌝ ⊏ ⌜ d ⌝

infixr 3 _⊢ᵗ_⊏_

-- Output  ⊏ 
diff-⊏ₒ : ∀ {xs ys as bs a b} {α : View as a} {β : View bs b} {x : DList xs} {y : DList ys} {e : ES xs ys} 
        -> y ⊢ α ⊏ β -> Diff x y e -> e ⊢ᵗ α ⊏ β
diff-⊏ₒ (here α x) (Del y q) with diff-⊏ₒ (here α x) q
diff-⊏ₒ (here ._ x) (Del y q) | target-⊏ {o₁ = o₁} {o₂ = o₂} r = target-⊏ {o₁ = o₁} {o₂ = o₂} (there (Del y) r)
diff-⊏ₒ (here α x) (Upd y .α q) with noEraseₒ q x
... | target-∈ {o = o} r = target-⊏ {o₂ = o} (here (Upd y α) r)
diff-⊏ₒ (here α x) (Cpy .α q) with noEraseₒ q x
... | target-∈ {o = o} r = target-⊏ {o₂ = o} (here (Cpy α) r)
diff-⊏ₒ (here α x) (Ins .α q) with noEraseₒ q x
... | target-∈ {o = o} r = target-⊏ {o₂ = o} (here (Ins α) r)
diff-⊏ₒ (there p) (Del x q) with diff-⊏ₒ (there p) q
... | target-⊏ {o₁ = o₁} {o₂ = o₂} r = target-⊏ {o₁ = o₁} {o₂ = o₂} (there (Del x) r)
diff-⊏ₒ (there p) (Upd x y q) with diff-⊏ₒ p q
... | target-⊏ {o₁ = o₁} {o₂ = o₂} r = target-⊏ {o₁ = o₁} {o₂ = o₂} (there (Upd x y) r)
diff-⊏ₒ (there p) (Cpy z q) with diff-⊏ₒ p q
... | target-⊏ {o₁ = o₁} {o₂ = o₂} r = target-⊏ {o₁ = o₁} {o₂ = o₂} (there (Cpy z) r)
diff-⊏ₒ (there p) (Ins z q) with diff-⊏ₒ p q
... | target-⊏ {o₁ = o₁} {o₂ = o₂} r = target-⊏ {o₁ = o₁} {o₂ = o₂} (there (Ins z) r)

--------------------------------------------------------------------------------

-- If the edit script has an output then, that value is either inserted or there
-- is a value from which it was generated.
-- ∈~>⟨⟩

-- If ⟪ e ⟫ ⊢ α ⊏ β then e ↦ α ⊏ β, which means that either:  
--   1) α is deleted
--   2) β is deleted
--   3) ∃ γ , φ . e ⊢ₑ ⟨ α ⟩ ~> ⟨ γ ⟩ and e ⊢ₑ ⟨ β ⟩ ~> ⟨ φ ⟩ and ⟦ e ⟧ ⊢ γ ⊏ φ 
preserve-↦ : ∀ {xs ys as bs a b} {e : ES xs ys} {α : View as a} {β : View bs b}
              (p : ⟪ e ⟫ ⊢ α ⊏ β) -> e ↦ α ⊏ β 
preserve-↦ {e = e} p with diff-⊏ˢ p (mkDiff e)
preserve-↦ p | source-⊏ {c = c} x with ∈⟨⟩~> (⊏ₑ-∈₁ x)
preserve-↦ p | source-⊏ {c = c} x | inj₁ a = Del₁ a
preserve-↦ p | source-⊏ {c = c} {d = d} x | inj₂ m with ∈⟨⟩~> (⊏ₑ-∈₂ x)
preserve-↦ p | source-⊏ x | inj₂ m | inj₁ b = Del₂ b
preserve-↦ p | source-⊏ {c = c} {d = d} x | inj₂ (source~> f) | inj₂ (source~> g) 
  = Map₂ f g (⟦⟧-⊏ c d x) 

-- If ⟪ e ⟫ ⊢ α ⊏ β then e ↤ α ⊏ β, which means that either:  
--   1) α is inserted
--   2) β is inserted
--   3) ∃ γ , φ . e ⊢ₑ ⟨ γ ⟩ ~> ⟨ α ⟩ and e ⊢ₑ ⟨ φ ⟩ ~> ⟨ β ⟩ and ⟪ e ⟫ ⊢ γ ⊏ φ 
preserve-↤ : ∀ {xs ys as bs a b} {e : ES xs ys} {α : View as a} {β : View bs b}
              (p : ⟦ e ⟧ ⊢ α ⊏ β) -> e ↤ α ⊏ β 
preserve-↤ {e = e} p with diff-⊏ₒ p (mkDiff e)
preserve-↤ p | target-⊏ x with ∈~>⟨⟩ (⊏ₑ-∈₁ x)
preserve-↤ p | target-⊏ x | inj₁ q = Ins₁ q
preserve-↤ p | target-⊏ x | inj₂ f with ∈~>⟨⟩ (⊏ₑ-∈₂ x)
preserve-↤ p | target-⊏ x | inj₂ f | inj₁ q = Ins₂ q
preserve-↤ p | target-⊏ {c = c} {d = d} x | inj₂ (target~> f) | inj₂ (target~> g) 
  = Map₂ f g (⟪⟫-⊏ c d x)


Diff↦ :  ∀ {xs ys as bs a b} {x : DList xs} {y : DList ys} {e : ES xs ys} {α : View as a} {β : View bs b}
            -> Diff x y e -> x ⊢ α ⊏ β -> e ↦ α ⊏ β
Diff↦ d p rewrite mkDiff⟪ d ⟫ = preserve-↦ p

Diff↤ :  ∀ {xs ys as bs a b} {x : DList xs} {y : DList ys} {e : ES xs ys} {α : View as a} {β : View bs b}
            -> Diff x y e -> y ⊢ α ⊏ β -> e ↤ α ⊏ β
Diff↤ d p rewrite mkDiff⟦ d ⟧ = preserve-↤ p
