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

data _⊢ˢ_⊏_ {xs ys} (e : ES xs ys) : ∀ {as bs a b} -> View as a -> View bs b -> Set₁ where
  source-⊏ : ∀ {as bs cs ds es fs gs hs}
           {c : Edit as bs cs ds} {d : Edit es fs gs hs} {i₁ : input c} {i₂ : input d} -> e ⊢ₑ c ⊏ d 
           -> e ⊢ˢ ⌞ c ⌟ ⊏ ⌞ d ⌟

-- Source  ⊏ 
diff-⊏ˢ : ∀ {xs ys as bs a b} {α : View as a} {β : View bs b} {x : DList xs} {y : DList ys} {e : ES xs ys} 
        -> Diff x y e -> x ⊢ α ⊏ β -> e ⊢ˢ α ⊏ β
diff-⊏ˢ (Del α p) (here .α q) with noEraseˢ p q 
diff-⊏ˢ (Del α p) (here .α q) | source-∈ {i = i} r = source-⊏ {i₂ = i} (here (Del α) r)
diff-⊏ˢ (Upd α β p) (here .α q) with noEraseˢ p q
diff-⊏ˢ (Upd α β p) (here .α q) | source-∈ {i = i} r = source-⊏ {i₂ = i} (here (Upd α β) r)
diff-⊏ˢ (Cpy α p) (here .α q) with noEraseˢ p q
diff-⊏ˢ (Cpy α p) (here .α q) | source-∈ {i = i} r = source-⊏ {i₂ = i} (here (Cpy α) r)
diff-⊏ˢ (Ins y p) (here α q) with diff-⊏ˢ p (here α q)
diff-⊏ˢ (Ins y p) (here ._ q) | source-⊏ {i₁ = i₁} {i₂ = i₂} r = source-⊏ {i₁ = i₁} {i₂ = i₂} (there (Ins y) r)
diff-⊏ˢ (Del z p) (there q) with diff-⊏ˢ p q
diff-⊏ˢ (Del z p) (there q) | source-⊏ {i₁ = i₁} {i₂ = i₂} r = source-⊏ {i₁ = i₁} {i₂ = i₂} (there (Del z) r)
diff-⊏ˢ (Upd z y p) (there q) with diff-⊏ˢ p q
diff-⊏ˢ (Upd z y p) (there q) | source-⊏ {i₁ = i₁} {i₂ = i₂} r = source-⊏ {i₁ = i₁} {i₂ = i₂} (there (Upd z y) r)
diff-⊏ˢ (Cpy z p) (there q) with diff-⊏ˢ p q
diff-⊏ˢ (Cpy z p) (there q) | source-⊏ {i₁ = i₁} {i₂ = i₂} r = source-⊏ {i₁ = i₁} {i₂ = i₂} (there (Cpy z) r)
diff-⊏ˢ (Ins y p) (there q) with diff-⊏ˢ p (there q)
diff-⊏ˢ (Ins y p) (there q) | source-⊏ {i₁ = i₁} {i₂ = i₂} r = source-⊏ {i₁ = i₁} {i₂ = i₂} (there (Ins y) r)

--------------------------------------------------------------------------------

data _⊢ᵗ_⊏_ : ∀ {xs ys as bs a b} -> ES xs ys -> View as a -> View bs b -> Set₁ where
  target-⊏ : ∀ {as bs cs ds es fs gs hs xs ys} {e : ES xs ys}
           {c : Edit as bs cs ds} {d : Edit es fs gs hs} {o₁ : output c} {o₂ : output d} -> e ⊢ₑ c ⊏ d 
           -> e ⊢ᵗ ⌜ c ⌝ ⊏ ⌜ d ⌝

infixr 3 _⊢ᵗ_⊏_

-- Output  ⊏ 
diff-⊏ₒ : ∀ {xs ys as bs a b} {α : View as a} {β : View bs b} {x : DList xs} {y : DList ys} {e : ES xs ys} 
        -> Diff x y e -> y ⊢ α ⊏ β -> e ⊢ᵗ α ⊏ β
diff-⊏ₒ (Del x p) (here α q) with diff-⊏ₒ p (here α q)
diff-⊏ₒ (Del x p) (here ._ q) | target-⊏ {o₁ = o₁} {o₂ = o₂} r = target-⊏ {o₁ = o₁} {o₂ = o₂} (there (Del x) r)
diff-⊏ₒ (Upd α β p) (here .β q) with noEraseₒ p q
diff-⊏ₒ (Upd α β p) (here .β q) | target-∈ {o = o} r = target-⊏ {o₂ = o} (here (Upd α β) r)
diff-⊏ₒ (Cpy α p) (here .α q) with noEraseₒ p q
diff-⊏ₒ (Cpy α p) (here .α q) | target-∈ {o = o} r = target-⊏ {o₂ = o} (here (Cpy α) r)
diff-⊏ₒ (Ins α p) (here .α q) with noEraseₒ p q
diff-⊏ₒ (Ins α p) (here .α q) | target-∈ {o = o} r = target-⊏ {o₂ = o} (here (Ins α) r)
diff-⊏ₒ (Del x p) (there q) with diff-⊏ₒ p (there q)
diff-⊏ₒ (Del x p) (there q) | target-⊏ {o₁ = o₁} {o₂ = o₂} r = target-⊏ {o₁ = o₁} {o₂ = o₂} (there (Del x) r)
diff-⊏ₒ (Upd x y p) (there q) with diff-⊏ₒ p q
diff-⊏ₒ (Upd x y p) (there q) | target-⊏ {o₁ = o₁} {o₂ = o₂} r = target-⊏ {o₁ = o₁} {o₂ = o₂} (there (Upd x y) r)
diff-⊏ₒ (Cpy z p) (there q) with diff-⊏ₒ p q
diff-⊏ₒ (Cpy z p) (there q) | target-⊏ {o₁ = o₁} {o₂ = o₂} r = target-⊏ {o₁ = o₁} {o₂ = o₂} (there (Cpy z) r)
diff-⊏ₒ (Ins z p) (there q) with diff-⊏ₒ p q
diff-⊏ₒ (Ins z p) (there q) | target-⊏ {o₁ = o₁} {o₂ = o₂} r = target-⊏ {o₁ = o₁} {o₂ = o₂} (there (Ins z) r)

--------------------------------------------------------------------------------

-- If ⟪ e ⟫ ⊢ α ⊏ β then e ↦ α ⊏ β, which means that either:  
--   1) α is deleted
--   2) β is deleted
--   3) ∃ γ , φ . e ⊢ₑ ⟨ α ⟩ ~> ⟨ γ ⟩ and e ⊢ₑ ⟨ β ⟩ ~> ⟨ φ ⟩ and ⟦ e ⟧ ⊢ γ ⊏ φ 
preserve-↦ : ∀ {xs ys as bs a b} {e : ES xs ys} {α : View as a} {β : View bs b}
              (p : ⟪ e ⟫ ⊢ α ⊏ β) -> e ↦ α ⊏ β 
preserve-↦ {e = e} p with diff-⊏ˢ (mkDiff e) p
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
preserve-↤ {e = e} p with diff-⊏ₒ (mkDiff e) p
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
