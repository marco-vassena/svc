module EditScript2.Embedding where

open import EditScript2.Core public
open import EditScript2.Safety
open import Data.DTree

open import Data.List
open import Data.Product

⟦⟧-lemma : ∀ {{ys}} {{zs}} {as bs a b xs} {α : View as a} {β : View bs b} (e : ES xs (ys ++ zs))
              -> ⟦ e ⟧ ⊢ α ⊏ β ->
             let ds₁ , ds₂ = dsplit ⟦ e ⟧ in ds₁ +++ ds₂ ⊢ α ⊏ β
⟦⟧-lemma e q rewrite dsplit-lemma ⟦ e ⟧ = q
 
-- This is a property of the ⟦⟧ and the edit-script, not the diff algorithm!!!
⟦⟧-⊏ : ∀ {as bs cs ds es fs a b xs ys} {e : ES xs ys} {α : View as a} {β : View bs b} {v : Val cs ds} {w : Val es fs}
              (c : v ~> ⟨ α ⟩) (d : w ~> ⟨ β ⟩) 
              -> e ⊢ₑ c ⊏ d -> ⟦ e ⟧ ⊢ α ⊏ β
⟦⟧-⊏ (Ins α) d (here .(Ins α) o) = here α (∈-dsplit _ (∈-⟦⟧ o))
⟦⟧-⊏ (Upd α β) d (here .(Upd α β) o) = here β (∈-dsplit _ (∈-⟦⟧ o))
⟦⟧-⊏ c d (there {e = e} (Ins α) p) = there (⟦⟧-lemma e (⟦⟧-⊏ c d p))
⟦⟧-⊏ c d (there (Del α) p) = ⟦⟧-⊏ c d p
⟦⟧-⊏ c d (there {e = e} (Upd α β) p) = there (⟦⟧-lemma e (⟦⟧-⊏ c d p))
⟦⟧-⊏ c d (there Nop p) = ⟦⟧-⊏ c d p

--------------------------------------------------------------------------------
-- Similar lemma for ⟪⟫

⟪⟫-lemma : ∀ {{xs}} {{ys}} {as bs a b zs} {α : View as a} {β : View bs b} (e : ES (xs ++ ys) zs)
              -> ⟪ e ⟫ ⊢ α ⊏ β ->
             let ds₁ , ds₂ = dsplit ⟪ e ⟫ in ds₁ +++ ds₂ ⊢ α ⊏ β
⟪⟫-lemma e q rewrite dsplit-lemma ⟪ e ⟫ = q

⟪⟫-⊏ : ∀ {as bs cs ds es fs a b xs ys} {e : ES xs ys} {α : View as a} {β : View bs b} {v : Val cs ds} {w : Val es fs}
              (c : ⟨ α ⟩ ~> v) (d : ⟨ β ⟩ ~> w) 
              -> e ⊢ₑ c ⊏ d -> ⟪ e ⟫ ⊢ α ⊏ β
⟪⟫-⊏ (Del α) d (here .(Del α) o) = here α (∈-dsplit _ (∈-⟪⟫ o))
⟪⟫-⊏ (Upd α β) d (here .(Upd α β) o) = here α (∈-dsplit _ (∈-⟪⟫ o))
⟪⟫-⊏ c d (there (Ins α) p) = ⟪⟫-⊏ c d p
⟪⟫-⊏ c d (there {e = e} (Del α) p) = there (⟪⟫-lemma e (⟪⟫-⊏ c d p))
⟪⟫-⊏ c d (there {e = e} (Upd α β) p) = there (⟪⟫-lemma e (⟪⟫-⊏ c d p))
⟪⟫-⊏ c d (there Nop p) = ⟪⟫-⊏ c d p

--------------------------------------------------------------------------------
