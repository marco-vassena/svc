module EditScript.Embedding where

open import Data.DTree hiding ([_])
open import EditScript.Core public
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Diff.Safety
open import Diff3.Safety

∈-dsplit : ∀ {as a} {{ys zs}} {ds : DList (ys ++ zs)} (α : View as a) ->  
           let ds₁ , ds₂ = dsplit ds in α ∈ ds -> α ∈ ds₁ +++ ds₂
∈-dsplit {ds = ds} _ q
  rewrite dsplit-lemma ds = q

--------------------------------------------------------------------------------

∈-⟦⟧  : ∀ {as bs cs ds xs ys} {d : Edit as bs cs ds} {{ o : output d }} {e : ES xs ys} -> d ∈ₑ e -> ⌜ d ⌝ ∈ ⟦ e ⟧
∈-⟦⟧ {{o = o}} {e = e} p = noMadeUpₒ (target-∈ {o = o} p) (mkDiff e)

⟦⟧-lemma : ∀ {{ys}} {{zs}} {as bs cs ds es fs gs hs xs} (c : Edit as bs cs ds) (d : Edit es fs gs hs) (e : ES xs (ys ++ zs))
             {{p : output c}} {{q : output d}} -> ⟦ e ⟧ ⊢ ⌜ c ⌝ ⊏ ⌜ d ⌝ ->
              let ds₁ , ds₂ = dsplit ⟦ e ⟧ in ds₁ +++ ds₂ ⊢ ⌜ c ⌝ ⊏ ⌜ d ⌝
⟦⟧-lemma c d e q rewrite dsplit-lemma ⟦ e ⟧ = q
 
-- This is a property of the ⟦⟧ and the edit-script, not the diff algorithm!!!
⟦⟧-⊏ : ∀ {as bs cs ds es fs gs hs xs ys} {e : ES xs ys}
              (c : Edit as bs cs ds) (d : Edit es fs gs hs) {{o₁ : output c}} {{o₂ : output d}} 
              -> e ⊢ₑ c ⊏ d -> ⟦ e ⟧ ⊢ ⌜ c ⌝ ⊏ ⌜ d ⌝
⟦⟧-⊏ (Ins x) d (here .(Ins x) p) = here x (∈-dsplit ⌜ d ⌝ (∈-⟦⟧ p))
⟦⟧-⊏ (Del x) d {{()}} (here .(Del x) p)
⟦⟧-⊏ (Cpy x) d (here {e = e} .(Cpy x) p) = here x (∈-dsplit ⌜ d ⌝ (∈-⟦⟧ p))
⟦⟧-⊏ (Upd x y) d (here .(Upd x y) p) = here y (∈-dsplit ⌜ d ⌝ (∈-⟦⟧ p))
⟦⟧-⊏ End d {{()}} (here .End x)
⟦⟧-⊏ c d (there {e = e} (Ins x) p) = there (⟦⟧-lemma c d e (⟦⟧-⊏ c d p))
⟦⟧-⊏ c d (there (Del x) p) = ⟦⟧-⊏ c d p
⟦⟧-⊏ c d (there {e = e} (Cpy x) p) = there (⟦⟧-lemma c d e (⟦⟧-⊏ c d p))
⟦⟧-⊏ c d (there {e = e} (Upd x y) p) = there (⟦⟧-lemma c d e (⟦⟧-⊏ c d p))
⟦⟧-⊏ c d (there End p) = ⟦⟧-⊏ c d p

--------------------------------------------------------------------------------
-- Similar lemma for ⟪⟫

∈-⟪⟫  : ∀ {as bs cs ds xs ys} {d : Edit as bs cs ds} {{ i : input d }} {e : ES xs ys} -> d ∈ₑ e -> ⌞ d ⌟ ∈ ⟪ e ⟫
∈-⟪⟫ {{i = i}} {e = e} p = noMadeUpˢ (source-∈ {i = i} p) (mkDiff e)

⟪⟫-lemma : ∀ {{xs ys}} {as bs cs ds es fs gs hs zs} (c : Edit as bs cs ds) (d : Edit es fs gs hs) (e : ES (xs ++ ys) zs)
             {{p : input c}} {{q : input d}} -> ⟪ e ⟫ ⊢ ⌞ c ⌟ ⊏ ⌞ d ⌟ ->
              let ds₁ , ds₂ = dsplit ⟪ e ⟫ in ds₁ +++ ds₂ ⊢ ⌞ c ⌟ ⊏ ⌞ d ⌟
⟪⟫-lemma c d e q rewrite dsplit-lemma ⟪ e ⟫ = q

⟪⟫-⊏ : ∀ {as bs cs ds es fs gs hs xs ys} {e : ES xs ys}
              (c : Edit as bs cs ds) (d : Edit es fs gs hs) {{i₁ : input c}} {{i₂ : input d}} 
              -> e ⊢ₑ c ⊏ d -> ⟪ e ⟫ ⊢ ⌞ c ⌟ ⊏ ⌞ d ⌟
⟪⟫-⊏ (Ins x) d {{()}} (here .(Ins x) o)
⟪⟫-⊏ (Del x) d (here .(Del x) o) = here x (∈-dsplit ⌞ d ⌟ (∈-⟪⟫ o))
⟪⟫-⊏ (Cpy x) d (here .(Cpy x) o) = here x (∈-dsplit ⌞ d ⌟ (∈-⟪⟫ o))
⟪⟫-⊏ (Upd x y) d (here .(Upd x y) o) = here x (∈-dsplit ⌞ d ⌟  (∈-⟪⟫ o))
⟪⟫-⊏ End d {{()}} (here .End o)
⟪⟫-⊏ c d (there (Ins x) q) = ⟪⟫-⊏ c d q
⟪⟫-⊏ c d (there {e = e} (Del x) q) = there (⟪⟫-lemma c d e (⟪⟫-⊏ c d q))
⟪⟫-⊏ c d (there {e = e} (Cpy x) q) = there (⟪⟫-lemma c d e (⟪⟫-⊏ c d q))
⟪⟫-⊏ c d (there {e = e} (Upd x y) q) = there (⟪⟫-lemma c d e (⟪⟫-⊏ c d q))
⟪⟫-⊏ c d (there End q) = ⟪⟫-⊏ c d q

--------------------------------------------------------------------------------
