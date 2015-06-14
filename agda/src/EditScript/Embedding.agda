module EditScript.Embedding where

open import EditScript.Core public
open import Data.DTree

open import Data.List
open import Data.Product
open import Relation.Nullary

-- TODO separate module Safety!

∈-⟦⟧  : ∀ {as bs cs ds xs ys} {d : Edit as bs cs ds} {{ o : output d }} {e : ES xs ys} -> d ∈ₑ e -> ⌜ d ⌝ ∈ ⟦ e ⟧
∈-⟦⟧ (here (Ins x)) = ∈-here x
∈-⟦⟧ {{o = ()}} (here (Del x))
∈-⟦⟧ (here (Cpy x)) = ∈-here x
∈-⟦⟧ (here (Upd x y)) = ∈-here y
∈-⟦⟧ {{o = ()}} (here End)
∈-⟦⟧ {d = d} {{o = o}} (there (Ins x) p) = ∈-there (∈-dsplit ⌜ d ⌝ (∈-⟦⟧ p))
∈-⟦⟧ (there (Del x) p) = ∈-⟦⟧ p
∈-⟦⟧ {d = d} (there (Cpy x) p) = ∈-there (∈-dsplit ⌜ d ⌝ (∈-⟦⟧ p))
∈-⟦⟧ {d = d} (there (Upd x y) p) = ∈-there (∈-dsplit ⌜ d ⌝ (∈-⟦⟧ p))
∈-⟦⟧ (there End p) = ∈-⟦⟧ p

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
∈-⟪⟫ {{i = ()}} (here (Ins x))
∈-⟪⟫ (here (Del x)) = ∈-here x
∈-⟪⟫ (here (Cpy x)) = ∈-here x
∈-⟪⟫ (here (Upd x y)) = ∈-here x
∈-⟪⟫ {{i = ()}} (here End)
∈-⟪⟫ (there (Ins x) p) = ∈-⟪⟫ p
∈-⟪⟫ {d = d} (there (Del x) p) = ∈-there (∈-dsplit ⌞ d ⌟ (∈-⟪⟫ p))
∈-⟪⟫ {d = d} (there (Cpy x) p) = ∈-there (∈-dsplit ⌞ d ⌟ (∈-⟪⟫ p))
∈-⟪⟫ {d = d} (there (Upd x y) p) = ∈-there (∈-dsplit ⌞ d ⌟ (∈-⟪⟫ p))
∈-⟪⟫ (there End p) = ∈-⟪⟫ p

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
