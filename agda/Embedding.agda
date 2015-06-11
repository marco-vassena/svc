module Embedding where

open import DTree hiding ([_])
open import View
open import Diff
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Diff3
open import Safety

∈-dsplit : ∀ {as a} {{ys zs}} {ds : DList (ys ++ zs)} (α : View as a) ->  
           let ds₁ , ds₂ = dsplit ds in α ∈ ds -> α ∈ ds₁ +++ ds₂
∈-dsplit {ds = ds} _ q
  rewrite dsplit-lemma ds = q

--------------------------------------------------------------------------------

∈-⟦⟧  : ∀ {as bs cs ds xs ys} {d : Edit as bs cs ds} {{ o : output d }} {e : ES xs ys} -> d ∈ₑ e -> ⌞ d ⌟ ∈ ⟦ e ⟧
∈-⟦⟧ {{o = o}} {e = e} p = noMadeUpₒ (target-∈ {o = o} p) (mkDiff e)

⟦⟧-lemma : ∀ {{ys}} {{zs}} {as bs cs ds es fs gs hs xs} (c : Edit as bs cs ds) (d : Edit es fs gs hs) (e : ES xs (ys ++ zs))
             {{p : output c}} {{q : output d}} -> ⟦ e ⟧ ⊢ ⌞ c ⌟ ⊏ ⌞ d ⌟ ->
              let ds₁ , ds₂ = dsplit ⟦ e ⟧ in ds₁ +++ ds₂ ⊢ ⌞ c ⌟ ⊏ ⌞ d ⌟
⟦⟧-lemma c d e q rewrite dsplit-lemma ⟦ e ⟧ = q
 
-- This is a property of the ⟦⟧ and the edit-script, not the diff algorithm!!!
⟦⟧-⊏ : ∀ {as bs cs ds es fs gs hs xs ys} {e : ES xs ys} {d : Edit es fs gs hs}
              (c : Edit as bs cs ds) -> {{o₁ : output c}} {{o₂ : output d}} 
              -> e ⊢ₑ c ⊏ d -> ⟦ e ⟧ ⊢ ⌞ c ⌟ ⊏ ⌞ d ⌟
⟦⟧-⊏ {d = d} (Ins x) (here .(Ins x) p) = here x (∈-dsplit ⌞ d ⌟ (∈-⟦⟧ p))
⟦⟧-⊏ (Del x) {{()}} (here .(Del x) p)
⟦⟧-⊏ {d = d} (Cpy x) (here {e = e} .(Cpy x) p) = here x (∈-dsplit ⌞ d ⌟ (∈-⟦⟧ p))
⟦⟧-⊏ {d = d} (Upd x y) (here .(Upd x y) p) = here y (∈-dsplit ⌞ d ⌟ (∈-⟦⟧ p))
⟦⟧-⊏ End {{()}} (here .End x)
⟦⟧-⊏ {d = d} c (there {e = e} (Ins x) p) = there (⟦⟧-lemma c d e (⟦⟧-⊏ c p))
⟦⟧-⊏ c (there (Del x) p) = ⟦⟧-⊏ c p
⟦⟧-⊏ {d = d} c (there {e = e} (Cpy x) p) = there (⟦⟧-lemma c d e (⟦⟧-⊏ c p))
⟦⟧-⊏ {d = d} c (there {e = e} (Upd x y) p) = there (⟦⟧-lemma c d e (⟦⟧-⊏ c p))
⟦⟧-⊏ c (there End p) = ⟦⟧-⊏ c p

--------------------------------------------------------------------------------
-- Similar lemma for ⟪⟫

∈-⟪⟫  : ∀ {as bs cs ds xs ys} {d : Edit as bs cs ds} {{ i : input d }} {e : ES xs ys} -> d ∈ₑ e -> ⌜ d ⌝ ∈ ⟪ e ⟫
∈-⟪⟫ {{i = i}} {e = e} p = noMadeUpˢ (source-∈ {i = i} p) (mkDiff e)

⟪⟫-lemma : ∀ {{xs ys}} {as bs cs ds es fs gs hs zs} (c : Edit as bs cs ds) (d : Edit es fs gs hs) (e : ES (xs ++ ys) zs)
             {{p : input c}} {{q : input d}} -> ⟪ e ⟫ ⊢ ⌜ c ⌝ ⊏ ⌜ d ⌝ ->
              let ds₁ , ds₂ = dsplit ⟪ e ⟫ in ds₁ +++ ds₂ ⊢ ⌜ c ⌝ ⊏ ⌜ d ⌝
⟪⟫-lemma c d e q rewrite dsplit-lemma ⟪ e ⟫ = q


⟪⟫-⊏ : ∀ {as bs cs ds es fs gs hs xs ys} {e : ES xs ys} {d : Edit es fs gs hs}
              (c : Edit as bs cs ds) -> {{i₁ : input c}} {{i₂ : input d}} 
              -> e ⊢ₑ c ⊏ d -> ⟪ e ⟫ ⊢ ⌜ c ⌝ ⊏ ⌜ d ⌝
⟪⟫-⊏ (Ins x) {{()}} (here .(Ins x) o)
⟪⟫-⊏ {d = d} (Del x) (here .(Del x) o) = here x (∈-dsplit ⌜ d ⌝ (∈-⟪⟫ o))
⟪⟫-⊏ {d = d} (Cpy x) (here .(Cpy x) o) = here x (∈-dsplit ⌜ d ⌝ (∈-⟪⟫ o))
⟪⟫-⊏ {d = d} (Upd x y) (here .(Upd x y) o) = here x (∈-dsplit ⌜ d ⌝  (∈-⟪⟫ o))
⟪⟫-⊏ End {{()}} (here .End o)
⟪⟫-⊏ c (there (Ins x) q) = ⟪⟫-⊏ c q
⟪⟫-⊏ {d = d} c (there {e = e} (Del x) q) = there (⟪⟫-lemma c d e (⟪⟫-⊏ c q))
⟪⟫-⊏ {d = d} c (there {e = e} (Cpy x) q) = there (⟪⟫-lemma c d e (⟪⟫-⊏ c q))
⟪⟫-⊏ {d = d} c (there {e = e} (Upd x y) q) = there (⟪⟫-lemma c d e (⟪⟫-⊏ c q))
⟪⟫-⊏ c (there End q) = ⟪⟫-⊏ c q

--------------------------------------------------------------------------------

-- diff3-⊏ : ∀ {as bs cs ds es fs gs hs xs ys zs ws} 
--             {c : Edit as bs cs ds} {d : Edit es fs gs hs} {{c₁ : change c}} {{c₂ : change d}}
--             {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws}
--             -> e₁ ⊢ₑ c ⊏ d -> Diff₃ e₁ e₂ e₃ -> e₃ ⊢ₑ c ⊏ d
-- diff3-⊏ (here (Ins x) o) (InsIns .x q) = here (Ins x) (noBackOutChanges₁ o q)
-- diff3-⊏ (here (Ins x) o) (Ins₁ .x q) = here (Ins x) (noBackOutChanges₁ o q)
-- diff3-⊏ (here (Ins x) o) (Ins₂ y q) = there (Ins y) (diff3-⊏ (here (Ins x) o) q)
-- diff3-⊏ (here (Del x) o) (Ins₂ y q) = there (Ins y) (diff3-⊏ (here (Del x) o) q)
-- diff3-⊏ (here (Del x) o) (DelDel .x q) = here (Del x) (noBackOutChanges₁ o q)
-- diff3-⊏ (here (Del x) o) (DelCpy .x q) = here (Del x) (noBackOutChanges₁ o q)
-- diff3-⊏ {{c₁ = ()}} (here (Cpy x) o) q
-- diff3-⊏ (here (Upd x y) o) (Ins₂ z q) = there (Ins z) (diff3-⊏ (here (Upd x y) o) q)
-- diff3-⊏ (here (Upd x y) o) (UpdCpy .x .y q) = here (Upd x y) (noBackOutChanges₁ o q)
-- diff3-⊏ (here (Upd x y) o) (UpdUpd .x .y q) = here (Upd x y) (noBackOutChanges₁ o q)
-- diff3-⊏ {{c₁ = ()}} (here End o) q
-- diff3-⊏ (there (Ins x) p) (InsIns .x q) = there (Ins x) (diff3-⊏ p q)
-- diff3-⊏ (there (Ins x) p) (Ins₁ .x q) = there (Ins x) (diff3-⊏ p q)
-- diff3-⊏ (there (Ins x) p) (Ins₂ y q) = there (Ins y) (diff3-⊏ (there (Ins x) p) q)
-- diff3-⊏ (there (Del x) p) (Ins₂ y q) = there (Ins y) (diff3-⊏ (there (Del x) p) q)
-- diff3-⊏ (there (Del x) p) (DelDel .x q) = there (Del x) (diff3-⊏ p q)
-- diff3-⊏ (there (Del x) p) (DelCpy .x q) = there (Del x) (diff3-⊏ p q)
-- diff3-⊏ (there (Cpy x) p) (Ins₂ y q) = there (Ins y) (diff3-⊏ (there (Cpy x) p) q)
-- diff3-⊏ (there (Cpy x) p) (CpyDel .x q) = there (Del x) (diff3-⊏ p q)
-- diff3-⊏ (there (Cpy x) p) (CpyCpy .x q) = there (Cpy x) (diff3-⊏ p q)
-- diff3-⊏ (there (Cpy x) p) (CpyUpd .x y q) = there (Upd x y) (diff3-⊏ p q)
-- diff3-⊏ (there (Upd x y) p) (Ins₂ z q) = there (Ins z) (diff3-⊏ (there (Upd x y) p) q)
-- diff3-⊏ (there (Upd x y) p) (UpdCpy .x .y q) = there (Upd x y) (diff3-⊏ p q)
-- diff3-⊏ (there (Upd x y) p) (UpdUpd .x .y q) = there (Upd x y) (diff3-⊏ p q)
-- diff3-⊏ (there End p) q = diff3-⊏ p q

open import Safety

data _⊢ˢ_⊏_ {xs ys} (e : ES xs ys) : ∀ {as bs a b} -> View as a -> View bs b -> Set₁ where
  source-⊏ : ∀ {as bs cs ds es fs gs hs}
           {c : Edit as bs cs ds} {d : Edit es fs gs hs} {i₁ : input c} {i₂ : input d} -> e ⊢ₑ c ⊏ d 
           -> e ⊢ˢ ⌜ c ⌝ ⊏ ⌜ d ⌝

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

data _⊢ᵗ_⊏_ : ∀ {xs ys as bs a b} -> ES xs ys -> View as a -> View bs b -> Set₁ where
  target-⊏ : ∀ {as bs cs ds es fs gs hs xs ys} {e : ES xs ys}
           {c : Edit as bs cs ds} {d : Edit es fs gs hs} {o₁ : output c} {o₂ : output d} -> e ⊢ₑ c ⊏ d 
           -> e ⊢ᵗ ⌞ c ⌟ ⊏ ⌞ d ⌟

--------------------------------------------------------------------------------

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
