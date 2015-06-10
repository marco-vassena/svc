module Embedding where

open import DTree hiding ([_])
open import View
open import Diff
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])

∈-dsplit : ∀ {as bs cs ds'} {{ys zs}} {ds : DList (ys ++ zs)} (d : Edit as bs cs ds') {{ p : output d }} ->  
           let ds₁ , ds₂ = dsplit ds in ⌞ d ⌟ ∈ ds -> ⌞ d ⌟ ∈ ds₁ +++ ds₂
∈-dsplit {ds = ds} _ q
  rewrite dsplit-lemma ds = q

∈ₑ-∈  : ∀ {as bs cs ds xs ys} {d : Edit as bs cs ds} {{ p : output d }} {e : ES xs ys} -> d ∈ₑ e -> ⌞ d ⌟ ∈ ⟦ e ⟧
∈ₑ-∈ (here {e = e} (Ins x)) = ∈-here x 
∈ₑ-∈ {{p = ()}} (here (Del x))
∈ₑ-∈ (here {e = e} (Cpy x)) = ∈-here x
∈ₑ-∈ (here {e = e} (Upd x y)) = ∈-here y
∈ₑ-∈ {{p = ()}} (here End)
∈ₑ-∈ {d = d} (there {e = e} (Ins x) q) = ∈-there (∈-dsplit d (∈ₑ-∈ q))
∈ₑ-∈ (there (Del x) q) = ∈ₑ-∈ q
∈ₑ-∈ {d = d} {{p = p}} (there {e = e} (Cpy x) q) = ∈-there (∈-dsplit d (∈ₑ-∈ q))
∈ₑ-∈ {d = d} (there (Upd x x₁) q) = ∈-there (∈-dsplit d (∈ₑ-∈ q))
∈ₑ-∈ (there End q) = ∈ₑ-∈ q

⟦⟧-lemma : ∀ {{ys}} {{zs}} {as bs cs ds es fs gs hs xs} (c : Edit as bs cs ds) (d : Edit es fs gs hs) (e : ES xs (ys ++ zs))
             {{p : output c}} {{q : output d}} -> ⟦ e ⟧ ⊢ ⌞ c ⌟ ⊏ ⌞ d ⌟ ->
              let ds₁ , ds₂ = dsplit ⟦ e ⟧ in ds₁ +++ ds₂ ⊢ ⌞ c ⌟ ⊏ ⌞ d ⌟
⟦⟧-lemma c d e q rewrite dsplit-lemma ⟦ e ⟧ = q

preserves-⊏ : ∀ {as bs cs ds es fs gs hs xs ys} {e : ES xs ys} {d : Edit es fs gs hs}
              (c : Edit as bs cs ds) -> {{p : output c}} {{q : output d}} 
              -> e ⊢ₑ c ⊏ d -> ⟦ e ⟧ ⊢ ⌞ c ⌟ ⊏ ⌞ d ⌟
preserves-⊏ {d = d} (Ins x) (here .(Ins x) p) = here x (∈-dsplit d {!!}) -- (∈-dsplit d (∈ₑ-∈ p))
preserves-⊏ (Del x) {{()}} (here .(Del x) p)
preserves-⊏ {d = d} (Cpy x) (here {e = e} .(Cpy x) p) = here x (∈-dsplit d (∈ₑ-∈ p))
preserves-⊏ {d = d} (Upd x y) (here .(Upd x y) p) = here y (∈-dsplit d (∈ₑ-∈ p))
preserves-⊏ End {{()}} (here .End x)
preserves-⊏ {d = d} c (there {e = e} (Ins x) p) = there (⟦⟧-lemma c d e (preserves-⊏ c p))
preserves-⊏ c (there (Del x) p) = preserves-⊏ c p
preserves-⊏ {d = d} c (there {e = e} (Cpy x) p) = there (⟦⟧-lemma c d e (preserves-⊏ c p))
preserves-⊏ {d = d} c (there {e = e} (Upd x y) p) = there (⟦⟧-lemma c d e (preserves-⊏ c p))
preserves-⊏ c (there End p) = preserves-⊏ c p

open import Relation.Nullary
open import Diff3
open import Safety

diff3-⊏ : ∀ {as bs cs ds es fs gs hs xs ys zs ws} 
            {c : Edit as bs cs ds} {d : Edit es fs gs hs} {{c₁ : change c}} {{c₂ : change d}}
            {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws}
            -> e₁ ⊢ₑ c ⊏ d -> Diff₃ e₁ e₂ e₃ -> e₃ ⊢ₑ c ⊏ d
diff3-⊏ (here (Ins x) o) (InsIns .x q) = here (Ins x) (noBackOutChanges₁ o q)
diff3-⊏ (here (Ins x) o) (Ins₁ .x q) = here (Ins x) (noBackOutChanges₁ o q)
diff3-⊏ (here (Ins x) o) (Ins₂ y q) = there (Ins y) (diff3-⊏ (here (Ins x) o) q)
diff3-⊏ (here (Del x) o) (Ins₂ y q) = there (Ins y) (diff3-⊏ (here (Del x) o) q)
diff3-⊏ (here (Del x) o) (DelDel .x q) = here (Del x) (noBackOutChanges₁ o q)
diff3-⊏ (here (Del x) o) (DelCpy .x q) = here (Del x) (noBackOutChanges₁ o q)
diff3-⊏ {{c₁ = ()}} (here (Cpy x) o) q
diff3-⊏ (here (Upd x y) o) (Ins₂ z q) = there (Ins z) (diff3-⊏ (here (Upd x y) o) q)
diff3-⊏ (here (Upd x y) o) (UpdCpy .x .y q) = here (Upd x y) (noBackOutChanges₁ o q)
diff3-⊏ (here (Upd x y) o) (UpdUpd .x .y q) = here (Upd x y) (noBackOutChanges₁ o q)
diff3-⊏ {{c₁ = ()}} (here End o) q
diff3-⊏ (there (Ins x) p) (InsIns .x q) = there (Ins x) (diff3-⊏ p q)
diff3-⊏ (there (Ins x) p) (Ins₁ .x q) = there (Ins x) (diff3-⊏ p q)
diff3-⊏ (there (Ins x) p) (Ins₂ y q) = there (Ins y) (diff3-⊏ (there (Ins x) p) q)
diff3-⊏ (there (Del x) p) (Ins₂ y q) = there (Ins y) (diff3-⊏ (there (Del x) p) q)
diff3-⊏ (there (Del x) p) (DelDel .x q) = there (Del x) (diff3-⊏ p q)
diff3-⊏ (there (Del x) p) (DelCpy .x q) = there (Del x) (diff3-⊏ p q)
diff3-⊏ (there (Cpy x) p) (Ins₂ y q) = there (Ins y) (diff3-⊏ (there (Cpy x) p) q)
diff3-⊏ (there (Cpy x) p) (CpyDel .x q) = there (Del x) (diff3-⊏ p q)
diff3-⊏ (there (Cpy x) p) (CpyCpy .x q) = there (Cpy x) (diff3-⊏ p q)
diff3-⊏ (there (Cpy x) p) (CpyUpd .x y q) = there (Upd x y) (diff3-⊏ p q)
diff3-⊏ (there (Upd x y) p) (Ins₂ z q) = there (Ins z) (diff3-⊏ (there (Upd x y) p) q)
diff3-⊏ (there (Upd x y) p) (UpdCpy .x .y q) = there (Upd x y) (diff3-⊏ p q)
diff3-⊏ (there (Upd x y) p) (UpdUpd .x .y q) = there (Upd x y) (diff3-⊏ p q)
diff3-⊏ (there End p) q = diff3-⊏ p q

data _⊢ₑ_~>_  {xs ys} (e : ES xs ys) : ∀ {as bs a} -> View as a -> View bs a -> Set₁ where
  Cpy : ∀ {as a} (α : View as a) -> Cpy α ∈ₑ e -> e ⊢ₑ α ~> α
  Upd : ∀ {as bs a} (α : View as a) (β : View bs a) -> Upd α β ∈ₑ e -> e ⊢ₑ α ~> β 

infixr 3 _⊢ₑ_~>_

open import Data.Sum

-- merge : ∀ {as bs cs a xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {α  : View as a} {β : View bs a} {γ : View cs a} ->
--           e₁ ⊢ₑ α ~> β -> e₂ ⊢ₑ α ~> γ -> (p : e₁ ~ e₂) ->
--           let e₁₂ = diff3 e₁ e₂ p in (q : e₁₂ ↓ ws) -> ( toES p q ⊢ₑ α ~> β) ⊎ (toES p q ⊢ₑ α ~> γ)
-- merge (Cpy γ x) (Cpy .γ x₁) p q = {!!}
-- merge (Cpy α x) (Upd .α γ x₁) p q = {!!}
-- merge (Upd γ β x) (Cpy .γ x₁) p q = {!!}
-- merge (Upd α β x) (Upd .α γ x₁) p q = {!!}

open import Safety

data _⊢ˢ_⊏_ : ∀ {xs ys as bs a b} -> ES xs ys -> View as a -> View bs b -> Set₁ where
  source-⊏ : ∀ {as bs cs ds es fs gs hs xs ys} {e : ES xs ys}
           {c : Edit as bs cs ds} {d : Edit es fs gs hs} {i₁ : input c} {i₂ : input d} -> e ⊢ₑ c ⊏ d 
           -> e ⊢ˢ ⌜ c ⌝ ⊏ ⌜ d ⌝

-- Source  ⊏ 
diff⊏ : ∀ {xs ys as bs a b} {α : View as a} {β : View bs b} {x : DList xs} {y : DList ys} {e : ES xs ys} 
        -> x ⊢ α ⊏ β -> Diff x y e -> e ⊢ˢ α ⊏ β
diff⊏ (here α x) (Del .α q) with noEraseˢ q x
diff⊏ (here α x) (Del .α q) | source-∈ {i = i} p = source-⊏ {i₂ = i} (here (Del α) p)
diff⊏ (here α x) (Upd .α y q) with noEraseˢ q x
diff⊏ (here α x) (Upd .α y q) | source-∈ {i = i} p = source-⊏ {i₂ = i} (here (Upd α y) p)
diff⊏ (here α x) (Cpy .α q) with noEraseˢ q x
diff⊏ (here α x) (Cpy .α q) | source-∈ {i = i} p = source-⊏ {i₂ = i} (here (Cpy α) p)
diff⊏ (here α x) (Ins y q) with diff⊏ (here α x) q
diff⊏ (here ._ x) (Ins y q) | source-⊏ {i₁ = i₁} {i₂ = i₂} p = source-⊏ {i₁ = i₁} {i₂ = i₂} (there (Ins y) p)
diff⊏ (there p) (Del z q) with diff⊏ p q
diff⊏ (there p) (Del z q) | source-⊏ {i₁ = i₁} {i₂ = i₂} x = source-⊏ {i₁ = i₁} {i₂ = i₂} (there (Del z) x)
diff⊏ (there p) (Upd z y q) with diff⊏ p q
diff⊏ (there p) (Upd z y q) | source-⊏ {i₁ = i₁} {i₂ = i₂} x = source-⊏ {i₁ = i₁} {i₂ = i₂} (there (Upd z y) x)
diff⊏ (there p) (Cpy z q) with diff⊏ p q
diff⊏ (there p) (Cpy z q) | source-⊏ {i₁ = i₁} {i₂ = i₂} x = source-⊏ {i₁ = i₁} {i₂ = i₂} (there (Cpy z) x)
diff⊏ (there p) (Ins y q) with diff⊏ (there p) q
diff⊏ (there p) (Ins y q) | source-⊏ {i₁ = i₁} {i₂ = i₂} x = source-⊏ {i₁ = i₁} {i₂ = i₂} (there (Ins y) x)

-- Output  ⊏ 
-- diff⊏ₒ : ∀ {xs ys as bs a b} {α : View as a} {β : View bs b} {x : DList xs} {y : DList ys} {e : ES xs ys} 
--         -> x ⊢ α ⊏ β -> Diff x y e -> e ⊢ₒ α ⊏ β
-- diff⊏ₒ = ?

open import Level
open import Function


-- Final lemma
preserve⊏ : ∀ {xs ys zs ws as bs a b} {t₀ : DList xs} {t₁ : DList ys} {t₂ : DList zs} {e₀₁ : ES xs ys} {e₀₂ : ES xs zs} 
              {α : View as a} {β : View bs b}
              -> Diff t₀ t₁ e₀₁ -> Diff t₀ t₂ e₀₂ -> (p : e₀₁ ~ e₀₂) ->
              let e₃ = diff3 e₀₁ e₀₂ p in (q : e₃ ↓ ws) ->
              let e₀₁₂ = toES p q in t₀ ⊢ α ⊏ β -> (⟦ e₀₁₂ ⟧ ⊢ α ⊏ β) -- ⊎ (Del α ∈ₑ e₀₁₂) ⊎ (Del β ∈ₑ e₀₁₂)
preserve⊏ c d p q r = {!!}

-- preserve⊏ (Del x c) (Del .x d) (DelDel .x p) (Del .x q) (here .x y) = inj₂ (here (Del x))
-- preserve⊏ c d (UpdUpd x y z p) q (here α x₁) = {!!}
-- preserve⊏ c d (CpyCpy x p) q (here α x₁) = {!!}
-- preserve⊏ c d (CpyDel x p) q (here α x₁) = {!!}
-- preserve⊏ c d (DelCpy x p) q (here α x₁) = {!!}
-- preserve⊏ c d (CpyUpd x y p) q (here α x₁) = {!!}
-- preserve⊏ c d (UpdCpy x y p) q (here α x₁) = {!!}
-- preserve⊏ c d (DelUpd x y p) q (here α x₁) = {!!}
-- preserve⊏ c d (UpdDel x y p) q (here α x₁) = {!!}
-- preserve⊏ c d (InsIns x y p) q (here α x₁) = {!!}
-- preserve⊏ c d (Ins₁ x p) q (here α x₁) = {!!}
-- preserve⊏ c d (Ins₂ x p) q (here α x₁) = {!!}
-- preserve⊏ c d p q (there r) = {!!}

-- preserve⊏ End End End End ()
-- preserve⊏ (Del α c) (Del .α d) (DelDel .α p) (Del .α q) (here .α x) = inj₂ (here (Del α))
-- preserve⊏ (Del x c) (Del .x d) (DelDel .x p) (Del .x q) (there r) = map₃ id (there (Del x)) (there (Del x)) (preserve⊏ c d p q r)
-- preserve⊏ (Upd α y c) (Upd .α z d) (UpdUpd .α .y .z p) q (here .α x) with y =?= z
-- preserve⊏ (Upd α y c) (Upd .α .y d) (UpdUpd .α .y .y p) (Upd .α .y q) (here .α x) | yes refl = {!!}
-- preserve⊏ (Upd α y c) (Upd .α z d) (UpdUpd .α .y .z p) q (here .α x) | no ¬p = {!!}
-- preserve⊏ (Upd x y c) (Upd .x z d) (UpdUpd .x .y .z p) q (there r) = {!!}
-- preserve⊏ c d (CpyCpy x p) q r = {!!}
-- preserve⊏ c d (CpyDel x p) q r = {!!}
-- preserve⊏ c d (DelCpy x p) q r = {!!}
-- preserve⊏ c d (CpyUpd x y p) q r = {!!}
-- preserve⊏ c d (UpdCpy x y p) q r = {!!}
-- preserve⊏ c d (DelUpd x y p) q r = {!!}
-- preserve⊏ c d (UpdDel x y p) q r = {!!}
-- preserve⊏ c d (InsIns x y p) q r = {!!}
-- preserve⊏ c d (Ins₁ x p) q r = {!!}
-- preserve⊏ c d (Ins₂ x p) q r = {!!}

-- -- I define my own some-type to avoid clutter
-- data _⊎_⊎_ {a b c} (A : Set a) (B : Set b) (C : Set c) : Set (a ⊔ b ⊔ c) where
--   inj₁ : (x : A) → A ⊎ B ⊎ C 
--   inj₂ : (y : B) → A ⊎ B ⊎ C
--   inj₃ : (z : C) → A ⊎ B ⊎ C
  
-- map₃ : ∀ {a b c d e f} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e} {F : Set f} →
--       (A → D) → (B → E) → (C → F) → (A ⊎ B ⊎ C → D ⊎ E ⊎ F)
-- map₃ f g h (inj₁ x) = inj₁ (f x)
-- map₃ f g h (inj₂ y) = inj₂ (g y)
-- map₃ f g h (inj₃ z) = inj₃ (h z)
