module Embedding where

open import DTree hiding ([_])
open import View
open import Diff
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])

-- ∈-dsplit : ∀ {as bs cs ds'} {{ys zs}} {ds : DList (ys ++ zs)} (d : Edit as bs cs ds') {{ p : output d }} ->  
--            let ds₁ , ds₂ = dsplit ds in ⌞ d ⌟ ∈ ds -> ⌞ d ⌟ ∈ ds₁ +++ ds₂
-- ∈-dsplit {ds = ds} _ q
--   rewrite dsplit-lemma ds = q

-- ∈ₑ-∈  : ∀ {as bs cs ds xs ys} {d : Edit as bs cs ds} {{ p : output d }} {e : ES xs ys} -> d ∈ₑ e -> ⌞ d ⌟ ∈ ⟦ e ⟧
-- ∈ₑ-∈ (here {e = e} (Ins x)) = ∈-here x 
-- ∈ₑ-∈ {{p = ()}} (here (Del x))
-- ∈ₑ-∈ (here {e = e} (Cpy x)) = ∈-here x
-- ∈ₑ-∈ (here {e = e} (Upd x y)) = ∈-here y
-- ∈ₑ-∈ {{p = ()}} (here End)
-- ∈ₑ-∈ {d = d} (there {e = e} (Ins x) q) = ∈-there (∈-dsplit d (∈ₑ-∈ q))
-- ∈ₑ-∈ (there (Del x) q) = ∈ₑ-∈ q
-- ∈ₑ-∈ {d = d} {{p = p}} (there {e = e} (Cpy x) q) = ∈-there (∈-dsplit d (∈ₑ-∈ q))
-- ∈ₑ-∈ {d = d} (there (Upd x x₁) q) = ∈-there (∈-dsplit d (∈ₑ-∈ q))
-- ∈ₑ-∈ (there End q) = ∈ₑ-∈ q

-- ⟦⟧-lemma : ∀ {{ys}} {{zs}} {as bs cs ds es fs gs hs xs} (c : Edit as bs cs ds) (d : Edit es fs gs hs) (e : ES xs (ys ++ zs))
--              {{p : output c}} {{q : output d}} -> ⟦ e ⟧ ⊢ ⌞ c ⌟ ⊏ ⌞ d ⌟ ->
--               let ds₁ , ds₂ = dsplit ⟦ e ⟧ in ds₁ +++ ds₂ ⊢ ⌞ c ⌟ ⊏ ⌞ d ⌟
-- ⟦⟧-lemma c d e q rewrite dsplit-lemma ⟦ e ⟧ = q

-- preserves-⊏ : ∀ {as bs cs ds es fs gs hs xs ys} {e : ES xs ys} {d : Edit es fs gs hs}
--               (c : Edit as bs cs ds) -> {{p : output c}} {{q : output d}} 
--               -> e ⊢ₑ c ⊏ d -> ⟦ e ⟧ ⊢ ⌞ c ⌟ ⊏ ⌞ d ⌟
-- preserves-⊏ {d = d} (Ins x) (here .(Ins x) p) = here x (∈-dsplit d (∈ₑ-∈ p))
-- preserves-⊏ (Del x) {{()}} (here .(Del x) p)
-- preserves-⊏ {d = d} (Cpy x) (here {e = e} .(Cpy x) p) = here x (∈-dsplit d (∈ₑ-∈ p))
-- preserves-⊏ {d = d} (Upd x y) (here .(Upd x y) p) = here y (∈-dsplit d (∈ₑ-∈ p))
-- preserves-⊏ End {{()}} (here .End x)
-- preserves-⊏ {d = d} c (there {e = e} (Ins x) p) = there (⟦⟧-lemma c d e (preserves-⊏ c p))
-- preserves-⊏ c (there (Del x) p) = preserves-⊏ c p
-- preserves-⊏ {d = d} c (there {e = e} (Cpy x) p) = there (⟦⟧-lemma c d e (preserves-⊏ c p))
-- preserves-⊏ {d = d} c (there {e = e} (Upd x y) p) = there (⟦⟧-lemma c d e (preserves-⊏ c p))
-- preserves-⊏ c (there End p) = preserves-⊏ c p

open import Relation.Nullary
open import Diff3

toES∈ₑ : ∀ {as bs cs ds xs ys zs ws} {d : Edit as bs cs ds} {{w : change d}} {e₁ : ES xs ys} {e₂ : ES xs zs} 
           -> d ∈ₑ e₁ -> (p : e₁ ~ e₂) ->
           let e₁₂ = diff3 e₁ e₂ p in (q : e₁₂ ↓ ws) -> d ∈ₑ toES p q
toES∈ₑ (here (Ins x)) (InsIns {a = a} {b = b} .x y p) q with eq? a b
toES∈ₑ (here (Ins x)) (InsIns .x y p) q | yes refl with x =?= y
toES∈ₑ (here (Ins x)) (InsIns .x .x p) (Ins .x q) | yes refl | yes refl = here (Ins x)
toES∈ₑ (here (Ins x)) (InsIns .x y p) () | yes refl | no ¬p
toES∈ₑ (here (Ins x)) (InsIns .x y p) () | no ¬p
toES∈ₑ (here (Ins x)) (Ins₁ .x p) (Ins .x q) = here (Ins x)
toES∈ₑ (here (Ins x)) (Ins₂ y p) (Ins .y q) = there (Ins y) (toES∈ₑ (here (Ins x)) p q)
toES∈ₑ (here (Del x)) (DelDel .x p) (Del .x q) = here (Del x)
toES∈ₑ (here (Del x)) (DelCpy .x p) (Del .x q) = here (Del x)
toES∈ₑ (here (Del x)) (DelUpd .x y p) ()
toES∈ₑ (here (Del x)) (Ins₂ y p) (Ins .y q) = there (Ins y) (toES∈ₑ (here (Del x)) p q)
toES∈ₑ {{w = ()}} (here (Cpy x)) p q
toES∈ₑ (here (Upd x y)) (UpdUpd .x .y z p) q with y =?= z
toES∈ₑ (here (Upd x y)) (UpdUpd .x .y .y p) (Upd .x .y q) | yes refl = here (Upd x y)
toES∈ₑ (here (Upd x y)) (UpdUpd .x .y z p) () | no ¬p
toES∈ₑ (here (Upd x y)) (UpdCpy .x .y p) (Upd .x .y q) = here (Upd x y)
toES∈ₑ (here (Upd x y)) (UpdDel .x .y p) ()
toES∈ₑ (here (Upd x y)) (Ins₂ z p) (Ins .z q) = there (Ins z) (toES∈ₑ (here (Upd x y)) p q)
toES∈ₑ {{w = ()}} (here End) p q
toES∈ₑ (there (Ins x) r) (InsIns {a = a} {b = b} .x y p) q with eq? a b
toES∈ₑ (there (Ins x) r) (InsIns .x y p) q | yes refl with x =?= y
toES∈ₑ (there (Ins x) r) (InsIns .x .x p) (Ins .x q) | yes refl | yes refl = there (Ins x) (toES∈ₑ r p q)
toES∈ₑ (there (Ins x) r) (InsIns .x y p) () | yes refl | no ¬p
toES∈ₑ (there (Ins x) r) (InsIns .x y p) () | no ¬p
toES∈ₑ (there (Ins x) r) (Ins₁ .x p) (Ins .x q) = there (Ins x) (toES∈ₑ r p q)
toES∈ₑ (there (Ins x) r) (Ins₂ y p) (Ins .y q) = there (Ins y) (toES∈ₑ (there (Ins x) r) p q)
toES∈ₑ (there (Del x) r) (DelDel .x p) (Del .x q) = there (Del x) (toES∈ₑ r p q)
toES∈ₑ (there (Del x) r) (DelCpy .x p) (Del .x q) = there (Del x) (toES∈ₑ r p q)
toES∈ₑ (there (Del x) r) (DelUpd .x y p) ()
toES∈ₑ (there (Del x) r) (Ins₂ y p) (Ins .y q) = there (Ins y) (toES∈ₑ (there (Del x) r) p q)
toES∈ₑ (there (Cpy x) r) (CpyCpy .x p) (Cpy .x q) = there (Cpy x) (toES∈ₑ r p q)
toES∈ₑ (there (Cpy x) r) (CpyDel .x p) (Del .x q) = there (Del x) (toES∈ₑ r p q)
toES∈ₑ (there (Cpy x) r) (CpyUpd .x y p) (Upd .x .y q) = there (Upd x y) (toES∈ₑ r p q)
toES∈ₑ (there (Cpy x) r) (Ins₂ y p) (Ins .y q) = there (Ins y ) (toES∈ₑ (there (Cpy x) r) p q)
toES∈ₑ (there (Upd x y) r) (UpdUpd .x .y z p) q with y =?= z
toES∈ₑ (there (Upd x y) r) (UpdUpd .x .y .y p) (Upd .x .y q) | yes refl = there (Upd x y) (toES∈ₑ r p q)
toES∈ₑ (there (Upd x y) r) (UpdUpd .x .y z p) () | no ¬p
toES∈ₑ (there (Upd x y) r) (UpdCpy .x .y p) (Upd .x .y q) = there (Upd x y) (toES∈ₑ r p q)
toES∈ₑ (there (Upd x y) r) (UpdDel .x .y p) ()
toES∈ₑ (there (Upd x y) r) (Ins₂ z p) (Ins .z q) = there (Ins z) (toES∈ₑ (there (Upd x y) r) p q)
toES∈ₑ (there End r) p q = toES∈ₑ r p q

-- diff3-⊏ : ∀ {as bs cs ds es fs gs hs xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs}
--               (c : Edit as bs cs ds) (d : Edit es fs gs hs) -> {{w : change c}} {{z : change d}} 
--               -> e₁ ⊢ₑ c ⊏ d -> (p : e₁ ~ e₂) ->
--               let e₁₂ = diff3 e₁ e₂ p in (q : e₁₂ ↓ ws) -> toES p q ⊢ₑ c ⊏ d
-- diff3-⊏ (Ins x) d (here .(Ins x) o) (InsIns {a = a} {b = b} .x y p) q with eq? a b
-- diff3-⊏ (Ins x) d (here .(Ins x) o) (InsIns .x y p) q | yes refl with x =?= y
-- diff3-⊏ (Ins x) d (here .(Ins x) o) (InsIns .x .x p) (Ins .x q) | yes refl | yes refl = here (Ins x) (toES∈ₑ o p q)
-- diff3-⊏ (Ins x) d (here .(Ins x) o) (InsIns .x y p) () | yes refl | no ¬p
-- diff3-⊏ (Ins x) d (here .(Ins x) o) (InsIns .x y p) () | no ¬p
-- diff3-⊏ (Ins x) d (here .(Ins x) o) (Ins₁ .x p) (Ins .x q) = here (Ins x) (toES∈ₑ o p q)
-- diff3-⊏ (Ins x) d (here .(Ins x) o) (Ins₂ y p) (Ins .y q) = there (Ins y) (diff3-⊏ (Ins x) d (here (Ins x) o) p q)
-- diff3-⊏ (Del x) d (here .(Del x) o) (DelDel .x p) (Del .x q) = here (Del x) (toES∈ₑ o p q)
-- diff3-⊏ (Del x) d (here .(Del x) o) (DelCpy .x p) (Del .x q) = here (Del x) (toES∈ₑ o p q)
-- diff3-⊏ (Del x) d (here .(Del x) o) (DelUpd .x y p) ()
-- diff3-⊏ (Del x) d (here .(Del x) o) (Ins₂ y p) (Ins .y q) = there (Ins y) (diff3-⊏ (Del x) d (here (Del x) o) p q)
-- diff3-⊏ (Cpy x) d (here .(Cpy x) o) (CpyCpy .x p) (Cpy .x q) = here (Cpy x) (toES∈ₑ o p q)
-- diff3-⊏ (Cpy x) d {{()}} (here .(Cpy x) o) (CpyDel .x p) q
-- diff3-⊏ (Cpy x) d {{()}} (here .(Cpy x) o) (CpyUpd .x y p) (Upd .x .y q)
-- diff3-⊏ (Cpy x) d (here .(Cpy x) o) (Ins₂ y p) (Ins .y q) = there (Ins y) (diff3-⊏ (Cpy x) d (here (Cpy x) o) p q)
-- diff3-⊏ (Upd x y) d (here .(Upd x y) o) (UpdUpd .x .y z p) q with y =?= z
-- diff3-⊏ (Upd x y) d (here .(Upd x y) o) (UpdUpd .x .y .y p) (Upd .x .y q) | yes refl = here (Upd x y) (toES∈ₑ o p q)
-- diff3-⊏ (Upd x y) d (here .(Upd x y) o) (UpdUpd .x .y z p) () | no ¬p
-- diff3-⊏ (Upd x y) d (here .(Upd x y) o) (UpdCpy .x .y p) (Upd .x .y q) = here (Upd x y) (toES∈ₑ o p q)
-- diff3-⊏ (Upd x y) d (here .(Upd x y) o) (UpdDel .x .y p) ()
-- diff3-⊏ (Upd x y) d (here .(Upd x y) o) (Ins₂ z p) (Ins .z q) = there (Ins z) (diff3-⊏ (Upd x y) d (here (Upd x y) o) p q)
-- diff3-⊏ End d {{()}} (here .End x) p q
-- diff3-⊏ c d (there (Ins x) r) (InsIns {a = a} {b = b} .x y p) q with eq? a b
-- diff3-⊏ c d (there (Ins x) r) (InsIns .x y p) q | yes refl with x =?= y
-- diff3-⊏ c d (there (Ins x) r) (InsIns .x .x p) (Ins .x q) | yes refl | yes refl = there (Ins x) (diff3-⊏ c d r p q)
-- diff3-⊏ c d (there (Ins x) r) (InsIns .x y p) () | yes refl | no ¬p
-- diff3-⊏ c d (there (Ins x) r) (InsIns .x y p) () | no ¬p
-- diff3-⊏ c d (there (Ins x) r) (Ins₁ .x p) (Ins .x q) = there (Ins x) (diff3-⊏ c d r p q)
-- diff3-⊏ c d (there (Ins x) r) (Ins₂ y p) (Ins .y q) = there (Ins y) (diff3-⊏ c d (there (Ins x) r) p q)
-- diff3-⊏ c d (there (Del x) r) (DelDel .x p) (Del .x q) = there (Del x) (diff3-⊏ c d r p q)
-- diff3-⊏ c d (there (Del x) r) (DelCpy .x p) (Del .x q) = there (Del x) (diff3-⊏ c d r p q)
-- diff3-⊏ c d (there (Del x) r) (DelUpd .x y p) ()
-- diff3-⊏ c d (there (Del x) r) (Ins₂ y p) (Ins .y q) = there (Ins y) (diff3-⊏ c d (there (Del x) r) p q)
-- diff3-⊏ c d (there (Cpy x) r) (CpyCpy .x p) (Cpy .x q) = there (Cpy x) (diff3-⊏ c d r p q)
-- diff3-⊏ c d (there (Cpy x) r) (CpyDel .x p) (Del .x q) = there (Del x) (diff3-⊏ c d r p q)
-- diff3-⊏ c d (there (Cpy x) r) (CpyUpd .x y p) (Upd .x .y q) = there (Upd x y) (diff3-⊏ c d r p q)
-- diff3-⊏ c d (there (Cpy x) r) (Ins₂ y p) (Ins .y q) = there (Ins y) (diff3-⊏ c d (there (Cpy x) r) p q)
-- diff3-⊏ c d (there (Upd x y) r) (UpdUpd .x .y z p) q with y =?= z
-- diff3-⊏ c d (there (Upd x y) r) (UpdUpd .x .y .y p) (Upd .x .y q) | yes refl = there (Upd x y) (diff3-⊏ c d r p q)
-- diff3-⊏ c d (there (Upd x y) r) (UpdUpd .x .y z p) () | no ¬p
-- diff3-⊏ c d (there (Upd x y) r) (UpdCpy .x .y p) (Upd .x .y q) = there (Upd x y) (diff3-⊏ c d r p q)
-- diff3-⊏ c d (there (Upd x y) r) (UpdDel .x .y p) ()
-- diff3-⊏ c d (there (Upd x y) r) (Ins₂ z p) (Ins .z q) = there (Ins z) (diff3-⊏ c d (there (Upd x y) r) p q)
-- diff3-⊏ c d (there End r) p q = diff3-⊏ c d r p q

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

diff3-⊏ : ∀ {as bs cs ds es fs gs hs xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs}
            (c : Edit as bs cs ds) (d : Edit es fs gs hs) -> {{w : change c}} {{z : change d}} 
              -> e₁ ⊢ₑ c ⊏ d -> (p : e₁ ~ e₂) ->
              let e₁₂ = diff3 e₁ e₂ p in (q : e₁₂ ↓ ws) -> toES p q ⊢ₑ c ⊏ d
diff3-⊏ = {!!}

open import Safety

data _⊢ˢ_⊏_ : ∀ {xs ys as bs a b} -> ES xs ys -> View as a -> View bs b -> Set₁ where
  source-⊏ : ∀ {as bs cs ds es fs gs hs xs ys} {e : ES xs ys}
           {c : Edit as bs cs ds} {d : Edit es fs gs hs} {i₁ : input c} {i₂ : input d} -> e ⊢ₑ c ⊏ d 
           -> e ⊢ˢ ⌜ c ⌝ ⊏ ⌜ d ⌝

diff⊏ : ∀ {xs ys as bs a b} {α : View as a} {β : View bs b} {x : DList xs} {y : DList ys} {e : ES xs ys} 
        -> x ⊢ α ⊏ β -> Diff x y e -> e ⊢ˢ α ⊏ β
diff⊏ (here α x) (Del .α q) with noErase q x
diff⊏ (here α x) (Del .α q) | source-∈ {i = i} p = source-⊏ {i₂ = i} (here (Del α) p)
diff⊏ (here α x) (Upd .α y q) with noErase q x
diff⊏ (here α x) (Upd .α y q) | source-∈ {i = i} p = source-⊏ {i₂ = i} (here (Upd α y) p)
diff⊏ (here α x) (Cpy .α q) with noErase q x
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

open import Level
open import Function


-- Final lemma
preserve⊏ : ∀ {xs ys zs ws as bs a b} {t₀ : DList xs} {t₁ : DList ys} {t₂ : DList zs} {e₀₁ : ES xs ys} {e₀₂ : ES xs zs} 
              {α : View as a} {β : View bs b}
              -> Diff t₀ t₁ e₀₁ -> Diff t₀ t₂ e₀₂ -> (p : e₀₁ ~ e₀₂) ->
              let e₃ = diff3 e₀₁ e₀₂ p in (q : e₃ ↓ ws) ->
              let e₀₁₂ = toES p q in t₀ ⊢ α ⊏ β -> (⟦ e₀₁₂ ⟧ ⊢ α ⊏ β) -- ⊎ (Del α ∈ₑ e₀₁₂) ⊎ (Del β ∈ₑ e₀₁₂)
preserve⊏ c d p q r with diff⊏ r c 
preserve⊏ c d p q r | source-⊏ {c = c'} {d = d'} x with diff3-⊏ {!c'!} {!d'!} {!x!} {!p!} {!q!}
... | y = {!!}

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
