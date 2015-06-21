-- In this module the conditions for the presence of conflcits are analyzed.

module Diff3.Conflict where

open import Diff3.Core
open import EditScript.Mapping

open import Data.List
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

-- p ⊢ v ~>[ x , y ] is the proof that in two aligned scripts xs and ys, the same source value v
-- is mapped to x and y in xs and ys respectively
data _⊢_~>[_,_] : ∀ {xs ys} -> xs ⋎ ys -> Val -> Val -> Val -> Set where
  here : ∀ {xs ys a b c } {p : xs ⋎ ys} (x : a ~> b) (y : a ~> c) -> cons x y p ⊢ a ~>[ b , c ]
  cons : ∀ {xs ys a b c v w z} {p : xs ⋎ ys} (x : v ~> w) (y : v ~> z) -> p ⊢ a ~>[ b , c ] -> cons x y p ⊢ a ~>[ b , c ] 

infixr 2 _⊢_~>[_,_]

-- The two mappings xs and ys produce the conflict c
data _↥_ {xs ys : Mapping} (p : xs ⋎ ys) : Conflict -> Set₁ where
  InsIns : ∀ {as a bs b} (α : View as a) (β : View bs b) -> 
             (q : p  ⊢ ⊥ ~>[ ⟨ α ⟩ , ⟨ β ⟩ ]) (α≠β : ¬ (α ⋍ β)) -> p ↥ InsIns α β
  UpdUpd : ∀ {as bs cs a} {α : View as a} (β : View bs a) (γ : View cs a) -> 
             (q : p ⊢ ⟨ α ⟩ ~>[ ⟨ β ⟩ , ⟨ γ ⟩ ]) (α≠β : ¬(α ⋍ β)) (α≠γ : ¬ (α ⋍ γ)) (β≠γ : ¬(β ⋍ γ)) -> p ↥ UpdUpd β γ
  UpdDel : ∀ {as bs a} (α : View as a) (β : View bs a) ->
             (q : p ⊢ ⟨ α ⟩ ~>[ ⟨ β ⟩ , ⊥ ]) (α≠β : ¬(α ⋍ β)) -> p ↥ UpdDel α β
  DelUpd : ∀ {as bs a} (α : View as a) (β : View bs a) -> 
             (q : p ⊢ ⟨ α ⟩ ~>[ ⊥ ,  ⟨ β ⟩ ]) (α≠β : ¬(α ⋍ β)) -> p ↥ DelUpd α β

cons↥ : ∀ {xs ys v w z c} {p : xs ⋎ ys} {x : v ~> w} {y : v ~> z} -> p ↥ c -> cons x y p ↥ c
cons↥ (InsIns α β q α≠β) = InsIns α β (cons _ _ q) α≠β
cons↥ (UpdUpd β γ q α≠β α≠γ β≠γ) = UpdUpd β γ (cons _ _ q) α≠β α≠γ β≠γ
cons↥ (UpdDel α β q α≠β) = UpdDel α β (cons _ _ q) α≠β
cons↥ (DelUpd α β q α≠β) = DelUpd α β (cons _ _ q) α≠β

-- ins₁↥ : ∀ {xs ys w c} {p : xs ⋎ ys} {x : ⊥ ~> w} {{i : ¬Insᵐ ys}}  -> p ↥ c -> ins₁ x p ↥ c
-- ins₁↥ (InsIns α β q α≠β) = InsIns α β (ins₁ _ q) α≠β
-- ins₁↥ (UpdUpd β γ q α≠β α≠γ β≠γ) = UpdUpd β γ (ins₁ _ q) α≠β α≠γ β≠γ
-- ins₁↥ (UpdDel α β q α≠β) = UpdDel α β (ins₁ _ q) α≠β
-- ins₁↥ (DelUpd α β q α≠β) = DelUpd α β (ins₁ _ q) α≠β

-- ins₂↥ : ∀ {xs ys w c} {p : xs ⋎ ys}{y : ⊥ ~> w} {{i : ¬Insᵐ xs}}  -> p ↥ c -> ins₂ y p ↥ c
-- ins₂↥ (InsIns α β q α≠β) = InsIns α β (ins₂ _ q) α≠β
-- ins₂↥ (UpdUpd β γ q α≠β α≠γ β≠γ) = UpdUpd β γ (ins₂ _ q) α≠β α≠γ β≠γ
-- ins₂↥ (UpdDel α β q α≠β) = UpdDel α β (ins₂ _ q) α≠β
-- ins₂↥ (DelUpd α β q α≠β) = DelUpd α β (ins₂ _ q) α≠β

conflict-nec : ∀ {xs ys zs c} {p : xs ⋎ ys} -> c ∈ᶜ zs -> p ⇓ zs -> p ↥ c
conflict-nec (here .(InsIns α β)) (conflict (InsIns (Ins α) (Ins β) α≠β) r) = InsIns α β (here (Ins α) (Ins β)) α≠β
conflict-nec (here ._) (conflict (UpdUpd x y α≠β α≠γ β≠γ) r) = UpdUpd _ _ (here x y) α≠β α≠γ β≠γ
conflict-nec (here ._) (conflict (UpdDel x y α≠β) r) = UpdDel _ _ (here x y) α≠β
conflict-nec (here ._) (conflict (DelUpd x y α≠β) r) = DelUpd  _ _ (here x y) α≠β
conflict-nec (there x q) (merge m r) = cons↥ (conflict-nec q r)
conflict-nec (thereᶜ x q) (conflict u r) = cons↥ (conflict-nec q r)

open import Data.Empty using (⊥-elim)

conflict-suf : ∀ {xs ys zs c} {p : xs ⋎ ys} -> p ↥ c -> p ⇓ zs -> c ∈ᶜ zs
conflict-suf (InsIns α .α (here (Ins .α) (Ins .α)) α≠β) (merge (Idem .(Ins α)) r) = ⊥-elim (α≠β refl)
conflict-suf (InsIns α β (here (Ins .α) (Ins .β)) α≠β) (conflict (InsIns .(Ins α) .(Ins β) α≠β₁) r) = here (InsIns α β)
conflict-suf (InsIns α β (cons x y q) α≠β) (merge m r) = there _ (conflict-suf (InsIns α β q α≠β) r)
conflict-suf (InsIns α β (cons x y q) α≠β) (conflict u r) = thereᶜ _ (conflict-suf (InsIns α β q α≠β) r)

conflict-suf (UpdUpd α γ (here f y) α≠β α≠γ β≠γ) (merge (Id₁ .f .y _) r) = ⊥-elim (α≠β refl)
conflict-suf (UpdUpd β α (here f y) α≠β α≠γ β≠γ) (merge (Id₂ .f .y _) r) = ⊥-elim (α≠γ refl)
conflict-suf (UpdUpd β .β (here y .y) α≠β α≠γ β≠γ) (merge (Idem .y) r) = ⊥-elim (β≠γ refl)
conflict-suf (UpdUpd β γ (here x y) α≠β α≠γ β≠γ) (conflict (UpdUpd .x .y α≠β₁ α≠γ₁ β≠γ₁) r) = here (UpdUpd β γ)
conflict-suf (UpdUpd β γ (cons x y q) α≠β α≠γ β≠γ) (merge m r) = there _ (conflict-suf (UpdUpd β γ q α≠β α≠γ β≠γ) r)
conflict-suf (UpdUpd β γ (cons x y q) α≠β α≠γ β≠γ) (conflict u r) = thereᶜ _ (conflict-suf (UpdUpd β γ q α≠β α≠γ β≠γ) r)

conflict-suf (UpdDel α .α (here f y) α≠β) (merge (Id₁ .f .y _) r) = ⊥-elim (α≠β refl)
conflict-suf (UpdDel α β (here x y) α≠β) (conflict (UpdDel .x .y α≠β₁) r) = here (UpdDel α β)
conflict-suf (UpdDel α β (cons x y q) α≠β) (merge m r) = there _ (conflict-suf (UpdDel α β q α≠β) r)
conflict-suf (UpdDel α β (cons x y q) α≠β) (conflict u r) = thereᶜ _ (conflict-suf (UpdDel α β q α≠β) r)

conflict-suf (DelUpd α .α (here f y) α≠β) (merge (Id₂ .f .y _) r) = ⊥-elim (α≠β refl)
conflict-suf (DelUpd α β (here x y) α≠β) (conflict (DelUpd .x .y α≠β₁) r) = here (DelUpd α β)
conflict-suf (DelUpd α β (cons x y q) α≠β) (merge m r) = there _ (conflict-suf (DelUpd α β q α≠β) r)
conflict-suf (DelUpd α β (cons x y q) α≠β) (conflict u r) = thereᶜ _ (conflict-suf (DelUpd α β q α≠β) r)

--------------------------------------------------------------------------------
-- Equivalence between ~ and ⋎

open import Data.Unit

fromRawMapping : RawMapping -> ES₃
fromRawMapping [] = End
fromRawMapping (Ins α ∷ r) = Ins α (fromRawMapping r)
fromRawMapping (Del α ∷ r) = Del α (fromRawMapping r)
fromRawMapping (Upd α β ∷ r) = Upd α β (fromRawMapping r)
fromRawMapping (x ∷ᶜ r) = Cnf x (fromRawMapping r)

toRawMapping : ES₃ -> RawMapping
toRawMapping End = []
toRawMapping (Ins x e) = Ins x ∷ toRawMapping e
toRawMapping (Del x e) = Del x ∷ toRawMapping e
toRawMapping (Upd x y e) = Upd x y ∷ toRawMapping e
toRawMapping (Cnf x e) = x ∷ᶜ toRawMapping e

-- TODO conflict lemmas about edit scripts (proved showing connection with mapping)
-- I would like to avoid to define a RawDiff₃ e₁ e₂ e₃ data-type to match ⇓, but instead
-- I'd prove the connection between diff3 and ⨆.
