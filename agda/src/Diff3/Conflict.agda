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
  ins₁ : ∀ {xs ys a b c d} {p : xs ⋎ ys} {{i : ¬Insᵐ ys}} (x : ⊥ ~> d) -> p ⊢ a ~>[ b , c ] -> ins₁ x p ⊢ a ~>[ b , c ]
  ins₂ : ∀ {xs ys a b c d} {p : xs ⋎ ys} {{i : ¬Insᵐ xs}} (y : ⊥ ~> d) -> p ⊢ a ~>[ b , c ] -> ins₂ y p ⊢ a ~>[ b , c ]

infixr 2 _⊢_~>[_,_]

--------------------------------------------------------------------------------

-- The two mappings xs and ys produce the conflict c
data _↑_ {xs ys : Mapping} (p : xs ⋎ ys) : Conflict -> Set₁ where
  InsIns : ∀ {as a bs b} (α : View as a) (β : View bs b) -> 
             (q : p  ⊢ ⊥ ~>[ ⟨ α ⟩ , ⟨ β ⟩ ]) (α≠β : ¬ (α ⋍ β)) -> p ↑ InsIns α β
  UpdUpd : ∀ {as bs cs a} {α : View as a} (β : View bs a) (γ : View cs a) -> 
             (q : p ⊢ ⟨ α ⟩ ~>[ ⟨ β ⟩ , ⟨ γ ⟩ ]) (α≠β : ¬(α ⋍ β)) (α≠γ : ¬ (α ⋍ γ)) (β≠γ : ¬(β ⋍ γ)) -> p ↑ UpdUpd β γ
  UpdDel : ∀ {as bs a} (α : View as a) (β : View bs a) ->
             (q : p ⊢ ⟨ α ⟩ ~>[ ⟨ β ⟩ , ⊥ ]) (α≠β : ¬(α ⋍ β)) -> p ↑ UpdDel α β
  DelUpd : ∀ {as bs a} (α : View as a) (β : View bs a) -> 
             (q : p ⊢ ⟨ α ⟩ ~>[ ⊥ ,  ⟨ β ⟩ ]) (α≠β : ¬(α ⋍ β)) -> p ↑ DelUpd α β

cons↑ : ∀ {xs ys v w z c} {p : xs ⋎ ys} {x : v ~> w} {y : v ~> z} -> p ↑ c -> cons x y p ↑ c
cons↑ (InsIns α β q α≠β) = InsIns α β (cons _ _ q) α≠β
cons↑ (UpdUpd β γ q α≠β α≠γ β≠γ) = UpdUpd β γ (cons _ _ q) α≠β α≠γ β≠γ
cons↑ (UpdDel α β q α≠β) = UpdDel α β (cons _ _ q) α≠β
cons↑ (DelUpd α β q α≠β) = DelUpd α β (cons _ _ q) α≠β

ins₁↑ : ∀ {xs ys w c} {p : xs ⋎ ys} {x : ⊥ ~> w} {{i : ¬Insᵐ ys}}  -> p ↑ c -> ins₁ x p ↑ c
ins₁↑ (InsIns α β q α≠β) = InsIns α β (ins₁ _ q) α≠β
ins₁↑ (UpdUpd β γ q α≠β α≠γ β≠γ) = UpdUpd β γ (ins₁ _ q) α≠β α≠γ β≠γ
ins₁↑ (UpdDel α β q α≠β) = UpdDel α β (ins₁ _ q) α≠β
ins₁↑ (DelUpd α β q α≠β) = DelUpd α β (ins₁ _ q) α≠β

ins₂↑ : ∀ {xs ys w c} {p : xs ⋎ ys}{y : ⊥ ~> w} {{i : ¬Insᵐ xs}}  -> p ↑ c -> ins₂ y p ↑ c
ins₂↑ (InsIns α β q α≠β) = InsIns α β (ins₂ _ q) α≠β
ins₂↑ (UpdUpd β γ q α≠β α≠γ β≠γ) = UpdUpd β γ (ins₂ _ q) α≠β α≠γ β≠γ
ins₂↑ (UpdDel α β q α≠β) = UpdDel α β (ins₂ _ q) α≠β
ins₂↑ (DelUpd α β q α≠β) = DelUpd α β (ins₂ _ q) α≠β

conflict-nec : ∀ {xs ys zs c} {p : xs ⋎ ys} -> c ∈ᶜ zs -> p ⇓ zs -> p ↑ c
conflict-nec (here .(InsIns α β)) (conflict (InsIns (Ins α) (Ins β) α≠β) r) = InsIns α β (here (Ins α) (Ins β)) α≠β
conflict-nec (here ._) (conflict (UpdUpd x y α≠β α≠γ β≠γ) r) = UpdUpd _ _ (here x y) α≠β α≠γ β≠γ
conflict-nec (here ._) (conflict (UpdDel x y α≠β) r) = UpdDel _ _ (here x y) α≠β
conflict-nec (here ._) (conflict (DelUpd x y α≠β) r) = DelUpd  _ _ (here x y) α≠β
conflict-nec (there x q) (merge m r) = cons↑ (conflict-nec q r)
conflict-nec (there x q) (ins₁ .x r) = ins₁↑ (conflict-nec q r)
conflict-nec (there x q) (ins₂ .x r) = ins₂↑ (conflict-nec q r)
conflict-nec (thereᶜ x q) (conflict u r) = cons↑ (conflict-nec q r)

open import Data.Empty using (⊥-elim)

conflict-suf : ∀ {xs ys zs c} {p : xs ⋎ ys} -> p ↑ c -> p ⇓ zs -> c ∈ᶜ zs
conflict-suf (InsIns α .α (here (Ins .α) (Ins .α)) α≠β) (merge (Idem .(Ins α)) r) = ⊥-elim (α≠β refl)
conflict-suf (InsIns α β (here (Ins .α) (Ins .β)) α≠β) (conflict (InsIns .(Ins α) .(Ins β) α≠β₁) r) = here (InsIns α β)
conflict-suf (InsIns α β (cons x y q) α≠β) (merge m r) = there _ (conflict-suf (InsIns α β q α≠β) r)
conflict-suf (InsIns α β (cons x y q) α≠β) (conflict u r) = thereᶜ _ (conflict-suf (InsIns α β q α≠β) r)
conflict-suf (InsIns α β (ins₁ x q) α≠β) (ins₁ .x r) = there x (conflict-suf (InsIns α β q α≠β) r)
conflict-suf (InsIns α β (ins₂ y q) α≠β) (ins₂ .y r) = there y (conflict-suf (InsIns α β q α≠β) r)

conflict-suf (UpdUpd α γ (here f y) α≠β α≠γ β≠γ) (merge (Id₁ .f .y) r) = ⊥-elim (α≠β refl)
conflict-suf (UpdUpd β α (here f y) α≠β α≠γ β≠γ) (merge (Id₂ .f .y) r) = ⊥-elim (α≠γ refl)
conflict-suf (UpdUpd β .β (here y .y) α≠β α≠γ β≠γ) (merge (Idem .y) r) = ⊥-elim (β≠γ refl)
conflict-suf (UpdUpd β γ (here x y) α≠β α≠γ β≠γ) (conflict (UpdUpd .x .y α≠β₁ α≠γ₁ β≠γ₁) r) = here (UpdUpd β γ)
conflict-suf (UpdUpd β γ (cons x y q) α≠β α≠γ β≠γ) (merge m r) = there _ (conflict-suf (UpdUpd β γ q α≠β α≠γ β≠γ) r)
conflict-suf (UpdUpd β γ (cons x y q) α≠β α≠γ β≠γ) (conflict u r) = thereᶜ _ (conflict-suf (UpdUpd β γ q α≠β α≠γ β≠γ) r)
conflict-suf (UpdUpd β γ (ins₁ x q) α≠β α≠γ β≠γ) (ins₁ .x r) = there x (conflict-suf (UpdUpd β γ q α≠β α≠γ β≠γ) r)
conflict-suf (UpdUpd β γ (ins₂ y q) α≠β α≠γ β≠γ) (ins₂ .y r) = there y (conflict-suf (UpdUpd β γ q α≠β α≠γ β≠γ) r)

conflict-suf (UpdDel α .α (here f y) α≠β) (merge (Id₁ .f .y) r) = ⊥-elim (α≠β refl)
conflict-suf (UpdDel α β (here x y) α≠β) (conflict (UpdDel .x .y α≠β₁) r) = here (UpdDel α β)
conflict-suf (UpdDel α β (cons x y q) α≠β) (merge m r) = there _ (conflict-suf (UpdDel α β q α≠β) r)
conflict-suf (UpdDel α β (cons x y q) α≠β) (conflict u r) = thereᶜ _ (conflict-suf (UpdDel α β q α≠β) r)
conflict-suf (UpdDel α β (ins₁ x q) α≠β) (ins₁ .x r) = there x (conflict-suf (UpdDel α β q α≠β) r)
conflict-suf (UpdDel α β (ins₂ y q) α≠β) (ins₂ .y r) = there y (conflict-suf (UpdDel α β q α≠β) r)

conflict-suf (DelUpd α .α (here f y) α≠β) (merge (Id₂ .f .y) r) = ⊥-elim (α≠β refl)
conflict-suf (DelUpd α β (here x y) α≠β) (conflict (DelUpd .x .y α≠β₁) r) = here (DelUpd α β)
conflict-suf (DelUpd α β (cons x y q) α≠β) (merge m r) = there _ (conflict-suf (DelUpd α β q α≠β) r)
conflict-suf (DelUpd α β (cons x y q) α≠β) (conflict u r) = thereᶜ _ (conflict-suf (DelUpd α β q α≠β) r)
conflict-suf (DelUpd α β (ins₁ x q) α≠β) (ins₁ .x r) = there x (conflict-suf (DelUpd α β q α≠β) r)
conflict-suf (DelUpd α β (ins₂ y q) α≠β) (ins₂ .y r) = there y (conflict-suf (DelUpd α β q α≠β) r)

-- --------------------------------------------------------------------------------
-- -- Equivalence between ~ and ⋎

-- aligned=>⋎ : ∀ {xs ys zs} {e₁ : ES xs ys} {e₂ : ES xs zs} -> e₁ ~ e₂ -> mapping e₁ ⋎ mapping e₂
-- aligned=>⋎ End = nil
-- aligned=>⋎ (DelDel x p) = cons (Del x) (Del x) (aligned=>⋎ p)
-- aligned=>⋎ (UpdUpd x y z p) = cons (Upd x y) (Upd x z) (aligned=>⋎ p)
-- aligned=>⋎ (CpyCpy x p) = cons (Cpy x) (Cpy x) (aligned=>⋎ p)
-- aligned=>⋎ (CpyDel x p) = cons (Cpy x) (Del x) (aligned=>⋎ p)
-- aligned=>⋎ (DelCpy x p) = cons (Del x) (Cpy x) (aligned=>⋎ p)
-- aligned=>⋎ (CpyUpd x y p) = cons (Cpy x) (Upd x y) (aligned=>⋎ p)
-- aligned=>⋎ (UpdCpy x y p) = cons (Upd x y) (Cpy x) (aligned=>⋎ p)
-- aligned=>⋎ (DelUpd x y p) = cons (Del x) (Upd x y) (aligned=>⋎ p)
-- aligned=>⋎ (UpdDel x y p) = cons (Upd x y) (Del x) (aligned=>⋎ p)
-- aligned=>⋎ (InsIns x y p) = cons (Ins x) (Ins y) (aligned=>⋎ p)
-- aligned=>⋎ (Ins₁ {e₂ = e₂} {{i = i}} x p) = ins₁ {{i = ¬Ins=>¬Insᵐ e₂ i}} (Ins x) (aligned=>⋎ p)
-- aligned=>⋎ (Ins₂ {e₁ = e₁} {{i = i}} x p) = ins₂ {{i = ¬Ins=>¬Insᵐ e₁ i}} (Ins x) (aligned=>⋎ p)

-- ⋎=>aligned : ∀ {xs ys zs} {e₁ : ES xs ys} {e₂ : ES xs zs} -> mapping e₁ ⋎ mapping e₂ -> e₁ ~ e₂
-- ⋎=>aligned {e₁ = Ins x e₁} {Ins y e₂} (cons .(Ins x) .(Ins y) p) = InsIns x y (⋎=>aligned p)
-- ⋎=>aligned {e₁ = Ins x e₁} {Ins y e₂} (ins₁ {{i = ()}} .(Ins x) p)
-- ⋎=>aligned {e₁ = Ins x e₁} {Ins y e₂} (ins₂ {{i = ()}} .(Ins y) p)
-- ⋎=>aligned {e₁ = Ins x e₁} {Del y e₂} (ins₁ .(Ins x) p) = Ins₁ {{i = tt}} x (⋎=>aligned p)
-- ⋎=>aligned {e₁ = Ins x e₁} {Cpy y e₂} (ins₁ .(Ins x) p) = Ins₁ {{i = tt}} x (⋎=>aligned p)
-- ⋎=>aligned {e₁ = Ins x e₁} {Upd y z e₂} (ins₁ .(Ins x) p) = Ins₁ {{i = tt}} x (⋎=>aligned p)
-- ⋎=>aligned {e₁ = Ins x e₁} {End} (ins₁ .(Ins x) p) = Ins₁ {{i = tt}} x (⋎=>aligned p)
-- ⋎=>aligned {e₁ = Del x e₁} {Ins y e₂} (ins₂ .(Ins y) p) = Ins₂ {{i = tt}} y (⋎=>aligned p)
-- ⋎=>aligned {e₁ = Del x e₁} {Del .x e₂} (cons .(Del x) .(Del x) p) = DelDel x (⋎=>aligned p)
-- ⋎=>aligned {e₁ = Del x e₁} {Cpy .x e₂} (cons .(Del x) .(Cpy x) p) = DelCpy x (⋎=>aligned p)
-- ⋎=>aligned {e₁ = Del x e₁} {Upd .x y e₂} (cons .(Del x) .(Upd x y) p) = DelUpd x y (⋎=>aligned p)
-- ⋎=>aligned {e₁ = Cpy x e₁} {Ins y e₂} (ins₂ .(Ins y) p) = Ins₂ {{i = tt}} y (⋎=>aligned p)
-- ⋎=>aligned {e₁ = Cpy x e₁} {Del .x e₂} (cons .(Cpy x) .(Del x) p) = CpyDel x (⋎=>aligned p)
-- ⋎=>aligned {e₁ = Cpy x e₁} {Cpy .x e₂} (cons .(Cpy x) .(Cpy x) p) = CpyCpy x (⋎=>aligned p)
-- ⋎=>aligned {e₁ = Cpy x e₁} {Upd .x z e₂} (cons .(Cpy x) .(Upd x z) p) = CpyUpd x z (⋎=>aligned p)
-- ⋎=>aligned {e₁ = Upd x y e₁} {Ins z e₂} (ins₂ .(Ins z) p) = Ins₂ {{i = tt}} z (⋎=>aligned p)
-- ⋎=>aligned {e₁ = Upd x y e₁} {Del .x e₂} (cons .(Upd x y) .(Del x) p) = UpdDel x y (⋎=>aligned p)
-- ⋎=>aligned {e₁ = Upd x y e₁} {Cpy .x e₂} (cons .(Upd x y) .(Cpy x) p) = UpdCpy x y (⋎=>aligned p)
-- ⋎=>aligned {e₁ = Upd x y e₁} {Upd .x z e₂} (cons .(Upd x y) .(Upd x z) p) = UpdUpd x y z (⋎=>aligned p)
-- ⋎=>aligned {e₁ = End} {Ins x e₂} (ins₂ .(Ins x) p) = Ins₂ {{i = tt}} x (⋎=>aligned p)
-- ⋎=>aligned {e₁ = End} {End} nil = End
