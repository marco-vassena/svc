-- In this module the conditions for the presence of conflcits are analyzed.

module Diff3.Conflict where

open import Diff3.Core
open import EditScript.Mapping

open import Data.List
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

data _∈ᶜ_ : Conflict -> RawMapping -> Set₁ where
  here : ∀ {xs} (c : Conflict) -> c ∈ᶜ c ∷ᶜ xs
  there : ∀ {xs v w} {c : Conflict} (x : v ~> w) -> c ∈ᶜ xs -> c ∈ᶜ x ∷ xs
  thereᶜ : ∀ {xs c} (c' : Conflict) -> c ∈ᶜ xs -> c ∈ᶜ c' ∷ᶜ xs

infixr 3 _∈ᶜ_ 

--------------------------------------------------------------------------------

-- The proof that two aligned mappings xs ys map the same node to some value.
-- data _⋎_⊢_~>[_,_] : Mapping -> Mapping -> Val -> Val -> Val -> Set where
--   here : ∀ {xs ys a b c} (x : a ~> b) (y : a ~> c) -> (x ∷ xs) ⋎ (y ∷ ys) ⊢ a ~>[ b , c ]
--   cons : ∀ {xs ys a b c v w z} (x : v ~> w) (y : v ~> z) -> xs ⋎ ys ⊢ a ~>[ b , c ] -> (x ∷ xs) ⋎ (y ∷ ys) ⊢ a ~>[ b , c ] 
--   ins₁ : ∀ {xs ys a b c d} {{i : ¬Insᵐ ys}} (x : ⊥ ~> d) -> xs ⋎ ys ⊢ a ~>[ b , c ] -> (x ∷ xs) ⋎ ys ⊢ a ~>[ b , c ]
--   ins₂ : ∀ {xs ys a b c d} {{i : ¬Insᵐ xs}} (y : ⊥ ~> d) -> xs ⋎ ys ⊢ a ~>[ b , c ] -> xs ⋎ (y ∷ ys) ⊢ a ~>[ b , c ]

data _⊢_~>[_,_] : ∀ {xs ys} -> xs ~ᵐ ys -> Val -> Val -> Val -> Set where
  here : ∀ {xs ys a b c } {p : xs ~ᵐ ys} (x : a ~> b) (y : a ~> c) -> cons x y p ⊢ a ~>[ b , c ]
  cons : ∀ {xs ys a b c v w z} {p : xs ~ᵐ ys} (x : v ~> w) (y : v ~> z) -> p ⊢ a ~>[ b , c ] -> cons x y p ⊢ a ~>[ b , c ] 
  ins₁ : ∀ {xs ys a b c d} {p : xs ~ᵐ ys} {{i : ¬Insᵐ ys}} (x : ⊥ ~> d) -> p ⊢ a ~>[ b , c ] -> ins₁ x p ⊢ a ~>[ b , c ]
  ins₂ : ∀ {xs ys a b c d} {p : xs ~ᵐ ys} {{i : ¬Insᵐ xs}} (y : ⊥ ~> d) -> p ⊢ a ~>[ b , c ] -> ins₂ y p ⊢ a ~>[ b , c ]


infixr 2 _⊢_~>[_,_]

-- The two mappings xs and ys produce the conflict c
data _↑_ {xs ys : Mapping} (p : xs ~ᵐ ys) : Conflict -> Set₁ where
  InsIns : ∀ {as a bs b} (α : View as a) (β : View bs b) -> 
             (q : p  ⊢ ⊥ ~>[ ⟨ α ⟩ , ⟨ β ⟩ ]) (α≠β : ¬ (α ⋍ β)) -> p ↑ InsIns α β
  UpdUpd : ∀ {as bs cs a} {α : View as a} (β : View bs a) (γ : View cs a) -> 
             (q : p ⊢ ⟨ α ⟩ ~>[ ⟨ β ⟩ , ⟨ γ ⟩ ]) (α≠β : ¬(α ⋍ β)) (α≠γ : ¬ (α ⋍ γ)) (β≠γ : ¬(β ⋍ γ)) -> p ↑ UpdUpd β γ
  UpdDel : ∀ {as bs a} (α : View as a) (β : View bs a) ->
             (q : p ⊢ ⟨ α ⟩ ~>[ ⟨ β ⟩ , ⊥ ]) (α≠β : ¬(α ⋍ β)) -> p ↑ UpdDel α β
  DelUpd : ∀ {as bs a} (α : View as a) (β : View bs a) -> 
             (q : p ⊢ ⟨ α ⟩ ~>[ ⊥ ,  ⟨ β ⟩ ]) (α≠β : ¬(α ⋍ β)) -> p ↑ DelUpd α β

cons↑ : ∀ {xs ys v w z c} {p : xs ~ᵐ ys} {x : v ~> w} {y : v ~> z} -> p ↑ c -> cons x y p ↑ c
cons↑ (InsIns α β q α≠β) = InsIns α β (cons _ _ q) α≠β
cons↑ (UpdUpd β γ q α≠β α≠γ β≠γ) = UpdUpd β γ (cons _ _ q) α≠β α≠γ β≠γ
cons↑ (UpdDel α β q α≠β) = UpdDel α β (cons _ _ q) α≠β
cons↑ (DelUpd α β q α≠β) = DelUpd α β (cons _ _ q) α≠β

ins₁↑ : ∀ {xs ys w c} {p : xs ~ᵐ ys} {x : ⊥ ~> w} {{i : ¬Insᵐ ys}}  -> p ↑ c -> ins₁ x p ↑ c
ins₁↑ (InsIns α β q α≠β) = InsIns α β (ins₁ _ q) α≠β
ins₁↑ (UpdUpd β γ q α≠β α≠γ β≠γ) = UpdUpd β γ (ins₁ _ q) α≠β α≠γ β≠γ
ins₁↑ (UpdDel α β q α≠β) = UpdDel α β (ins₁ _ q) α≠β
ins₁↑ (DelUpd α β q α≠β) = DelUpd α β (ins₁ _ q) α≠β

ins₂↑ : ∀ {xs ys w c} {p : xs ~ᵐ ys}{y : ⊥ ~> w} {{i : ¬Insᵐ xs}}  -> p ↑ c -> ins₂ y p ↑ c
ins₂↑ (InsIns α β q α≠β) = InsIns α β (ins₂ _ q) α≠β
ins₂↑ (UpdUpd β γ q α≠β α≠γ β≠γ) = UpdUpd β γ (ins₂ _ q) α≠β α≠γ β≠γ
ins₂↑ (UpdDel α β q α≠β) = UpdDel α β (ins₂ _ q) α≠β
ins₂↑ (DelUpd α β q α≠β) = DelUpd α β (ins₂ _ q) α≠β

conflict-nec : ∀ {xs ys zs c} {p : xs ~ᵐ ys} -> c ∈ᶜ zs -> p ⇓ zs -> p ↑ c
conflict-nec (here .(InsIns α β)) (conflict (InsIns (Ins α) (Ins β) α≠β) r) = InsIns α β (here (Ins α) (Ins β)) α≠β
conflict-nec (here ._) (conflict (UpdUpd x y α≠β α≠γ β≠γ) r) = UpdUpd _ _ (here x y) α≠β α≠γ β≠γ
conflict-nec (here ._) (conflict (UpdDel x y α≠β) r) = UpdDel _ _ (here x y) α≠β
conflict-nec (here ._) (conflict (DelUpd x y α≠β) r) = DelUpd  _ _ (here x y) α≠β
conflict-nec (there x q) (merge m r) = cons↑ (conflict-nec q r)
conflict-nec (there x q) (ins₁ .x r) = ins₁↑ (conflict-nec q r)
conflict-nec (there x q) (ins₂ .x r) = ins₂↑ (conflict-nec q r)
conflict-nec (thereᶜ x q) (conflict u r) = cons↑ (conflict-nec q r)

open import Data.Empty using (⊥-elim)

conflict-suf : ∀ {xs ys zs c} {p : xs ~ᵐ ys} -> p ↑ c -> p ⇓ zs -> c ∈ᶜ zs
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
-- -- Equivalence between ~ and ~ᵐ

-- aligned=>~ᵐ : ∀ {xs ys zs} {e₁ : ES xs ys} {e₂ : ES xs zs} -> e₁ ~ e₂ -> mapping e₁ ~ᵐ mapping e₂
-- aligned=>~ᵐ End = nil
-- aligned=>~ᵐ (DelDel x p) = cons (Del x) (Del x) (aligned=>~ᵐ p)
-- aligned=>~ᵐ (UpdUpd x y z p) = cons (Upd x y) (Upd x z) (aligned=>~ᵐ p)
-- aligned=>~ᵐ (CpyCpy x p) = cons (Cpy x) (Cpy x) (aligned=>~ᵐ p)
-- aligned=>~ᵐ (CpyDel x p) = cons (Cpy x) (Del x) (aligned=>~ᵐ p)
-- aligned=>~ᵐ (DelCpy x p) = cons (Del x) (Cpy x) (aligned=>~ᵐ p)
-- aligned=>~ᵐ (CpyUpd x y p) = cons (Cpy x) (Upd x y) (aligned=>~ᵐ p)
-- aligned=>~ᵐ (UpdCpy x y p) = cons (Upd x y) (Cpy x) (aligned=>~ᵐ p)
-- aligned=>~ᵐ (DelUpd x y p) = cons (Del x) (Upd x y) (aligned=>~ᵐ p)
-- aligned=>~ᵐ (UpdDel x y p) = cons (Upd x y) (Del x) (aligned=>~ᵐ p)
-- aligned=>~ᵐ (InsIns x y p) = cons (Ins x) (Ins y) (aligned=>~ᵐ p)
-- aligned=>~ᵐ (Ins₁ {e₂ = e₂} {{i = i}} x p) = ins₁ {{i = ¬Ins=>¬Insᵐ e₂ i}} (Ins x) (aligned=>~ᵐ p)
-- aligned=>~ᵐ (Ins₂ {e₁ = e₁} {{i = i}} x p) = ins₂ {{i = ¬Ins=>¬Insᵐ e₁ i}} (Ins x) (aligned=>~ᵐ p)

-- ~ᵐ=>aligned : ∀ {xs ys zs} {e₁ : ES xs ys} {e₂ : ES xs zs} -> mapping e₁ ~ᵐ mapping e₂ -> e₁ ~ e₂
-- ~ᵐ=>aligned {e₁ = Ins x e₁} {Ins y e₂} (cons .(Ins x) .(Ins y) p) = InsIns x y (~ᵐ=>aligned p)
-- ~ᵐ=>aligned {e₁ = Ins x e₁} {Ins y e₂} (ins₁ {{i = ()}} .(Ins x) p)
-- ~ᵐ=>aligned {e₁ = Ins x e₁} {Ins y e₂} (ins₂ {{i = ()}} .(Ins y) p)
-- ~ᵐ=>aligned {e₁ = Ins x e₁} {Del y e₂} (ins₁ .(Ins x) p) = Ins₁ {{i = tt}} x (~ᵐ=>aligned p)
-- ~ᵐ=>aligned {e₁ = Ins x e₁} {Cpy y e₂} (ins₁ .(Ins x) p) = Ins₁ {{i = tt}} x (~ᵐ=>aligned p)
-- ~ᵐ=>aligned {e₁ = Ins x e₁} {Upd y z e₂} (ins₁ .(Ins x) p) = Ins₁ {{i = tt}} x (~ᵐ=>aligned p)
-- ~ᵐ=>aligned {e₁ = Ins x e₁} {End} (ins₁ .(Ins x) p) = Ins₁ {{i = tt}} x (~ᵐ=>aligned p)
-- ~ᵐ=>aligned {e₁ = Del x e₁} {Ins y e₂} (ins₂ .(Ins y) p) = Ins₂ {{i = tt}} y (~ᵐ=>aligned p)
-- ~ᵐ=>aligned {e₁ = Del x e₁} {Del .x e₂} (cons .(Del x) .(Del x) p) = DelDel x (~ᵐ=>aligned p)
-- ~ᵐ=>aligned {e₁ = Del x e₁} {Cpy .x e₂} (cons .(Del x) .(Cpy x) p) = DelCpy x (~ᵐ=>aligned p)
-- ~ᵐ=>aligned {e₁ = Del x e₁} {Upd .x y e₂} (cons .(Del x) .(Upd x y) p) = DelUpd x y (~ᵐ=>aligned p)
-- ~ᵐ=>aligned {e₁ = Cpy x e₁} {Ins y e₂} (ins₂ .(Ins y) p) = Ins₂ {{i = tt}} y (~ᵐ=>aligned p)
-- ~ᵐ=>aligned {e₁ = Cpy x e₁} {Del .x e₂} (cons .(Cpy x) .(Del x) p) = CpyDel x (~ᵐ=>aligned p)
-- ~ᵐ=>aligned {e₁ = Cpy x e₁} {Cpy .x e₂} (cons .(Cpy x) .(Cpy x) p) = CpyCpy x (~ᵐ=>aligned p)
-- ~ᵐ=>aligned {e₁ = Cpy x e₁} {Upd .x z e₂} (cons .(Cpy x) .(Upd x z) p) = CpyUpd x z (~ᵐ=>aligned p)
-- ~ᵐ=>aligned {e₁ = Upd x y e₁} {Ins z e₂} (ins₂ .(Ins z) p) = Ins₂ {{i = tt}} z (~ᵐ=>aligned p)
-- ~ᵐ=>aligned {e₁ = Upd x y e₁} {Del .x e₂} (cons .(Upd x y) .(Del x) p) = UpdDel x y (~ᵐ=>aligned p)
-- ~ᵐ=>aligned {e₁ = Upd x y e₁} {Cpy .x e₂} (cons .(Upd x y) .(Cpy x) p) = UpdCpy x y (~ᵐ=>aligned p)
-- ~ᵐ=>aligned {e₁ = Upd x y e₁} {Upd .x z e₂} (cons .(Upd x y) .(Upd x z) p) = UpdUpd x y z (~ᵐ=>aligned p)
-- ~ᵐ=>aligned {e₁ = End} {Ins x e₂} (ins₂ .(Ins x) p) = Ins₂ {{i = tt}} x (~ᵐ=>aligned p)
-- ~ᵐ=>aligned {e₁ = End} {End} nil = End

-- --------------------------------------------------------------------------------

-- data _,_↑_ {xs ys zs} (e₁ : ES xs ys) (e₂ : ES xs zs) (c : Conflict) : Set₁ where
--   Cnf : ∀ {p : e₁ ~ e₂} -> aligned=>~ᵐ p ↑ c -> e₁ , e₂ ↑ c

-- -- TODO move to Core/Algo
-- RawDiff₃~ : ∀ {xs ys zs e₃} {e₁ : ES xs ys} {e₂ : ES xs zs} -> RawDiff₃ e₁ e₂ e₃ -> e₁ ~ e₂
-- RawDiff₃~ EndEnd = End
-- RawDiff₃~ (InsIns α r) = InsIns α α (RawDiff₃~ r)
-- RawDiff₃~ (Ins₁ α r) = Ins₁ α (RawDiff₃~ r)
-- RawDiff₃~ (Ins₂ α r) = Ins₂ α (RawDiff₃~ r)
-- RawDiff₃~ (DelDel α r) = DelDel α (RawDiff₃~ r)
-- RawDiff₃~ (CpyCpy α r) = CpyCpy α (RawDiff₃~ r)
-- RawDiff₃~ (UpdUpd α β r) = UpdUpd α β β (RawDiff₃~ r)
-- RawDiff₃~ (CpyDel α r) = CpyDel α (RawDiff₃~ r)
-- RawDiff₃~ (DelCpy α r) = DelCpy α (RawDiff₃~ r)
-- RawDiff₃~ (CpyUpd α β r) = CpyUpd α β (RawDiff₃~ r)
-- RawDiff₃~ (UpdCpy α β r) = UpdCpy α β (RawDiff₃~ r)
-- RawDiff₃~ (DelUpdC α β r) = DelUpd α β (RawDiff₃~ r)
-- RawDiff₃~ (UpdDelC α β r) = UpdDel α β (RawDiff₃~ r)
-- RawDiff₃~ (InsInsC α β r) = InsIns α β (RawDiff₃~ r)
-- RawDiff₃~ (UpdUpdC α β γ r) = UpdUpd α β γ (RawDiff₃~ r)

-- -- Firstly I will consider only mappings, then I will connect this proofs with edit scripts.
-- conflict-nec : ∀ {xs ys zs e₃ c} {e₁ : ES xs ys} {e₂ : ES xs zs} -> 
--                  RawDiff₃ e₁ e₂ e₃ -> c ∈ᶜ e₃ -> e₁ , e₂ ↑ c
-- conflict-nec {e₁ = e₁} {e₂ = e₂} r p = Cnf {p = RawDiff₃~ r} {!!}


-- --------------------------------------------------------------------------------

-- -- Necessary conditions for the presence of conflicts
-- -- Note that this cannot be the sufficient conditions due to the aliasing problem.
-- -- We could be more explicit and include as an index the specific conflict
-- -- data _↑_ {xs ys zs ws} (e₁ : ES xs ys) (e₂ : ES zs ws) : Set₁ where
-- --   InsIns : ∀ {as bs a b} {α : View as a} {β : View bs b} -> e₁ ⊢ₑ ⊥ ~> ⟨ α ⟩ -> e₂ ⊢ₑ ⊥ ~> ⟨ β ⟩ -> ¬ (α ⋍ β) -> e₁ ↑ e₂
-- --   DelUpd : ∀ {as bs a} {α : View as a} {β : View bs a} -> e₁ ⊢ₑ ⟨ α ⟩ ~> ⊥ -> e₂ ⊢ₑ ⟨ α ⟩ ~> ⟨ β ⟩ -> e₁ ↑ e₂
-- --   UpdDel : ∀ {as bs a} {α : View as a} {β : View bs a} -> e₁ ⊢ₑ ⟨ α ⟩ ~> ⟨ β ⟩ -> e₂ ⊢ₑ ⟨ α ⟩ ~> ⊥ -> e₁ ↑ e₂
-- --   UpdUpd : ∀ {as bs cs a} {α : View as a} {β : View bs a} {γ : View cs a} -> 
-- --              e₁ ⊢ₑ ⟨ α ⟩ ~> ⟨ β ⟩ -> e₂ ⊢ₑ ⟨ α ⟩ ~> ⟨ γ ⟩ -> ¬ (β ⋍ γ) -> e₁ ↑ e₂

-- -- infixr 3 _↑_

-- --   -- I could also merge all these in one single case
-- --   -- Cnf : ∀ {a b c} -> e₁ ⊢ₑ a ~> b -> e₂ ⊢ₑ a ~> c -> ¬ (b ≡ c) -> e₁ ↑ e₂

-- -- conflict-nec : ∀ {xs ys zs c e₃} {e₁ : ES xs ys} {e₂ : ES xs zs} -> RawDiff₃ e₁ e₂ e₃ -> c ∈ᶜ e₃ -> e₁ ↑ e₂
-- -- conflict-nec (DelUpdC α β p) (Cnf .(DelUpd α β)) = DelUpd (Del α (here (Del α))) (Upd α β (here (Upd α β)))
-- -- conflict-nec (UpdDelC α β p) (Cnf .(UpdDel α β)) = UpdDel (Upd α β (here (Upd α β))) (Del α (here (Del α)))
-- -- conflict-nec (InsInsC α β {¬eq = ¬p} p) (Cnf .(InsIns α β)) = InsIns (Ins α (here (Ins α))) (Ins β (here (Ins β))) ¬p
-- -- conflict-nec (UpdUpdC α β γ {¬eq = ¬p} p) (Cnf .(UpdUpd β γ)) = UpdUpd (Upd α β (here (Upd α β))) (Upd α γ (here (Upd α γ))) ¬p
-- -- conflict-nec (InsIns α p) (Ins .α q) = there↑ (Ins α) (conflict-nec p q)
-- -- conflict-nec (Ins₁ α p) (Ins .α q) = there₁↑ (Ins α) (conflict-nec p q)
-- -- conflict-nec (Ins₂ α p) (Ins .α q) = there₂↑ (Ins α) (conflict-nec p q)
-- -- conflict-nec (DelDel α p) (Del .α q) = there↑ (Del α) (conflict-nec p q)
-- -- conflict-nec (CpyDel α p) (Del .α q) = there₁↑ (Cpy α) (there₂↑ (Del α) (conflict-nec p q))
-- -- conflict-nec (DelCpy α p) (Del .α q) = there₁↑ (Del α) (there₂↑ (Cpy α) (conflict-nec p q))
-- -- conflict-nec (UpdUpd α β p) (Upd .α .β q) = there↑ (Upd α β) (conflict-nec p q)
-- -- conflict-nec (CpyUpd α β p) (Upd .α .β q) = there₁↑ (Cpy α) (there₂↑ (Upd α β) (conflict-nec p q))
-- -- conflict-nec (UpdCpy α β p) (Upd .α .β q) = there₁↑ (Upd α β) (there₂↑ (Cpy α) (conflict-nec p q))

-- -- -- e₁ ↑ e₂ is not sufficient, because of the aliasing problem  
-- -- conflict-suc : ∀ {xs ys zs c e₃} {e₁ : ES xs ys} {e₂ : ES xs zs} -> RawDiff₃ e₁ e₂ e₃ -> e₁ ↑ e₂ -> c ∈ᶜ e₃
-- -- conflict-suc p (InsIns (Ins α x) (Ins β x₁) q) = {!!}
-- -- conflict-suc p (DelUpd x x₁) = {!!}
-- -- conflict-suc p (UpdDel x x₁) = {!!}
-- -- conflict-suc p (UpdUpd x x₁ x₂) = {!!}
