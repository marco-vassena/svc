-- In this module the conditions for the presence of conflcits are analyzed.

module Diff3.Conflict where

open import Diff3.Core
open import EditScript.Mapping

open import Data.List
open import Relation.Nullary

data _∈ᶜ_ : Conflict -> ES₃ -> Set where
  Cnf : ∀ {e} -> (c : Conflict) -> c ∈ᶜ (Cnf c e) 
  Ins : ∀ {as a c e} (α : View as a) -> c ∈ᶜ e -> c ∈ᶜ (Ins α e)
  Del : ∀ {as a c e} (α : View as a) -> c ∈ᶜ e -> c ∈ᶜ (Del α e)
  Upd : ∀ {as bs a c e} (α : View as a) (β : View bs a) -> c ∈ᶜ e -> c ∈ᶜ (Upd α β e)


--------------------------------------------------------------------------------

import Data.Empty
open import Data.Unit

¬Insᵐ : Mapping -> Set
¬Insᵐ [] = ⊤
¬Insᵐ (Ins α ∷ m) = Data.Empty.⊥
¬Insᵐ (Del α ∷ m) = ⊤
¬Insᵐ (Cpy α ∷ m) = ⊤
¬Insᵐ (Upd α β ∷ m) = ⊤
¬Insᵐ (End ∷ m) = ⊤

¬Ins=>¬Insᵐ : ∀ {xs ys} (e : ES xs ys) -> ¬Ins e -> ¬Insᵐ (mapping e)
¬Ins=>¬Insᵐ (Ins x e) p = p
¬Ins=>¬Insᵐ (Del x e) p = tt
¬Ins=>¬Insᵐ (Cpy x e) p = tt
¬Ins=>¬Insᵐ (Upd x y e) p = tt
¬Ins=>¬Insᵐ End p = tt

data _~ᵐ_ : Mapping -> Mapping -> Set where
  cons : ∀ {xs ys a b c} (x : a ~> b) (y : a ~> c) -> xs ~ᵐ ys -> (x ∷ xs) ~ᵐ (y ∷ ys)
  ins₁ : ∀ {xs ys b} {{i : ¬Insᵐ ys}} (x : ⊥ ~> b) -> xs ~ᵐ ys -> x ∷ xs ~ᵐ ys
  ins₂ : ∀ {xs ys c} {{i : ¬Insᵐ xs}} (y : ⊥ ~> c) -> xs ~ᵐ ys -> xs ~ᵐ y ∷ ys
  nil : [] ~ᵐ []

infixl 3 _~ᵐ_

-- The proof that two aligned mappings xs ys map the same node to some value.
data _⊢ᵐ_~>[_,_] : ∀ {xs ys} -> xs ~ᵐ ys -> Val -> Val -> Val -> Set where
  here : ∀ {xs ys a b c} {p : xs ~ᵐ ys} (x : a ~> b) (y : a ~> c) -> cons x y p ⊢ᵐ a ~>[ b , c ]
  cons : ∀ {xs ys a b c v w z} {p : xs ~ᵐ ys} (x : a ~> b) (y : a ~> c) -> p ⊢ᵐ a ~>[ b , c ] -> cons x y p ⊢ᵐ v ~>[ w , z ] 
  ins₁ : ∀ {xs ys a b c d} {p : xs ~ᵐ ys} {i : ¬Insᵐ ys} (x : ⊥ ~> d) -> p ⊢ᵐ a ~>[ b , c ] -> ins₁ x p ⊢ᵐ a ~>[ b , c ]
  ins₂ : ∀ {xs ys a b c d} {p : xs ~ᵐ ys} {i : ¬Insᵐ xs} (y : ⊥ ~> d) -> p ⊢ᵐ a ~>[ b , c ] -> ins₂ y p ⊢ᵐ a ~>[ b , c ]

infixr 2 _⊢ᵐ_~>[_,_]

--------------------------------------------------------------------------------
-- Equivalence between ~ and ~ᵐ

aligned=>~ᵐ : ∀ {xs ys zs} {e₁ : ES xs ys} {e₂ : ES xs zs} -> e₁ ~ e₂ -> mapping e₁ ~ᵐ mapping e₂
aligned=>~ᵐ End = nil
aligned=>~ᵐ (DelDel x p) = cons (Del x) (Del x) (aligned=>~ᵐ p)
aligned=>~ᵐ (UpdUpd x y z p) = cons (Upd x y) (Upd x z) (aligned=>~ᵐ p)
aligned=>~ᵐ (CpyCpy x p) = cons (Cpy x) (Cpy x) (aligned=>~ᵐ p)
aligned=>~ᵐ (CpyDel x p) = cons (Cpy x) (Del x) (aligned=>~ᵐ p)
aligned=>~ᵐ (DelCpy x p) = cons (Del x) (Cpy x) (aligned=>~ᵐ p)
aligned=>~ᵐ (CpyUpd x y p) = cons (Cpy x) (Upd x y) (aligned=>~ᵐ p)
aligned=>~ᵐ (UpdCpy x y p) = cons (Upd x y) (Cpy x) (aligned=>~ᵐ p)
aligned=>~ᵐ (DelUpd x y p) = cons (Del x) (Upd x y) (aligned=>~ᵐ p)
aligned=>~ᵐ (UpdDel x y p) = cons (Upd x y) (Del x) (aligned=>~ᵐ p)
aligned=>~ᵐ (InsIns x y p) = cons (Ins x) (Ins y) (aligned=>~ᵐ p)
aligned=>~ᵐ (Ins₁ {e₂ = e₂} {{i = i}} x p) = ins₁ {{i = ¬Ins=>¬Insᵐ e₂ i}} (Ins x) (aligned=>~ᵐ p)
aligned=>~ᵐ (Ins₂ {e₁ = e₁} {{i = i}} x p) = ins₂ {{i = ¬Ins=>¬Insᵐ e₁ i}} (Ins x) (aligned=>~ᵐ p)

~ᵐ=>aligned : ∀ {xs ys zs} {e₁ : ES xs ys} {e₂ : ES xs zs} -> mapping e₁ ~ᵐ mapping e₂ -> e₁ ~ e₂
~ᵐ=>aligned {e₁ = Ins x e₁} {Ins y e₂} (cons .(Ins x) .(Ins y) p) = InsIns x y (~ᵐ=>aligned p)
~ᵐ=>aligned {e₁ = Ins x e₁} {Ins y e₂} (ins₁ {{i = ()}} .(Ins x) p)
~ᵐ=>aligned {e₁ = Ins x e₁} {Ins y e₂} (ins₂ {{i = ()}} .(Ins y) p)
~ᵐ=>aligned {e₁ = Ins x e₁} {Del y e₂} (ins₁ .(Ins x) p) = Ins₁ {{i = tt}} x (~ᵐ=>aligned p)
~ᵐ=>aligned {e₁ = Ins x e₁} {Cpy y e₂} (ins₁ .(Ins x) p) = Ins₁ {{i = tt}} x (~ᵐ=>aligned p)
~ᵐ=>aligned {e₁ = Ins x e₁} {Upd y z e₂} (ins₁ .(Ins x) p) = Ins₁ {{i = tt}} x (~ᵐ=>aligned p)
~ᵐ=>aligned {e₁ = Ins x e₁} {End} (ins₁ .(Ins x) p) = Ins₁ {{i = tt}} x (~ᵐ=>aligned p)
~ᵐ=>aligned {e₁ = Del x e₁} {Ins y e₂} (ins₂ .(Ins y) p) = Ins₂ {{i = tt}} y (~ᵐ=>aligned p)
~ᵐ=>aligned {e₁ = Del x e₁} {Del .x e₂} (cons .(Del x) .(Del x) p) = DelDel x (~ᵐ=>aligned p)
~ᵐ=>aligned {e₁ = Del x e₁} {Cpy .x e₂} (cons .(Del x) .(Cpy x) p) = DelCpy x (~ᵐ=>aligned p)
~ᵐ=>aligned {e₁ = Del x e₁} {Upd .x y e₂} (cons .(Del x) .(Upd x y) p) = DelUpd x y (~ᵐ=>aligned p)
~ᵐ=>aligned {e₁ = Cpy x e₁} {Ins y e₂} (ins₂ .(Ins y) p) = Ins₂ {{i = tt}} y (~ᵐ=>aligned p)
~ᵐ=>aligned {e₁ = Cpy x e₁} {Del .x e₂} (cons .(Cpy x) .(Del x) p) = CpyDel x (~ᵐ=>aligned p)
~ᵐ=>aligned {e₁ = Cpy x e₁} {Cpy .x e₂} (cons .(Cpy x) .(Cpy x) p) = CpyCpy x (~ᵐ=>aligned p)
~ᵐ=>aligned {e₁ = Cpy x e₁} {Upd .x z e₂} (cons .(Cpy x) .(Upd x z) p) = CpyUpd x z (~ᵐ=>aligned p)
~ᵐ=>aligned {e₁ = Upd x y e₁} {Ins z e₂} (ins₂ .(Ins z) p) = Ins₂ {{i = tt}} z (~ᵐ=>aligned p)
~ᵐ=>aligned {e₁ = Upd x y e₁} {Del .x e₂} (cons .(Upd x y) .(Del x) p) = UpdDel x y (~ᵐ=>aligned p)
~ᵐ=>aligned {e₁ = Upd x y e₁} {Cpy .x e₂} (cons .(Upd x y) .(Cpy x) p) = UpdCpy x y (~ᵐ=>aligned p)
~ᵐ=>aligned {e₁ = Upd x y e₁} {Upd .x z e₂} (cons .(Upd x y) .(Upd x z) p) = UpdUpd x y z (~ᵐ=>aligned p)
~ᵐ=>aligned {e₁ = End} {Ins x e₂} (ins₂ .(Ins x) p) = Ins₂ {{i = tt}} x (~ᵐ=>aligned p)
~ᵐ=>aligned {e₁ = End} {End} nil = End

--------------------------------------------------------------------------------

-- The two mappings xs and ys produce the conflict c
data _↑_ {xs ys} (p : xs ~ᵐ ys) : Conflict -> Set₁ where
  InsIns : ∀ {as a bs b} (α : View as a) (β : View bs b) -> 
             p ⊢ᵐ ⊥ ~>[ ⟨ α ⟩ , ⟨ β ⟩ ] -> ¬(α ⋍ β) -> p ↑ InsIns α β
  UpdUpd : ∀ {as bs cs a} {α : View as a} (β : View bs a) (γ : View cs a) -> 
             p ⊢ᵐ ⟨ α ⟩ ~>[ ⟨ β ⟩ , ⟨ γ ⟩ ] -> ¬(β ⋍ γ) -> p ↑ UpdUpd β γ
  UpdDel : ∀ {as bs a} (α : View as a) (β : View bs a) ->
             p ⊢ᵐ ⟨ α ⟩ ~>[ ⟨ β ⟩ , ⊥ ] -> ¬(α ⋍ β) -> p ↑ UpdDel α β
  DelUpd : ∀ {as bs a} (α : View as a) (β : View bs a) -> 
             p ⊢ᵐ ⟨ α ⟩ ~>[ ⊥ ,  ⟨ β ⟩ ] -> ¬(α ⋍ β) -> p ↑ DelUpd α β

data _,_↑_ {xs ys zs} (e₁ : ES xs ys) (e₂ : ES xs zs) (c : Conflict) : Set₁ where
  Cnf : ∀ {p : e₁ ~ e₂} -> aligned=>~ᵐ p ↑ c -> e₁ , e₂ ↑ c

-- TODO move to Core/Algo
RawDiff₃~ : ∀ {xs ys zs e₃} {e₁ : ES xs ys} {e₂ : ES xs zs} -> RawDiff₃ e₁ e₂ e₃ -> e₁ ~ e₂
RawDiff₃~ EndEnd = End
RawDiff₃~ (InsIns α r) = InsIns α α (RawDiff₃~ r)
RawDiff₃~ (Ins₁ α r) = Ins₁ α (RawDiff₃~ r)
RawDiff₃~ (Ins₂ α r) = Ins₂ α (RawDiff₃~ r)
RawDiff₃~ (DelDel α r) = DelDel α (RawDiff₃~ r)
RawDiff₃~ (CpyCpy α r) = CpyCpy α (RawDiff₃~ r)
RawDiff₃~ (UpdUpd α β r) = UpdUpd α β β (RawDiff₃~ r)
RawDiff₃~ (CpyDel α r) = CpyDel α (RawDiff₃~ r)
RawDiff₃~ (DelCpy α r) = DelCpy α (RawDiff₃~ r)
RawDiff₃~ (CpyUpd α β r) = CpyUpd α β (RawDiff₃~ r)
RawDiff₃~ (UpdCpy α β r) = UpdCpy α β (RawDiff₃~ r)
RawDiff₃~ (DelUpdC α β r) = DelUpd α β (RawDiff₃~ r)
RawDiff₃~ (UpdDelC α β r) = UpdDel α β (RawDiff₃~ r)
RawDiff₃~ (InsInsC α β r) = InsIns α β (RawDiff₃~ r)
RawDiff₃~ (UpdUpdC α β γ r) = UpdUpd α β γ (RawDiff₃~ r)

-- Firstly I will consider only mappings, then I will connect this proofs with edit scripts.
conflict-nec : ∀ {xs ys zs e₃ c} {e₁ : ES xs ys} {e₂ : ES xs zs} -> 
                 RawDiff₃ e₁ e₂ e₃ -> c ∈ᶜ e₃ -> e₁ , e₂ ↑ c
conflict-nec {e₁ = e₁} {e₂ = e₂} r p = Cnf {p = RawDiff₃~ r} {!!}


--------------------------------------------------------------------------------

-- Necessary conditions for the presence of conflicts
-- Note that this cannot be the sufficient conditions due to the aliasing problem.
-- We could be more explicit and include as an index the specific conflict
-- data _↑_ {xs ys zs ws} (e₁ : ES xs ys) (e₂ : ES zs ws) : Set₁ where
--   InsIns : ∀ {as bs a b} {α : View as a} {β : View bs b} -> e₁ ⊢ₑ ⊥ ~> ⟨ α ⟩ -> e₂ ⊢ₑ ⊥ ~> ⟨ β ⟩ -> ¬ (α ⋍ β) -> e₁ ↑ e₂
--   DelUpd : ∀ {as bs a} {α : View as a} {β : View bs a} -> e₁ ⊢ₑ ⟨ α ⟩ ~> ⊥ -> e₂ ⊢ₑ ⟨ α ⟩ ~> ⟨ β ⟩ -> e₁ ↑ e₂
--   UpdDel : ∀ {as bs a} {α : View as a} {β : View bs a} -> e₁ ⊢ₑ ⟨ α ⟩ ~> ⟨ β ⟩ -> e₂ ⊢ₑ ⟨ α ⟩ ~> ⊥ -> e₁ ↑ e₂
--   UpdUpd : ∀ {as bs cs a} {α : View as a} {β : View bs a} {γ : View cs a} -> 
--              e₁ ⊢ₑ ⟨ α ⟩ ~> ⟨ β ⟩ -> e₂ ⊢ₑ ⟨ α ⟩ ~> ⟨ γ ⟩ -> ¬ (β ⋍ γ) -> e₁ ↑ e₂

-- infixr 3 _↑_

--   -- I could also merge all these in one single case
--   -- Cnf : ∀ {a b c} -> e₁ ⊢ₑ a ~> b -> e₂ ⊢ₑ a ~> c -> ¬ (b ≡ c) -> e₁ ↑ e₂

-- there₁↑ : ∀ {as bs cs ds xs ys zs ws} {e₁ : ES (as ++ xs) (bs ++ ys)} {e₂ : ES zs ws}
--            (c : Edit as bs cs ds) -> e₁ ↑ e₂ -> c ∻ e₁ ↑ e₂
-- there₁↑ c (InsIns f g p) = InsIns (there~> c f) g p
-- there₁↑ c (DelUpd f g) = DelUpd (there~> c f) g
-- there₁↑ c (UpdDel f g) = UpdDel (there~> c f) g
-- there₁↑ c (UpdUpd f g p) = UpdUpd (there~> c f) g p

-- there₂↑ : ∀ {as bs cs ds xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES (as ++ zs) (bs ++ ws)}
--            (c : Edit as bs cs ds) -> e₁ ↑ e₂ -> e₁ ↑ c ∻ e₂
-- there₂↑ c (InsIns f g p) = InsIns f (there~> c g) p
-- there₂↑ c (DelUpd f g) = DelUpd f (there~> c g)
-- there₂↑ c (UpdDel f g) = UpdDel f (there~> c g)
-- there₂↑ c (UpdUpd f g p) = UpdUpd f (there~> c g) p

-- there↑ : ∀ {as bs cs ds xs ys zs} {e₁ : ES (as ++ xs) (bs ++ ys)} {e₂ : ES (as ++ xs) (bs ++ zs)}
--            (c : Edit as bs cs ds) -> e₁ ↑ e₂ -> c ∻ e₁ ↑ c ∻ e₂
-- there↑ c e = there₁↑ c (there₂↑ c e)

-- conflict-nec : ∀ {xs ys zs c e₃} {e₁ : ES xs ys} {e₂ : ES xs zs} -> RawDiff₃ e₁ e₂ e₃ -> c ∈ᶜ e₃ -> e₁ ↑ e₂
-- conflict-nec (DelUpdC α β p) (Cnf .(DelUpd α β)) = DelUpd (Del α (here (Del α))) (Upd α β (here (Upd α β)))
-- conflict-nec (UpdDelC α β p) (Cnf .(UpdDel α β)) = UpdDel (Upd α β (here (Upd α β))) (Del α (here (Del α)))
-- conflict-nec (InsInsC α β {¬eq = ¬p} p) (Cnf .(InsIns α β)) = InsIns (Ins α (here (Ins α))) (Ins β (here (Ins β))) ¬p
-- conflict-nec (UpdUpdC α β γ {¬eq = ¬p} p) (Cnf .(UpdUpd β γ)) = UpdUpd (Upd α β (here (Upd α β))) (Upd α γ (here (Upd α γ))) ¬p
-- conflict-nec (InsIns α p) (Ins .α q) = there↑ (Ins α) (conflict-nec p q)
-- conflict-nec (Ins₁ α p) (Ins .α q) = there₁↑ (Ins α) (conflict-nec p q)
-- conflict-nec (Ins₂ α p) (Ins .α q) = there₂↑ (Ins α) (conflict-nec p q)
-- conflict-nec (DelDel α p) (Del .α q) = there↑ (Del α) (conflict-nec p q)
-- conflict-nec (CpyDel α p) (Del .α q) = there₁↑ (Cpy α) (there₂↑ (Del α) (conflict-nec p q))
-- conflict-nec (DelCpy α p) (Del .α q) = there₁↑ (Del α) (there₂↑ (Cpy α) (conflict-nec p q))
-- conflict-nec (UpdUpd α β p) (Upd .α .β q) = there↑ (Upd α β) (conflict-nec p q)
-- conflict-nec (CpyUpd α β p) (Upd .α .β q) = there₁↑ (Cpy α) (there₂↑ (Upd α β) (conflict-nec p q))
-- conflict-nec (UpdCpy α β p) (Upd .α .β q) = there₁↑ (Upd α β) (there₂↑ (Cpy α) (conflict-nec p q))

-- -- e₁ ↑ e₂ is not sufficient, because of the aliasing problem  
-- conflict-suc : ∀ {xs ys zs c e₃} {e₁ : ES xs ys} {e₂ : ES xs zs} -> RawDiff₃ e₁ e₂ e₃ -> e₁ ↑ e₂ -> c ∈ᶜ e₃
-- conflict-suc p (InsIns (Ins α x) (Ins β x₁) q) = {!!}
-- conflict-suc p (DelUpd x x₁) = {!!}
-- conflict-suc p (UpdDel x x₁) = {!!}
-- conflict-suc p (UpdUpd x x₁ x₂) = {!!}
