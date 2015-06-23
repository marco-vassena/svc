-- In this module the conditions for the presence of conflcits are analyzed.

module Diff3.Conflict where

open import Diff3.Core
open import EditScript.Mapping

open import Data.List
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty using (⊥-elim)

-- TODO maybe move to Core ? 

-- p ⊢ v ~>[ x , y ] is the proof that in two aligned scripts xs and ys, the same source value v
-- is mapped to x and y in xs and ys respectively
data Map⋎ {as bs cs ds es fs} (u : Val as bs) (v : Val cs ds) (w : Val es fs) 
          : ∀ {xs ys zs} {e₁ : ES xs ys} {e₂ : ES xs zs} (p : e₁ ⋎ e₂) -> Set where
  here : ∀ {xs ys zs} {e₁ : ES (as ++ xs) (cs ++ ys)} {e₂ : ES (as ++ xs) (es ++ zs)} {p : e₁ ⋎ e₂} 
           (x : u ~> v) (y : u ~> w) -> Map⋎ u v w (cons x y p) 
  cons : ∀ {xs ys zs as' bs' cs' ds' es' fs'} {e₁ : ES (as' ++ xs) (cs' ++ ys)} {e₂ : ES (as' ++ xs) (es' ++ zs)} 
           {p : e₁ ⋎ e₂} {u' : Val as' bs'} {v' : Val cs' ds'} {w' : Val es' fs'} 
           (x : u' ~> v') (y : u' ~> w') -> Map⋎ u v w p -> Map⋎ u v w (cons x y p)

-- More readable syntax
-- Note that a syntax declaration would not work here, because it is not possible
-- to include instance arguments (e₁ ⋎ e₂) 
_,_⊢_~>[_,_] : ∀ {xs ys zs as bs cs ds es fs} (e₁ : ES xs ys) (e₂ : ES xs zs) {{p : e₁ ⋎ e₂}} -> 
                 (u : Val as bs) (v : Val cs ds) (w : Val es fs) -> Set
_,_⊢_~>[_,_] e₁ e₂ {{p}} u v w = Map⋎ u v w p

infixr 2 _,_⊢_~>[_,_]

-- The two mappings xs and ys produce the conflict c
data Failure {xs ys zs} {e₁ : ES xs ys} {e₂ : ES xs zs} (p : e₁ ⋎ e₂) 
           : ∀ {as bs cs ds es fs} {u : Val as bs} {v : Val cs ds} {w : Val es fs} -> Conflict u v w -> Set₁ where
  InsIns : ∀ {as a bs b} (α : View as a) (β : View bs b) -> 
             (q : e₁ , e₂ ⊢ ⊥ ~>[ ⟨ α ⟩ , ⟨ β ⟩ ]) (α≠β : ¬ (α ⋍ β)) -> Failure p (InsIns α β)
  UpdUpd : ∀ {as bs cs a} (α : View as a) (β : View bs a) (γ : View cs a) -> 
             (q : e₁ , e₂ ⊢ ⟨ α ⟩ ~>[ ⟨ β ⟩ , ⟨ γ ⟩ ]) ->
             (α≠β : ¬(α ⋍ β)) (α≠γ : ¬ (α ⋍ γ)) (β≠γ : ¬(β ⋍ γ)) -> Failure p (UpdUpd α β γ)
  UpdDel : ∀ {as bs a} (α : View as a) (β : View bs a) ->
             (q : e₁ , e₂  ⊢ ⟨ α ⟩ ~>[ ⟨ β ⟩ , ⊥ ]) (α≠β : ¬(α ⋍ β)) -> Failure p (UpdDel α β)
  DelUpd : ∀ {as bs a} (α : View as a) (β : View bs a) -> 
             (q : e₁ , e₂  ⊢ ⟨ α ⟩ ~>[ ⊥ ,  ⟨ β ⟩ ]) (α≠β : ¬(α ⋍ β)) -> Failure p (DelUpd α β)

_,_↥_ : ∀ {xs ys zs} {as bs cs ds es fs} {u : Val as bs} {v : Val cs ds} {w : Val es fs} 
          (e₁ : ES xs ys) (e₂ : ES xs zs) {{p : e₁ ⋎ e₂}} -> Conflict u v w -> Set₁
_,_↥_ e₁ e₂ {{p}} c = Failure p c 

infixl 2 _,_↥_

cons↥ : ∀ {xs ys zs as bs cs ds es fs as' bs' cs' ds' es' fs'} {u' : Val as' bs'} {v' : Val cs' ds'} {w' : Val es' fs'}
          {e₁ : ES (as ++ xs) (cs ++ ys)} {e₂ : ES (as ++ xs) (es ++ zs)} {p : e₁ ⋎ e₂} 
          {u : Val as bs} {v : Val cs ds} {w : Val es fs} {x : u ~> v} {y : u ~> w}
          {c : Conflict u' v' w'} -> e₁ , e₂ ↥ c -> Failure (cons x y p) c
cons↥ (InsIns α β q α≠β) = InsIns α β (cons _ _ q) α≠β
cons↥ (UpdUpd α β γ q α≠β α≠γ β≠γ) = UpdUpd α β γ (cons _ _ q) α≠β α≠γ β≠γ
cons↥ (UpdDel α β q α≠β) = UpdDel α β (cons _ _ q) α≠β
cons↥ (DelUpd α β q α≠β) = DelUpd α β (cons _ _ q) α≠β

conflict-nec : ∀ {xs ys zs as bs cs ds es fs} {e₁ : ES xs ys} {e₂ : ES xs zs} {p : e₁ ⋎ e₂} {e₃ : ES₃ xs}
                 {u : Val as bs} {v : Val cs ds} {w : Val es fs} {c : Conflict u v w} ->
                 c ∈ᶜ e₃ -> Diff₃ e₁ e₂ e₃ -> e₁ , e₂ ↥ c
conflict-nec (here (UpdUpd α β γ)) (conflict (UpdUpd f g α≠β α≠γ β≠γ) d) = UpdUpd α β γ (here f g) α≠β α≠γ β≠γ
conflict-nec (here (DelUpd α β)) (conflict (DelUpd f g α≠β) d) = DelUpd α β (here f g) α≠β
conflict-nec (here (UpdDel α β)) (conflict (UpdDel f g α≠β) d) = UpdDel α β (here f g) α≠β
conflict-nec (here (InsIns α β)) (conflict (InsIns f g α≠β) d) = InsIns α β (here f g) α≠β
conflict-nec (there x q) (merge m d) = cons↥ (conflict-nec q d)
conflict-nec (thereᶜ c q) (conflict u d) = cons↥ (conflict-nec q d)

conflict-suf : ∀ {xs ys zs as bs cs ds es fs} {e₁ : ES xs ys} {e₂ : ES xs zs} {p : e₁ ⋎ e₂} {e₃ : ES₃ xs}
                 {u : Val as bs} {v : Val cs ds} {w : Val es fs} {c : Conflict u v w} ->
                 e₁ , e₂ ↥ c -> Diff₃ e₁ e₂ e₃ -> c ∈ᶜ e₃
conflict-suf (InsIns α .α (here y .y) α≠β) (merge (Idem .y) d) = ⊥-elim (α≠β refl)
conflict-suf (InsIns α β (here x y) α≠β) (conflict (InsIns .x .y α≠β₁) d) = here (InsIns α β)
conflict-suf (InsIns α β (cons x y q) α≠β) (merge m d) = there _ (conflict-suf (InsIns α β q α≠β) d)
conflict-suf (InsIns α β (cons x y q) α≠β) (conflict u d) = thereᶜ _ (conflict-suf (InsIns α β q α≠β) d)

conflict-suf (UpdUpd β .β γ (here x y) α≠β α≠γ β≠γ) (merge (Id₁ .x .y v≠w) d) = ⊥-elim (α≠β refl)
conflict-suf (UpdUpd γ β .γ (here x y) α≠β α≠γ β≠γ) (merge (Id₂ .x .y v≠w) d) = ⊥-elim (α≠γ refl)
conflict-suf (UpdUpd α β .β (here x .x) α≠β α≠γ β≠γ) (merge (Idem .x) d) = ⊥-elim (β≠γ refl)
conflict-suf (UpdUpd α β γ (here x y) α≠β α≠γ β≠γ) (conflict (UpdUpd .x .y α≠β₁ α≠γ₁ β≠γ₁) d) = here (UpdUpd α β γ)
conflict-suf (UpdUpd α β γ (cons x y q) α≠β α≠γ β≠γ) (merge m r) = there _ (conflict-suf (UpdUpd α β γ q α≠β α≠γ β≠γ) r)
conflict-suf (UpdUpd α β γ (cons x y q) α≠β α≠γ β≠γ) (conflict u r) = thereᶜ _ (conflict-suf (UpdUpd α β γ q α≠β α≠γ β≠γ) r)

conflict-suf (UpdDel α .α (here f y) α≠β) (merge (Id₁ .f .y _) r) = ⊥-elim (α≠β refl)
conflict-suf (UpdDel α β (here x y) α≠β) (conflict (UpdDel .x .y α≠β₁) r) = here (UpdDel α β)
conflict-suf (UpdDel α β (cons x y q) α≠β) (merge m r) = there _ (conflict-suf (UpdDel α β q α≠β) r)
conflict-suf (UpdDel α β (cons x y q) α≠β) (conflict u r) = thereᶜ _ (conflict-suf (UpdDel α β q α≠β) r)

conflict-suf (DelUpd α .α (here f y) α≠β) (merge (Id₂ .f .y _) r) = ⊥-elim (α≠β refl)
conflict-suf (DelUpd α β (here x y) α≠β) (conflict (DelUpd .x .y α≠β₁) r) = here (DelUpd α β)
conflict-suf (DelUpd α β (cons x y q) α≠β) (merge m r) = there _ (conflict-suf (DelUpd α β q α≠β) r)
conflict-suf (DelUpd α β (cons x y q) α≠β) (conflict u r) = thereᶜ _ (conflict-suf (DelUpd α β q α≠β) r)

--------------------------------------------------------------------------------
