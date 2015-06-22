module Diff3.Core where

open import Diff.Core public
open import EditScript.Core public
open import EditScript.Aligned public
open import EditScript.Mapping

open import Relation.Nullary
open import Data.Product hiding (swap)
open import Data.Sum
open import Data.List
open import Relation.Binary.PropositionalEquality

--------------------------------------------------------------------------------

data Conflict : ∀ {as bs cs ds es fs} (u : Val as bs) (v : Val cs ds) (w : Val es fs) -> Set₁ where
  UpdUpd : ∀ {as bs cs a} (α : View as a) (β : View bs a) (γ : View cs a) -> Conflict ⟨ α ⟩ ⟨ β ⟩ ⟨ γ ⟩
  DelUpd : ∀ {as bs a} (α : View as a) (β : View bs a) -> Conflict ⟨ α ⟩ ⊥ ⟨ β ⟩
  UpdDel : ∀ {as bs a} (α : View as a) (β : View bs a) -> Conflict ⟨ α ⟩ ⟨ β ⟩ ⊥ 
  InsIns : ∀ {a b as bs} -> (α : View as a) (β : View bs b) -> Conflict ⊥ ⟨ α ⟩ ⟨ β ⟩

swap : ∀ {as bs cs ds es fs} {u : Val as bs} {v : Val cs ds} {w : Val es fs} -> Conflict u v w -> Conflict u w v
swap (UpdUpd α β γ) = UpdUpd α γ β
swap (DelUpd α β) = UpdDel α β
swap (UpdDel α β) = DelUpd α β
swap (InsIns α β) = InsIns β α

data ES₃ : List Set -> List Set -> Set₁ where
  [] : ES₃ [] []
  _∷_ : ∀ {as bs cs ds xs ys} {v : Val as bs} {w : Val cs ds} -> v ~> w -> ES₃ (as ++ xs) (cs ++ ys) -> ES₃ (bs ++ xs) (ds ++ ys)
  _∷ᶜ_ : ∀ {as bs cs ds es fs xs ys zs} {u : Val as bs} {v : Val cs ds} {w : Val es fs} -> 
           (c : Conflict u v w) -> ES₃ (as ++ xs) ys -> ES₃ (bs ++ xs) zs

sym₃ : ∀ {xs ys} -> ES₃ xs ys -> ES₃ xs ys
sym₃ [] = []
sym₃ (x ∷ e) = x ∷ sym₃ e
sym₃ (c ∷ᶜ e) = swap c ∷ᶜ sym₃ e

⟪_⟫₃ : ∀ {xs ys} -> ES₃ xs ys -> DList xs
⟪ [] ⟫₃ = []
⟪ Ins α ∷ e ⟫₃ = ⟪ e ⟫₃
⟪ Del α ∷ e ⟫₃ with dsplit ⟪ e ⟫₃
⟪ Del α ∷ e ⟫₃ | ds₁ , ds₂ = Node α ds₁ ∷ ds₂
⟪ Upd α β ∷ e ⟫₃ with dsplit ⟪ e ⟫₃
⟪ Upd α β ∷ e ⟫₃ | ds₁ , ds₂ = Node α ds₁ ∷ ds₂
⟪ Nop ∷ e ⟫₃ = ⟪ e ⟫₃
⟪ UpdUpd α β γ ∷ᶜ e ⟫₃ with dsplit ⟪ e ⟫₃
⟪ UpdUpd α β γ ∷ᶜ e ⟫₃ | ds₁ , ds₂ = Node α ds₁ ∷ ds₂
⟪ DelUpd α β ∷ᶜ e ⟫₃ with dsplit ⟪ e ⟫₃
⟪ DelUpd α β ∷ᶜ e ⟫₃ | ds₁ , ds₂ = Node α ds₁ ∷ ds₂
⟪ UpdDel α β ∷ᶜ e ⟫₃ with dsplit ⟪ e ⟫₃
⟪ UpdDel α β ∷ᶜ e ⟫₃ | ds₁ , ds₂ = Node α ds₁ ∷ ds₂
⟪ InsIns α β ∷ᶜ e ⟫₃ = ⟪ e ⟫₃

--------------------------------------------------------------------------------
-- Merge datatypes

-- TODO move to EditScript.Core
-- Heterogeneous equality for Val
data _≃_ {as bs} (v : Val as bs) : ∀ {cs ds} (w : Val cs ds) -> Set where
  refl : v ≃ v

-- TODO use ↧ for merge

-- It minimally represents how mappings can be merged.
-- Id₁ and Id₂ can be used when one of the two function is just a copy, in which case we choose the other function.
-- The third constructor Idem corresponds to the fact that ⊔ is idempotent, therefore any 
-- function can be successfully merged against itself producing the same function. 
-- Note that this datatype is polymorphic in the source node v, which is common
-- in all the three mappings.
data _≔_⊔_ {as bs} {v : Val as bs} : ∀ {cs ds es fs gs hs} {a : Val cs ds} {b : Val es fs} {c : Val gs hs} -> 
                                     v ~> a -> v ~> b -> v ~> c -> Set₁ where
  Id₁ : ∀ {cs ds} {w : Val cs ds} -> (f : v ~> v) (g : v ~> w) (v≠w : ¬ (v ≃ w)) -> g ≔ f ⊔ g
  Id₂ : ∀ {cs ds} {w : Val cs ds} -> (f : v ~> w) (g : v ~> v) (v≠w : ¬ (v ≃ w)) -> f ≔ f ⊔ g
  Idem : ∀ {cs ds} {w : Val cs ds} -> (f : v ~> w) -> f ≔ f ⊔ f

infixl 2 _≔_⊔_

⊔-sym : ∀ {as bs cs ds es fs gs hs} {v : Val as bs} {a : Val cs ds} {b : Val es fs} {c : Val gs hs}
          {f : v ~> a} {g : v ~> b} {h : v ~> c} -> h ≔ f ⊔ g -> h ≔ g ⊔ f
⊔-sym (Id₁ f g v≠w) = Id₂ g f v≠w
⊔-sym (Id₂ f g v≠w) = Id₁ g f v≠w
⊔-sym (Idem f) = Idem f
 
-- This datatype is the proof that two mapping cannot be merged, thus ⊔ fails producing a conflict.
-- There are 4 constructors, one for each possible conflict.
-- Furthermore necessary inequality proofs about nodes are included.  
data _⊔_↥_ : ∀ {as bs cs ds es fs} {v : Val as bs} {w : Val cs ds} {z : Val es fs}
               -> (v ~> w) -> (v ~> z) -> Conflict v w z -> Set where
  InsIns : ∀ {as a bs b} {α : View as a} {β : View bs b} 
             (f : ⊥ ~> ⟨ α ⟩) (g : ⊥ ~> ⟨ β ⟩) (α≠β : ¬ (α ⋍ β)) -> f ⊔ g ↥ InsIns α β
  UpdUpd : ∀ {as bs cs a} {α : View as a} {β : View bs a} {γ : View cs a}
             (f : ⟨ α ⟩ ~> ⟨ β ⟩) (g : ⟨ α ⟩ ~> ⟨ γ ⟩)
             (α≠β : ¬ (α ⋍ β)) (α≠γ : ¬ (α ⋍ γ)) (β≠γ : ¬ (β ⋍ γ)) -> f ⊔ g ↥ UpdUpd α β γ
  UpdDel : ∀ {as bs a} {α : View as a} {β : View bs a} 
             (f : ⟨ α ⟩ ~> ⟨ β ⟩) (g : ⟨ α ⟩ ~> ⊥) (α≠β : ¬ (α ⋍ β)) -> f ⊔ g ↥ UpdDel α β
  DelUpd : ∀ {as bs a} {α : View as a} {β : View bs a} 
             (f : ⟨ α ⟩ ~> ⊥) (g : ⟨ α ⟩ ~> ⟨ β ⟩) (α≠β : ¬ (α ⋍ β)) -> f ⊔ g ↥ DelUpd α β

infixl 2 _⊔_↥_

↥-sym : ∀ {as bs cs ds es fs} {v : Val as bs} {a : Val cs ds} {b : Val es fs} {c : Conflict v a b}
          {f : v ~> a} {g : v ~> b} -> f ⊔ g ↥ c -> g ⊔ f ↥ swap c
↥-sym (InsIns f g α≠β) = InsIns g f (¬⋍-sym α≠β)
↥-sym (UpdUpd f g α≠β α≠γ β≠γ) = UpdUpd g f α≠γ α≠β (¬⋍-sym β≠γ)
↥-sym (UpdDel f g α≠β) = DelUpd g f α≠β
↥-sym (DelUpd f g α≠β) = UpdDel g f α≠β

--------------------------------------------------------------------------------

-- Refifies result of diff3
data Diff₃ : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} -> e₁ ⋎ e₂ -> ES₃ xs ws -> Set₁ where
  nil : Diff₃ nil []
  merge : ∀ {xs ys zs ws as bs cs ds es fs gs hs} 
            {e₁ : ES (as ++ xs) (cs ++ ys)} {e₂ : ES (as ++ xs) (es ++ zs)} {e₃ : ES₃ (as ++ xs) (gs ++ ws)} 
            {p : e₁ ⋎ e₂} {u : Val as bs} {v : Val cs ds} {w : Val es fs} {z : Val gs hs} 
            {f : u ~> v} {g : u ~> w} {h : u ~> z} -> 
            (m : h ≔ f ⊔ g) -> Diff₃ p e₃ -> Diff₃ (cons f g p) (h ∷ e₃)
  conflict : ∀ {xs ys zs ws us as bs cs ds es fs} 
               {e₁ : ES (as ++ xs) (cs ++ ys)} {e₂ : ES (as ++ xs) (es ++ zs)} {e₃ : ES₃ (as ++ xs) us}
               {v : Val as bs} {w : Val cs ds} {z : Val es fs} {c : Conflict v w z}
               {x : v ~> w} {y : v ~> z} {p : e₁ ⋎ e₂} -> 
               (u : x ⊔ y ↥ c) -> Diff₃ p e₃ -> Diff₃ {ws = ws} (cons x y p) (c ∷ᶜ e₃)

Diff₃-sym : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES₃ xs ws} {p : e₁ ⋎ e₂} 
            -> Diff₃ p e₃ -> Diff₃ (⋎-sym p) (sym₃ e₃)
Diff₃-sym nil = nil
Diff₃-sym (merge m d) = merge (⊔-sym m) (Diff₃-sym d)
Diff₃-sym (conflict u d) = conflict (↥-sym u) (Diff₃-sym d)

--------------------------------------------------------------------------------

Diff₃⟪_⟫ : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES₃ xs ws} {p : e₁ ⋎ e₂} ->
            Diff₃ p e₃ -> ⟪ e₁ ⟫ ≡ ⟪ e₃ ⟫₃
Diff₃⟪ nil ⟫ = refl
Diff₃⟪ merge {f = Ins α} {h = Ins α₁} m e ⟫ = Diff₃⟪ e ⟫
Diff₃⟪ merge {f = Ins α} {h = Nop} m e ⟫ = Diff₃⟪ e ⟫
Diff₃⟪ merge {f = Del α} {h = Del .α} m e ⟫ rewrite Diff₃⟪ e ⟫ = refl
Diff₃⟪ merge {f = Del α} {h = Upd .α β} m e ⟫ rewrite Diff₃⟪ e ⟫ = refl
Diff₃⟪ merge {f = Upd α β} {h = Del .α} m e ⟫ rewrite Diff₃⟪ e ⟫ = refl
Diff₃⟪ merge {f = Upd α β} {h = Upd .α γ} m e ⟫ rewrite Diff₃⟪ e ⟫ = refl
Diff₃⟪ merge {f = Nop} {h = Ins α} m e ⟫ = Diff₃⟪ e ⟫
Diff₃⟪ merge {f = Nop} {h = Nop} m e ⟫ = Diff₃⟪ e ⟫
Diff₃⟪ conflict (InsIns (Ins α) y α≠β) e ⟫ = Diff₃⟪ e ⟫
Diff₃⟪ conflict (UpdUpd (Upd α β) y α≠β α≠γ β≠γ) e ⟫ rewrite Diff₃⟪ e ⟫ = refl
Diff₃⟪ conflict (UpdDel (Upd α β) y α≠β) e ⟫ rewrite Diff₃⟪ e ⟫ = refl
Diff₃⟪ conflict (DelUpd (Del α) y α≠β) e ⟫ rewrite Diff₃⟪ e ⟫ = refl

--------------------------------------------------------------------------------

-- Relation between Diff and Diff₃
-- Note that implicitly says that the edit scripts all originated from the 
-- same source object
-- getDiff : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} ->
--             Diff₃ e₁ e₂ e₃ -> Diff ⟪ e₃ ⟫ ⟦ e₁ ⟧ e₁ × Diff ⟪ e₃ ⟫ ⟦ e₂ ⟧ e₂
-- getDiff {e₁ = e₁} {e₂ = e₂} {e₃ = e₃} d₃
--   rewrite Diff₃⟪ d₃ ⟫ with mkDiff e₁ | mkDiff e₂ | (Diff₃~ d₃)
-- ... | d₁ | d₂ | p = d₁ , aux d₂ (Diff~nec d₁ d₂ p)
--   where aux : Diff ⟪ e₂ ⟫ ⟦ e₂ ⟧ e₂ -> ⟪ e₁ ⟫ ≡ ⟪ e₂ ⟫ -> Diff ⟪ e₁ ⟫ ⟦ e₂ ⟧ e₂
--         aux d p rewrite p = d

≃-⋍ : ∀ {as bs} {a b : Set} {α : View as a} {β : View bs b} -> ¬ (⟨ α ⟩ ≃ ⟨ β ⟩) -> ¬ (α ⋍ β)
≃-⋍ ¬p refl = ¬p refl

open import Diff.Safety -- remove

_≟ⱽ_ : ∀ {as bs cs ds} (v : Val as bs) (w : Val cs ds) -> Dec (v ≃ w)
⊥ ≟ⱽ ⊥ = yes refl
⊥ ≟ⱽ ⟨ α ⟩ = no (λ ())
⟨ α ⟩ ≟ⱽ ⊥ = no (λ ())
⟨ α ⟩ ≟ⱽ ⟨ β ⟩ with α ≟ β
⟨ α ⟩ ≟ⱽ ⟨ .α ⟩ | yes refl = yes refl
⟨ α ⟩ ≟ⱽ ⟨ β ⟩ | no α≠β = no (aux α≠β) 
  where aux : ∀ {as bs a b} {α : View as a} {β : View bs b} -> ¬ (α ⋍ β) -> ¬ (⟨ α ⟩ ≃ ⟨ β ⟩)
        aux α≠β₁ refl = α≠β₁ refl

-- For any two mapping from the same source u, either there is a third mapping h from u that merges them
-- or the merge fails with some conflict c. 
-- TODO swap inj₁ and inj₂
mergeOrConflict : ∀ {as bs cs ds es fs} {u : Val as bs} {v : Val cs ds} {w : Val es fs} 
                    (f : u ~> v) (g : u ~> w) -> ∃ᴹ (λ h → h ≔ f ⊔ g) ⊎ (∃ λ c -> f ⊔ g ↥ c)
mergeOrConflict (Ins {a = a} α) (Ins {a = b} β) with α ≟ β
mergeOrConflict (Ins α) (Ins .α) | yes refl = inj₁ (Ins α , Idem (Ins α))
mergeOrConflict (Ins α) (Ins β) | no ¬p = inj₂ (InsIns α β , InsIns (Ins α) (Ins β) ¬p)
mergeOrConflict (Ins α) Nop = inj₁ (Ins α , Id₂ (Ins α) Nop (λ ()))
mergeOrConflict (Del α) (Del .α) = inj₁ (Del α , Idem (Del α))
mergeOrConflict (Del α) (Upd .α β) with α =?= β
mergeOrConflict (Del α) (Upd .α .α) | yes refl = inj₁ (Del α , Id₂ (Del α) (Upd α α) (λ ()))
mergeOrConflict (Del α) (Upd .α β) | no ¬p = inj₂ (DelUpd α β , DelUpd (Del α) (Upd α β) ¬p)
mergeOrConflict (Upd α β) (Del .α) with α =?= β
mergeOrConflict (Upd α .α) (Del .α) | yes refl = inj₁ (Del α , Id₁ (Upd α α) (Del α) (λ ()))
mergeOrConflict (Upd α β) (Del .α) | no ¬p = inj₂ (UpdDel α β , UpdDel (Upd α β) (Del α) ¬p)
mergeOrConflict (Upd α β) (Upd .α γ) with ⟨ β ⟩ ≟ⱽ ⟨ γ ⟩
mergeOrConflict (Upd α β) (Upd .α .β) | yes refl = inj₁ (Upd α β , Idem (Upd α β))
mergeOrConflict (Upd α β) (Upd .α γ) | no β≠γ with ⟨ α ⟩ ≟ⱽ ⟨ β ⟩
mergeOrConflict (Upd β .β) (Upd .β γ) | no β≠γ | yes refl = inj₁ (Upd β γ , Id₁ (Upd β β) (Upd β γ) β≠γ)
mergeOrConflict (Upd α β) (Upd .α γ) | no β≠γ | no α≠β with ⟨ α ⟩ ≟ⱽ ⟨ γ ⟩
mergeOrConflict (Upd α β) (Upd .α .α) | no β≠γ | no α≠β | yes refl = inj₁ (Upd α β , Id₂ (Upd α β) (Upd α α) α≠β)
mergeOrConflict (Upd α β) (Upd .α γ) | no β≠γ | no α≠β | no α≠γ 
  = inj₂ (UpdUpd α β γ , UpdUpd (Upd α β) (Upd α γ) (≃-⋍ α≠β) (≃-⋍ α≠γ) (≃-⋍ β≠γ))
mergeOrConflict Nop (Ins α) = inj₁ (Ins α , Id₁ Nop (Ins α) (λ ()))
mergeOrConflict Nop Nop = inj₁ (Nop , Idem Nop)

--------------------------------------------------------------------------------

-- data _∈ᶜ_ : ∀ {as bs cs ds es fs} {v : Conflict -> ES₃ -> Set₁ where
--   here : ∀ {xs} (c : Conflict) -> c ∈ᶜ c ∷ᶜ xs
--   there : ∀ {xs as bs cs ds} {v : Val as bs} {w : Val cs ds} {c : Conflict} (x : v ~> w) -> c ∈ᶜ xs -> c ∈ᶜ x ∷ xs
--   thereᶜ : ∀ {xs c} (c' : Conflict) -> c ∈ᶜ xs -> c ∈ᶜ c' ∷ᶜ xs

-- infixr 3 _∈ᶜ_ 

--------------------------------------------------------------------------------
-- diff₃

-- _⨆_ : ∀ {xs ys} (e₁ e₂ : ES xs ys ) -> {{ p : e₁ ⋎ e₂ }} -> ES₃
-- _⨆_ (x ∷ xs) (y ∷ ys) {{cons .x .y p}} with mergeOrConflict x y
-- _⨆_ (x ∷ xs) (y ∷ ys) {{cons .x .y p}} | inj₁ (_ , z , _) = z ∷ (xs ⨆ ys)
-- _⨆_ (x ∷ xs) (y ∷ ys) {{cons .x .y p}} | inj₂ (c , _) = c ∷ᶜ (xs ⨆ ys)
-- _⨆_ .[] .[] {{nil}} = []

-- suf-⇓ : ∀ {xs ys} (p : xs ⋎ ys) -> p ⇓ (xs ⨆ ys)
-- suf-⇓ (cons x y p) with mergeOrConflict x y
-- suf-⇓ (cons x y p) | inj₁ (_ , z , m) = merge m (suf-⇓ p)
-- suf-⇓ (cons x y p) | inj₂ (c , u) = conflict u (suf-⇓ p)
-- suf-⇓ nil = nil 

-- -- Heterogeneous equality tailored for transformations
-- data _≅_ {a b} (x : a ~> b) : ∀ {c d} (y : c ~> d) → Set where
--    refl : x ≅ x

-- mergeConflictExclusive : ∀ {c s u v w} {x : s ~> u} {y : s ~> v} {z : s ~> w} -> z ≔ x ⊔ y -> ¬ (x ⊔ y ↥ c)
-- mergeConflictExclusive (Id₁ f y _) (UpdUpd .f .y α≠β α≠γ β≠γ) = α≠β refl
-- mergeConflictExclusive (Id₁ f y _) (UpdDel .f .y α≠β) = α≠β refl
-- mergeConflictExclusive (Id₂ f y _) (UpdUpd .f .y α≠β α≠γ β≠γ) = α≠γ refl
-- mergeConflictExclusive (Id₂ f y _) (DelUpd .f .y α≠β) = α≠β refl
-- mergeConflictExclusive (Idem x) (InsIns .x .x α≠β) = α≠β refl
-- mergeConflictExclusive (Idem x) (UpdUpd .x .x α≠β α≠γ β≠γ) = β≠γ refl

-- open import Data.Empty using (⊥-elim)

-- mergeDeterministic : ∀ {a b c d e} {x : a ~> b} {y : a ~> c} {z₁ : a ~> d} {z₂ : a ~> e} ->
--                        z₁ ≔ x ⊔ y -> z₂ ≔ x ⊔ y -> z₁ ≅ z₂
-- mergeDeterministic (Id₁ f g v≠w) (Id₁ .f .g v≠w₁) = refl
-- mergeDeterministic (Id₁ f g v≠w) (Id₂ .f .g v≠w₁) = ⊥-elim (v≠w₁ refl)
-- mergeDeterministic (Id₁ z₂ .z₂ v≠w) (Idem .z₂) = ⊥-elim (v≠w refl)
-- mergeDeterministic (Id₂ f g v≠w) (Id₁ .f .g v≠w₁) = ⊥-elim (v≠w₁ refl)
-- mergeDeterministic (Id₂ f g v≠w) (Id₂ .f .g v≠w₁) = refl
-- mergeDeterministic (Id₂ z₂ .z₂ v≠w) (Idem .z₂) = ⊥-elim (v≠w refl)
-- mergeDeterministic (Idem f) (Id₁ .f .f v≠w) = ⊥-elim (v≠w refl)
-- mergeDeterministic (Idem f) (Id₂ .f .f v≠w) = ⊥-elim (v≠w refl)
-- mergeDeterministic (Idem z₂) (Idem .z₂) = refl

-- conflictDeterministic : ∀ {u v w c₁ c₂} {x : u ~> v} {y : u ~> w} -> x ⊔ y ↥ c₁ -> x ⊔ y ↥ c₂ -> c₁ ≡ c₂
-- conflictDeterministic (InsIns x y α≠β) (InsIns .x .y α≠β₁) = refl
-- conflictDeterministic (UpdUpd x y α≠β α≠γ β≠γ) (UpdUpd .x .y α≠β₁ α≠γ₁ β≠γ₁) = refl
-- conflictDeterministic (UpdDel x y α≠β) (UpdDel .x .y α≠β₁) = refl
-- conflictDeterministic (DelUpd x y α≠β) (DelUpd .x .y α≠β₁) = refl

-- open import Data.Empty

-- nec-⇓ : ∀ {xs ys zs} {p :  xs ⋎ ys} -> p ⇓ zs -> zs ≡ xs ⨆ ys
-- nec-⇓ nil = refl
-- nec-⇓ (merge {x = x} {y = y} m q) with mergeOrConflict x y
-- nec-⇓ (merge m q) | inj₁ (v , z , m') with mergeDeterministic m m'
-- nec-⇓ (merge m q) | inj₁ (v , z , m') | refl = cong (_∷_ z) (nec-⇓ q)
-- nec-⇓ (merge m q) | inj₂ (c , u) = ⊥-elim (mergeConflictExclusive m u)
-- nec-⇓ (conflict {x = x} {y = y} u q) with mergeOrConflict x y
-- nec-⇓ (conflict u q) | inj₁ (v , z , m) = ⊥-elim (mergeConflictExclusive m u)
-- nec-⇓ (conflict u q) | inj₂ (c , u') with conflictDeterministic u u'
-- nec-⇓ (conflict u q) | inj₂ (c , u') | refl = cong (_∷ᶜ_ c) (nec-⇓ q)
