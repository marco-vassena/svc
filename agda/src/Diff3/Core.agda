module Diff3.Core where

open import Diff.Core public
open import EditScript.Core public
open import EditScript.Aligned public
open import EditScript.Mapping

open import Relation.Nullary
open import Data.Product
open import Data.Sum
open import Data.List
open import Relation.Binary

--------------------------------------------------------------------------------

data Conflict : Set₁ where
  UpdUpd : ∀ {xs ys a} -> View xs a -> View ys a -> Conflict
  DelUpd : ∀ {xs ys a} -> View xs a -> View ys a -> Conflict
  UpdDel : ∀ {xs ys a} -> View xs a -> View ys a -> Conflict
  InsIns : ∀ {xs ys a b} -> View xs a -> View ys b -> Conflict

-- Untytped version of ES3
data ES₃ : Set₁ where
  End : ES₃
  Ins : ∀ {xs a} -> View xs a -> ES₃ -> ES₃
  Del : ∀ {xs a} -> View xs a -> ES₃ -> ES₃
  Upd : ∀ {xs ys a} -> View xs a -> View ys a -> ES₃ -> ES₃
  Cpy : ∀ {xs a} -> View xs a -> ES₃ -> ES₃
  Cnf : Conflict -> ES₃ -> ES₃

--------------------------------------------------------------------------------

-- Refifies result of diff3
data Diff₃ : ∀ {xs ys zs ws} -> ES xs ys -> ES xs zs -> ES xs ws -> Set where
  End : Diff₃ End End End
  InsIns : ∀ {xs ys zs ws as a} {e₁ : ES xs (as ++ ys)} {e₂ : ES xs (as ++ zs)} {e₃ : ES xs (as ++ ws)}
           -> (x : View as a) -> Diff₃ e₁ e₂ e₃ -> Diff₃ (Ins x e₁) (Ins x e₂) (Ins x e₃)
  Ins₁ : ∀ {xs ys zs ws as a} {e₁ : ES xs (as ++ ys)} {e₂ : ES xs zs} {e₃ : ES xs (as ++ ws)} {{i : ¬Ins e₂}}
           -> (x : View as a) -> Diff₃ e₁ e₂ e₃ -> Diff₃ (Ins x e₁) e₂ (Ins x e₃)
  Ins₂ : ∀ {xs ys zs ws as a} {e₁ : ES xs ys} {e₂ : ES xs (as ++ zs)} {e₃ : ES xs (as ++ ws)} {{i : ¬Ins e₁}} 
           -> (x : View as a) -> Diff₃ e₁ e₂ e₃ -> Diff₃ e₁ (Ins x e₂) (Ins x e₃)
  DelDel : ∀ {xs ys zs ws as a} {e₁ : ES (as ++ xs) ys} {e₂ : ES (as ++ xs) zs} {e₃ : ES (as ++ xs) ws}
           -> (x : View as a) -> Diff₃ e₁ e₂ e₃ -> Diff₃ (Del x e₁) (Del x e₂) (Del x e₃)
  DelCpy : ∀ {xs ys zs ws as a} {e₁ : ES (as ++ xs) ys} {e₂ : ES (as ++ xs) (as ++ zs)} {e₃ : ES (as ++ xs) ws}
           ->  (x : View as a) -> Diff₃ e₁ e₂ e₃ -> Diff₃ (Del x e₁) (Cpy x e₂) (Del x e₃)
  CpyDel : ∀ {xs ys zs ws as a} {e₁ : ES (as ++ xs) (as ++ ys)} {e₂ : ES (as ++ xs) zs} {e₃ : ES (as ++ xs) ws}
           ->  (x : View as a) -> Diff₃ e₁ e₂ e₃ -> Diff₃ (Cpy x e₁) (Del x e₂) (Del x e₃)
  CpyCpy : ∀ {xs ys zs ws as a} {e₁ : ES (as ++ xs) (as ++ ys)} {e₂ : ES (as ++ xs) (as ++ zs)} {e₃ : ES (as ++ xs) (as ++ ws)}
           -> (x : View as a) -> Diff₃ e₁ e₂ e₃ -> Diff₃ (Cpy x e₁) (Cpy x e₂) (Cpy x e₃)
  CpyUpd : ∀ {xs ys zs ws as bs a} {e₁ : ES (as ++ xs) (as ++ ys)} {e₂ : ES (as ++ xs) (bs ++ zs)} {e₃ : ES (as ++ xs) (bs ++ ws)} 
           -> (x : View as a) (y : View bs a) -> Diff₃ e₁ e₂ e₃ -> Diff₃ (Cpy x e₁) (Upd x y e₂) (Upd x y e₃)
  UpdCpy : ∀ {xs ys zs ws as bs a} {e₁ : ES (as ++ xs) (bs ++ ys)} {e₂ : ES (as ++ xs) (as ++ zs)} {e₃ : ES (as ++ xs) (bs ++ ws)} 
           -> (x : View as a) (y : View bs a) -> Diff₃ e₁ e₂ e₃ -> Diff₃ (Upd x y e₁) (Cpy x e₂) (Upd x y e₃)
  UpdUpd : ∀ {xs ys zs ws as bs a} {e₁ : ES (as ++ xs) (bs ++ ys)} {e₂ : ES (as ++ xs) (bs ++ zs)} {e₃ : ES (as ++ xs) (bs ++ ws)} 
           -> (x : View as a) (y : View bs a) -> Diff₃ e₁ e₂ e₃ -> Diff₃ (Upd x y e₁) (Upd x y e₂) (Upd x y e₃)

Diff₃-sym : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} 
            -> Diff₃ e₁ e₂ e₃ -> Diff₃ e₂ e₁ e₃
Diff₃-sym End = End
Diff₃-sym (InsIns x d) = InsIns x (Diff₃-sym d)
Diff₃-sym (Ins₁ x d) = Ins₂ x (Diff₃-sym d)
Diff₃-sym (Ins₂ x d) = Ins₁ x (Diff₃-sym d)
Diff₃-sym (DelDel x d) = DelDel x (Diff₃-sym d)
Diff₃-sym (DelCpy x d) = CpyDel x (Diff₃-sym d)
Diff₃-sym (CpyDel x d) = DelCpy x (Diff₃-sym d)
Diff₃-sym (CpyCpy x d) = CpyCpy x (Diff₃-sym d)
Diff₃-sym (CpyUpd x y d) = UpdCpy x y (Diff₃-sym d)
Diff₃-sym (UpdCpy x y d) = CpyUpd x y (Diff₃-sym d)
Diff₃-sym (UpdUpd x y d) = UpdUpd x y (Diff₃-sym d)

--------------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality

Diff₃⟪_⟫ : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} ->
            Diff₃ e₁ e₂ e₃ -> ⟪ e₃ ⟫ ≡ ⟪ e₁ ⟫
Diff₃⟪ End ⟫ = refl
Diff₃⟪ InsIns x d ⟫ = Diff₃⟪ d ⟫
Diff₃⟪ Ins₁ x d ⟫ = Diff₃⟪ d ⟫
Diff₃⟪ Ins₂ x d ⟫ = Diff₃⟪ d ⟫
Diff₃⟪ DelDel x d ⟫ rewrite Diff₃⟪ d ⟫ = refl
Diff₃⟪ DelCpy x d ⟫ rewrite Diff₃⟪ d ⟫ = refl
Diff₃⟪ CpyDel x d ⟫ rewrite Diff₃⟪ d ⟫ = refl
Diff₃⟪ CpyCpy x d ⟫ rewrite Diff₃⟪ d ⟫ = refl
Diff₃⟪ CpyUpd x y d ⟫ rewrite Diff₃⟪ d ⟫ = refl
Diff₃⟪ UpdCpy x y d ⟫ rewrite Diff₃⟪ d ⟫ = refl
Diff₃⟪ UpdUpd x y d ⟫ rewrite Diff₃⟪ d ⟫ = refl 

Diff₃~ : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} 
           -> Diff₃ e₁ e₂ e₃ -> e₁ ~ e₂
Diff₃~ End = End
Diff₃~ (InsIns x d) = InsIns x x (Diff₃~ d)
Diff₃~ (Ins₁ x d) = Ins₁ x (Diff₃~ d)
Diff₃~ (Ins₂ x d) = Ins₂ x (Diff₃~ d)
Diff₃~ (DelDel x d) = DelDel x (Diff₃~ d)
Diff₃~ (DelCpy x d) = DelCpy x (Diff₃~ d)
Diff₃~ (CpyDel x d) = CpyDel x (Diff₃~ d)
Diff₃~ (CpyCpy x d) = CpyCpy x (Diff₃~ d)
Diff₃~ (CpyUpd x y d) = CpyUpd x y (Diff₃~ d)
Diff₃~ (UpdCpy x y d) = UpdCpy x y (Diff₃~ d)
Diff₃~ (UpdUpd x y d) = UpdUpd x y y (Diff₃~ d)

-- I would like to prove symmetricity of Diff₃ reusing diff3-sym
-- but at best I stumble upon ill-formed with clause
-- diff3-sym' : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} 
--              -> Diff₃ e₁ e₂ e₃ -> Diff₃ e₂ e₁ e₃
-- diff3-sym' d  with diff3~ d | diff3↓ d
-- ... | p | q with inspect (diff3 _ _) p | inspect (diff3 _ _) (~-sym p)
-- diff3-sym' d | p | q | Reveal_is_.[ refl ] | Reveal_is_.[ refl ] with diff₃-suf p q | diff₃-suf (~-sym p) (↓-sym p q)
-- ... | a | b with diff₃-nec p q a | diff₃-nec (~-sym p) (↓-sym p q) b
-- diff3-sym' d | p | q | Reveal_is_.[ refl ] | Reveal_is_.[ refl ] | a | b | refl | refl 
--   with diff₃-nec p q a | diff₃-nec (~-sym p) (↓-sym p q) b
-- diff3-sym' d | p | q | Reveal_is_.[ refl ] | Reveal_is_.[ refl ] | a | b | refl | refl | refl | refl = {!!}

-- diff3-sym' d | p | q | Reveal_is_.[ refl ] with inspect (toES p) q
-- diff3-sym' d | p | q | Reveal_is_.[ refl ] | Reveal_is_.[ refl ] with diff₃-nec p q d
-- ... | r = {!!}

-- with toES (diff3~ d) (diff3↓ d) | diff₃-nec (diff3~ d) (diff3↓ d) d
-- diff3-sym' d | e₃ | p with diff3-sym (diff3~ d) (diff3-wt (diff3~ d) (diff3↓ d)) 
-- ... | a = {!!}

--------------------------------------------------------------------------------

-- Relation between Diff and Diff₃
-- Note that implicitly says that the edit scripts all originated from the 
-- same source object
getDiff : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} ->
            Diff₃ e₁ e₂ e₃ -> Diff ⟪ e₃ ⟫ ⟦ e₁ ⟧ e₁ × Diff ⟪ e₃ ⟫ ⟦ e₂ ⟧ e₂
getDiff {e₁ = e₁} {e₂ = e₂} {e₃ = e₃} d₃
  rewrite Diff₃⟪ d₃ ⟫ with mkDiff e₁ | mkDiff e₂ | (Diff₃~ d₃)
... | d₁ | d₂ | p = d₁ , aux d₂ (Diff~nec d₁ d₂ p)
  where aux : Diff ⟪ e₂ ⟫ ⟦ e₂ ⟧ e₂ -> ⟪ e₁ ⟫ ≡ ⟪ e₂ ⟫ -> Diff ⟪ e₁ ⟫ ⟦ e₂ ⟧ e₂
        aux d p rewrite p = d

--------------------------------------------------------------------------------
-- Merge datatypes


-- It minimally represents how mappings can be merged.
-- Id₁ and Id₂ can be used when one of the two function is just a copy, in which case we choose the other function.
-- The third constructor Idem corresponds to the fact that ⊔ is idempotent, therefore any 
-- function can be successfully merged against itself producing the same function. 
-- Note that this datatype is polymorphic in the source node v, which is common
-- in all the three mappings.
data _≔_⊔_ {v : Val} : ∀ {a b c} -> v ~> a -> v ~> b -> v ~> c -> Set₁ where
  Id₁ : ∀ {w} -> (f : v ~> v) (g : v ~> w) -> g ≔ f ⊔ g
  Id₂ : ∀ {w} -> (f : v ~> w) (g : v ~> v) -> f ≔ f ⊔ g
  Idem : ∀ {w} -> (f : v ~> w) -> f ≔ f ⊔ f

infixl 2 _≔_⊔_

-- This datatype is the proof that two mapping cannot be merged, thus ⊔ fails producing a conflict.
-- There are 4 constructors, one for each possible conflict.
-- Furthermore necessary inequality proofs about nodes are included.  
data _⊔_↥_ : ∀ {v w z} -> (v ~> w) -> (v ~> z) -> Conflict -> Set where
  InsIns : ∀ {as a bs b} {α : View as a} {β : View bs b} 
             (f : ⊥ ~> ⟨ α ⟩) (g : ⊥ ~> ⟨ β ⟩) (α≠β : ¬ (α ⋍ β)) -> f ⊔ g ↥ InsIns α β
  UpdUpd : ∀ {as bs cs a} {α : View as a} {β : View bs a} {γ : View cs a}
             (f : ⟨ α ⟩ ~> ⟨ β ⟩) (g : ⟨ α ⟩ ~> ⟨ γ ⟩)
             (α≠β : ¬ (α ⋍ β)) (α≠γ : ¬ (α ⋍ γ)) (β≠γ : ¬ (β ⋍ γ))
             -> f ⊔ g ↥ UpdUpd β γ
  UpdDel : ∀ {as bs a} {α : View as a} {β : View bs a} 
             (f : ⟨ α ⟩ ~> ⟨ β ⟩) (g : ⟨ α ⟩ ~> ⊥) (α≠β : ¬ (α ⋍ β)) -> f ⊔ g ↥ UpdDel α β
  DelUpd : ∀ {as bs a} {α : View as a} {β : View bs a} 
             (f : ⟨ α ⟩ ~> ⊥) (g : ⟨ α ⟩ ~> ⟨ β ⟩) (α≠β : ¬ (α ⋍ β)) -> f ⊔ g ↥ DelUpd α β

infixl 2 _⊔_↥_

open import Data.Sum

≡-⋍ : ∀ {as bs} {a b : Set} {α : View as a} {β : View bs b} -> ¬ (a ≡ b) -> ¬ (α ⋍ β)
≡-⋍ ¬p refl = ¬p refl

-- For any two mapping from the same source u, either there is a third mapping h from u that merges them
-- or the merge fails with some conflict c. 
mergeOrConflict : ∀ {u v w} (f : u ~> v) (g : u ~> w) -> ∃₂ {A = Val} {B = _~>_ u} (λ _ h → h ≔ f ⊔ g) ⊎ (∃ λ c -> f ⊔ g ↥ c)
mergeOrConflict (Ins {a = a} α) (Ins {a = b} β) with eq? a b 
mergeOrConflict (Ins α) (Ins β) | yes refl with α =?= β
mergeOrConflict (Ins α) (Ins .α) | yes refl | yes refl = inj₁ (⟨ α ⟩ , Ins α , Idem (Ins α))
mergeOrConflict (Ins α) (Ins β) | yes refl | no ¬p = inj₂ (InsIns α β , InsIns (Ins α) (Ins β) ¬p)
mergeOrConflict (Ins α) (Ins β) | no ¬p = inj₂ (InsIns α β , InsIns (Ins α) (Ins β) (≡-⋍ ¬p))
mergeOrConflict (Ins α) End = inj₁ (⟨ α ⟩ , Ins α , Id₂ (Ins α) End)
mergeOrConflict (Del α) (Del .α) = inj₁ (⊥ , Del α , Idem (Del α))
mergeOrConflict (Del α) (Cpy .α) = inj₁ (⊥ , Del α , Id₂ (Del α) (Cpy α))
-- Implicitly with Upd we assume that α≠β however ~> is enough expressive to cover also this case.
mergeOrConflict (Del α) (Upd .α β) with α =?= β
mergeOrConflict (Del α) (Upd .α .α) | yes refl = inj₁ (⊥ , Del α , Id₂ (Del α) (Upd α α))
mergeOrConflict (Del α) (Upd .α β) | no ¬p = inj₂ (DelUpd α β , DelUpd (Del α) (Upd α β) ¬p)
mergeOrConflict (Cpy α) g = inj₁ (_ , g , Id₁ (Cpy α) g)
mergeOrConflict (Upd α β) (Del .α) with α =?= β
mergeOrConflict (Upd α .α) (Del .α) | yes refl = inj₁ (⊥ , Del α , Id₁ (Upd α α) (Del α))
mergeOrConflict (Upd α β) (Del .α) | no ¬p = inj₂ (UpdDel α β , UpdDel (Upd α β) (Del α) ¬p)
mergeOrConflict (Upd α β) (Cpy .α) = inj₁ (⟨ β ⟩ , Upd α β , Id₂ (Upd α β) (Cpy α))
mergeOrConflict (Upd α β) (Upd .α γ) with β =?= γ
mergeOrConflict (Upd α β) (Upd .α .β) | yes refl = inj₁ (⟨ β ⟩ , Upd α β , Idem (Upd α β))
mergeOrConflict (Upd α β) (Upd .α γ) | no ¬p with α =?= β
mergeOrConflict (Upd β .β) (Upd .β γ) | no ¬p | yes refl = inj₁ (⟨ γ ⟩ , Upd β γ , Id₁ (Upd β β) (Upd β γ))
mergeOrConflict (Upd α β) (Upd .α γ) | no ¬p₁ | no ¬p with α =?= γ
mergeOrConflict (Upd α β) (Upd .α .α) | no ¬p₁ | no ¬p | yes refl = inj₁ (⟨ β ⟩ , Upd α β , Id₂ (Upd α β) (Upd α α))
mergeOrConflict (Upd α β) (Upd .α γ) | no β≠γ | no α≠β | no α≠γ = inj₂ (UpdUpd β γ , UpdUpd (Upd α β) (Upd α γ) α≠β α≠γ β≠γ)
mergeOrConflict End g = inj₁ (_ , g , Id₁ End g)

--------------------------------------------------------------------------------
-- RawMapping
--------------------------------------------------------------------------------

-- TODO better name
-- It represents a partial mapping, which may contain conflicts. 
data RawMapping : Set₁ where
  [] : RawMapping
  _∷_ : ∀ {a b} -> a ~> b -> RawMapping -> RawMapping
  _∷ᶜ_ : Conflict -> RawMapping -> RawMapping


data _∈ᶜ_ : Conflict -> RawMapping -> Set₁ where
  here : ∀ {xs} (c : Conflict) -> c ∈ᶜ c ∷ᶜ xs
  there : ∀ {xs v w} {c : Conflict} (x : v ~> w) -> c ∈ᶜ xs -> c ∈ᶜ x ∷ xs
  thereᶜ : ∀ {xs c} (c' : Conflict) -> c ∈ᶜ xs -> c ∈ᶜ c' ∷ᶜ xs

infixr 3 _∈ᶜ_ 

--------------------------------------------------------------------------------

-- TODO point out in thesis that we need to use ⋎ to keep things aligned in the proofs.
-- p ⇓ zs is the proof that two aligned mapping xs ⋎ ys when merged produce the 
-- RawMapping zs. Unilateral inserts are always accepted (ins₁, ins₂).
-- The constructor merge requires the proof z ≔ x ⊔ y, i.e. x and y can be successfully merged
-- producing the mapping z, which can now be prepended to zs.
-- The constructor conflict instead requires the proof that x ⊔ y ↥ c, i.e. x and y cannot
-- be merged and therefore produce a conflict c, which is prepended to zs.
data _⇓_ : ∀ {xs ys} -> xs ⋎ ys -> RawMapping -> Set₁ where
  nil : nil ⇓ []
  merge : ∀ {xs ys zs a b c d} {p : xs ⋎ ys} {x : a ~> b} {y : a ~> c} {z : a ~> d} -> 
          (m : z ≔ x ⊔ y) -> p ⇓ zs -> cons x y p ⇓ (z ∷ zs)
  conflict : ∀ {xs ys zs v w z c} {x : v ~> w} {y : v ~> z} {p : xs ⋎ ys}  -> 
               (u : x ⊔ y ↥ c) -> p ⇓ zs -> cons x y p ⇓ (c ∷ᶜ zs)
  ins₁ : ∀ {xs ys zs as a} {p : xs ⋎ ys} {α : View as a} {{i : ¬Insᵐ ys}} (x : ⊥ ~> ⟨ α ⟩) -> p ⇓ zs -> ins₁ x p ⇓ (x ∷ zs)
  ins₂ : ∀ {xs ys zs as a} {p : xs ⋎ ys} {α : View as a} {{i : ¬Insᵐ xs}} (y : ⊥ ~> ⟨ α ⟩) -> p ⇓ zs -> ins₂ y p ⇓ (y ∷ zs)   
