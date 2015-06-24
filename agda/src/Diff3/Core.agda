module Diff3.Core where

open import Diff3.ES3 public 

open import Relation.Nullary
open import Data.Product hiding (swap)
open import Data.Sum
open import Data.List
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality

--------------------------------------------------------------------------------
-- Merge datatypes.
-- These datatypes describe merging declaratively and succintly.
--------------------------------------------------------------------------------

-- It minimally represents how transformations can be merged.
-- Id₁ and Id₂ can be used when one of the two transformation is just id, 
-- in which case we choose the other transformation.
-- The third constructor Idem corresponds to the fact that ⊔ is idempotent, therefore any 
-- transformation can be successfully merged against itself producing itself. 
-- Note that this datatype is polymorphic in the source node v, which is common
-- in all the three mappings.
data _⊔_↧_ {as bs} {v : Val as bs} : ∀ {cs ds es fs gs hs} {a : Val cs ds} {b : Val es fs} {c : Val gs hs} -> 
                                     v ~> a -> v ~> b -> v ~> c -> Set₁ where
  Id₁ : ∀ {cs ds} {w : Val cs ds} -> (f : v ~> v) (g : v ~> w) (v≠w : ¬ (v ≃ w)) -> f ⊔ g ↧ g
  Id₂ : ∀ {cs ds} {w : Val cs ds} -> (f : v ~> w) (g : v ~> v) (v≠w : ¬ (v ≃ w)) -> f ⊔ g ↧ f
  Idem : ∀ {cs ds} {w : Val cs ds} -> (f : v ~> w) -> f ⊔ f ↧ f

infixl 2 _⊔_↧_

-- ⊔ is symmetric in the input transformations.
↧-sym : ∀ {as bs cs ds es fs gs hs} {v : Val as bs} {a : Val cs ds} {b : Val es fs} {c : Val gs hs}
          {f : v ~> a} {g : v ~> b} {h : v ~> c} -> f ⊔ g ↧ h -> g ⊔ f ↧ h
↧-sym (Id₁ f g v≠w) = Id₂ g f v≠w
↧-sym (Id₂ f g v≠w) = Id₁ g f v≠w
↧-sym (Idem f) = Idem f
 
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

-- ↥ is symmetric modulo `swap', because conflicts are inherently ordered.
↥-sym : ∀ {as bs cs ds es fs} {v : Val as bs} {a : Val cs ds} {b : Val es fs} {c : Conflict v a b}
          {f : v ~> a} {g : v ~> b} -> f ⊔ g ↥ c -> g ⊔ f ↥ swap c
↥-sym (InsIns f g α≠β) = InsIns g f (¬⋍-sym α≠β)
↥-sym (UpdUpd f g α≠β α≠γ β≠γ) = UpdUpd g f α≠γ α≠β (¬⋍-sym β≠γ)
↥-sym (UpdDel f g α≠β) = DelUpd g f α≠β
↥-sym (DelUpd f g α≠β) = UpdDel g f α≠β

-- For any two mapping from the same source u, either there is a third mapping h from u that merges them
-- or the merge fails with some conflict c. 
mergeOrConflict : ∀ {as bs cs ds es fs} {u : Val as bs} {v : Val cs ds} {w : Val es fs} 
                    (f : u ~> v) (g : u ~> w) -> (∃ λ c -> f ⊔ g ↥ c) ⊎ ∃ᴹ (λ h → f ⊔ g ↧ h)
mergeOrConflict (Ins {a = a} α) (Ins {a = b} β) with α ≟ β
mergeOrConflict (Ins α) (Ins .α) | yes refl = inj₂ (Ins α , Idem (Ins α))
mergeOrConflict (Ins α) (Ins β) | no ¬p = inj₁ (InsIns α β , InsIns (Ins α) (Ins β) ¬p)
mergeOrConflict (Ins α) Nop = inj₂ (Ins α , Id₂ (Ins α) Nop (λ ()))
mergeOrConflict (Del α) (Del .α) = inj₂ (Del α , Idem (Del α))
mergeOrConflict (Del α) (Upd .α β) with α =?= β
mergeOrConflict (Del α) (Upd .α .α) | yes refl = inj₂ (Del α , Id₂ (Del α) (Upd α α) (λ ()))
mergeOrConflict (Del α) (Upd .α β) | no ¬p = inj₁ (DelUpd α β , DelUpd (Del α) (Upd α β) ¬p)
mergeOrConflict (Upd α β) (Del .α) with α =?= β
mergeOrConflict (Upd α .α) (Del .α) | yes refl = inj₂ (Del α , Id₁ (Upd α α) (Del α) (λ ()))
mergeOrConflict (Upd α β) (Del .α) | no ¬p = inj₁ (UpdDel α β , UpdDel (Upd α β) (Del α) ¬p)
mergeOrConflict (Upd α β) (Upd .α γ) with ⟨ β ⟩ ≟ⱽ ⟨ γ ⟩
mergeOrConflict (Upd α β) (Upd .α .β) | yes refl = inj₂ (Upd α β , Idem (Upd α β))
mergeOrConflict (Upd α β) (Upd .α γ) | no β≠γ with ⟨ α ⟩ ≟ⱽ ⟨ β ⟩
mergeOrConflict (Upd β .β) (Upd .β γ) | no β≠γ | yes refl = inj₂ (Upd β γ , Id₁ (Upd β β) (Upd β γ) β≠γ)
mergeOrConflict (Upd α β) (Upd .α γ) | no β≠γ | no α≠β with ⟨ α ⟩ ≟ⱽ ⟨ γ ⟩
mergeOrConflict (Upd α β) (Upd .α .α) | no β≠γ | no α≠β | yes refl = inj₂ (Upd α β , Id₂ (Upd α β) (Upd α α) α≠β)
mergeOrConflict (Upd α β) (Upd .α γ) | no β≠γ | no α≠β | no α≠γ 
  = inj₁ (UpdUpd α β γ , UpdUpd (Upd α β) (Upd α γ) (≃-⋍ α≠β) (≃-⋍ α≠γ) (≃-⋍ β≠γ))
mergeOrConflict Nop (Ins α) = inj₂ (Ins α , Id₁ Nop (Ins α) (λ ()))
mergeOrConflict Nop Nop = inj₂ (Nop , Idem Nop)

--------------------------------------------------------------------------------

-- Merge and conficts are exclusive:
-- For any pair of transformations either they are merged or raise a conflict
mergeConflictExclusive : ∀ {as bs cs ds es fs gs hs} {s : Val as bs} {u : Val cs ds} {v : Val es fs} {w : Val gs hs} 
                           {c : Conflict s u v} {x : s ~> u} {y : s ~> v} {z : s ~> w} -> x ⊔ y ↧ z -> ¬ (x ⊔ y ↥ c)
mergeConflictExclusive (Id₁ f y _) (UpdUpd .f .y α≠β α≠γ β≠γ) = α≠β refl
mergeConflictExclusive (Id₁ f y _) (UpdDel .f .y α≠β) = α≠β refl
mergeConflictExclusive (Id₂ f y _) (UpdUpd .f .y α≠β α≠γ β≠γ) = α≠γ refl
mergeConflictExclusive (Id₂ f y _) (DelUpd .f .y α≠β) = α≠β refl
mergeConflictExclusive (Idem x) (InsIns .x .x α≠β) = α≠β refl
mergeConflictExclusive (Idem x) (UpdUpd .x .x α≠β α≠γ β≠γ) = β≠γ refl

-- Merges are deterministic.
-- If f ⊔ g ↧ h₁ and f ⊔ g ↧ h₂ then h₁ ≅ h₂.
mergeDeterministic : ∀ {as bs cs ds es fs gs hs is ls} 
                       {a : Val as bs} {b : Val cs ds} {c : Val es fs} {d : Val gs hs} {e : Val is ls} 
                       {f : a ~> b} {g : a ~> c} {h₁ : a ~> d} {h₂ : a ~> e} ->
                       f ⊔ g ↧ h₁ -> f ⊔ g ↧ h₂ -> h₁ ≅ h₂
mergeDeterministic (Id₁ f h₂ v≠w) (Id₁ .f .h₂ v≠w₁) = refl
mergeDeterministic (Id₁ f g v≠w) (Id₂ .f .g v≠w₁) = ⊥-elim (v≠w₁ refl)
mergeDeterministic (Id₁ f .f v≠w) (Idem .f) = ⊥-elim (v≠w refl)
mergeDeterministic (Id₂ f g v≠w) (Id₁ .f .g v≠w₁) = ⊥-elim (v≠w₁ refl)
mergeDeterministic (Id₂ h₂ g v≠w) (Id₂ .h₂ .g v≠w₁) = refl
mergeDeterministic (Id₂ g .g v≠w) (Idem .g) = ⊥-elim (v≠w refl)
mergeDeterministic (Idem h₂) (Id₁ .h₂ .h₂ v≠w) = ⊥-elim (v≠w refl)
mergeDeterministic (Idem h₂) (Id₂ .h₂ .h₂ v≠w) = ⊥-elim (v≠w refl)
mergeDeterministic (Idem h₂) (Idem .h₂) = refl

-- Conflicts are deterministic.
-- If x ⊔ y ↥ c₁ and x ⊔ y ↥ c₂ then c₁ ≡ c₂.
conflictDeterministic : ∀ {as bs cs ds es fs} {u : Val as bs} {v : Val cs ds} {w : Val es fs} 
                          {c₁ c₂ : Conflict u v w} {x : u ~> v} {y : u ~> w} -> 
                          x ⊔ y ↥ c₁ -> x ⊔ y ↥ c₂ -> c₁ ≡ c₂
conflictDeterministic (InsIns x y α≠β) (InsIns .x .y α≠β₁) = refl
conflictDeterministic (UpdUpd x y α≠β α≠γ β≠γ) (UpdUpd .x .y α≠β₁ α≠γ₁ β≠γ₁) = refl
conflictDeterministic (UpdDel x y α≠β) (UpdDel .x .y α≠β₁) = refl
conflictDeterministic (DelUpd x y α≠β) (DelUpd .x .y α≠β₁) = refl

--------------------------------------------------------------------------------
-- Minors proofs about the merge data-types

-- If both transformations perform a change and they are merged then they are all the same transformation.
changeAll-≡ : ∀ {as bs cs ds es fs gs hs} {u : Val as bs} {v : Val cs ds} {w : Val es fs} {z : Val gs hs}
                {f : u ~> v} {g : u ~> w} {h : u ~> z} -> Change f -> Change g -> f ⊔ g ↧ h -> f ≅ g × f ≅ h
changeAll-≡ (IsChange v≠w) q (Id₁ f g v≠w₁) = ⊥-elim (v≠w refl)
changeAll-≡ p (IsChange v≠w) (Id₂ f g v≠w₁) = ⊥-elim (v≠w refl)
changeAll-≡ p q (Idem f) = refl , refl

-- An id transformation can never raise a conflict
⊥-IdConflict : ∀ {as bs cs ds} {v : Val as bs} {w : Val cs ds} 
                  {f : v ~> v} {g : v ~> w} {c : Conflict v v w} -> ¬ (f ⊔ g ↥ c)
⊥-IdConflict (UpdUpd f g α≠β α≠γ β≠γ) = α≠β refl
⊥-IdConflict (UpdDel f g α≠β) = α≠β refl

--------------------------------------------------------------------------------

--------------------------------------------------------------------------------

-- Refifies result of Diff3
data _⇓_ : ∀ {xs ys zs} {e₁ : ES xs ys} {e₂ : ES xs zs} -> e₁ ⋎ e₂ -> ES₃ xs -> Set₁ where
  nil : nil ⇓ []
  merge : ∀ {xs ys zs as bs cs ds es fs gs hs} 
            {e₁ : ES (as ++ xs) (cs ++ ys)} {e₂ : ES (as ++ xs) (es ++ zs)} {e₃ : ES₃ (as ++ xs)} 
            {p : e₁ ⋎ e₂} {u : Val as bs} {v : Val cs ds} {w : Val es fs} {z : Val gs hs} 
            {f : u ~> v} {g : u ~> w} {h : u ~> z} -> 
            (m : f ⊔ g ↧ h) -> p ⇓ e₃ -> (cons f g p) ⇓ (h ∷ e₃)
  conflict : ∀ {xs ys zs as bs cs ds es fs} 
               {e₁ : ES (as ++ xs) (cs ++ ys)} {e₂ : ES (as ++ xs) (es ++ zs)} {e₃ : ES₃ (as ++ xs)}
               {v : Val as bs} {w : Val cs ds} {z : Val es fs} {c : Conflict v w z}
               {f : v ~> w} {g : v ~> z} {p : e₁ ⋎ e₂} -> 
               (u : f ⊔ g ↥ c) -> p ⇓ e₃ -> (cons f g p) ⇓ (c ∷ᶜ e₃)

⇓-sym : ∀ {xs ys zs} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES₃ xs} {p : e₁ ⋎ e₂} 
            -> p ⇓ e₃ -> (⋎-sym p) ⇓ (sym₃ e₃)
⇓-sym nil = nil
⇓-sym (merge m d) = merge (↧-sym m) (⇓-sym d)
⇓-sym (conflict u d) = conflict (↥-sym u) (⇓-sym d)

-- A simple type synonym more readable than ⇓:
-- Diff₃ e₁ e₂ e₃ is more intuitive than p ⇓ e₃
Diff₃ : ∀ {xs ys zs} (e₁ : ES xs ys) (e₂ : ES xs zs) {{p : e₁ ⋎ e₂}} -> ES₃ xs -> Set₁
Diff₃ _ _ {{p}} e₃ = p ⇓ e₃

-- Diff₃ e₁ e₂ e₃ implies that the three editscripts originated from the same source.
Diff₃⟪_⟫ : ∀ {xs ys zs} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES₃ xs} {p : e₁ ⋎ e₂} ->
            Diff₃ e₁ e₂ e₃ -> ⟪ e₁ ⟫ ≡ ⟪ e₃ ⟫₃
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

--------------------------------------------------------------------------------

-- Merged₃ e₁ e₂ e₃ is the proof that e₃ is well-typed edit script
-- obtained succesfully merging e₁ and e₂.
-- The absence of conflicts and the fact that it is well-typed 
-- are implicit in the fact that e₃ is a ES, and not an ES₃
-- as it happens for Diff₃.
data Merged₃ : ∀ {xs ys zs ws} -> ES xs ys -> ES xs zs -> ES xs ws -> Set₁ where  
  nil : Merged₃ [] [] []
  cons : ∀ {xs ys zs ws as bs cs ds es fs gs hs} 
            {e₁ : ES (as ++ xs) (cs ++ ys)} {e₂ : ES (as ++ xs) (es ++ zs)} {e₃ : ES (as ++ xs) (gs ++ ws)} 
            {u : Val as bs} {v : Val cs ds} {w : Val es fs} {z : Val gs hs} 
            {f : u ~> v} {g : u ~> w} {h : u ~> z} -> 
            (m : f ⊔ g ↧ h) -> Merged₃ e₁ e₂ e₃ -> Merged₃ (f ∷ e₁) (g ∷ e₂) (h ∷ e₃)

Merged₃⋎ : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} ->
             Merged₃ e₁ e₂ e₃ -> e₁ ⋎ e₂
Merged₃⋎ nil = nil
Merged₃⋎ (cons m d) = cons _ _ (Merged₃⋎ d)

Merged₃-Diff₃ : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} ->
                  (m : Merged₃ e₁ e₂ e₃) -> Merged₃⋎ m ⇓ ⌞ e₃ ⌟ 
Merged₃-Diff₃ nil = nil
Merged₃-Diff₃ (cons m d) = merge m (Merged₃-Diff₃ d)
