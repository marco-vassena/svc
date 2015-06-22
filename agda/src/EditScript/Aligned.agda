module EditScript.Aligned where

open import EditScript.Core

open import Data.Empty
open import Data.Unit
open import Data.List
open import Relation.Binary.PropositionalEquality

¬Ins : ∀ {xs ys} -> ES xs ys -> Set
¬Ins (Ins x e) = ⊥
¬Ins (Del x e) = ⊤
¬Ins (Upd x y e) = ⊤
¬Ins End = ⊤

-- e₁ ~ e₂ is the proof that e₁ and e₂ are aligned, meaning that they e₁ and e₂ refer to the same
-- original tree. All the Del/Cpy constructors for each are appropriately paired.
data _~_ : ∀ {xs ys zs ws} -> (e₁ : ES xs ys) (e₂ : ES zs ws) -> Set₁ where
  End : End ~ End
  DelDel : ∀ {as xs ys zs a} {e₁ : ES (as ++ xs) ys} {e₂ : ES (as ++ xs) zs} (x : View as a) -> 
           e₁ ~ e₂ -> Del x e₁ ~ Del x e₂
  UpdUpd : ∀ {as bs cs xs ys zs a} (x : View as a) (y : View bs a) (z : View cs a)
           {e₁ : ES (as ++ xs) (bs ++ ys)} {e₂ : ES (as ++ xs) (cs ++ zs)} -> e₁ ~ e₂ -> Upd x y e₁ ~ Upd x z e₂
  DelUpd : ∀ {as bs xs ys zs a} (x : View as a) (y : View bs a) 
           {e₁ : ES (as ++ xs) ys} {e₂ : ES (as ++ xs) (bs ++ zs)} -> e₁ ~ e₂ -> Del x e₁ ~ Upd x y e₂
  UpdDel : ∀ {as bs xs ys zs a} (x : View as a) (y : View bs a) 
           {e₁ : ES (as ++ xs) (bs ++ ys)} {e₂ : ES (as ++ xs) zs} -> e₁ ~ e₂ -> Upd x y e₁ ~ Del x e₂
  InsIns : ∀ {as bs xs ys zs a b} (x : View as a) (y : View bs b) 
           {e₁ : ES xs (as ++ ys)} {e₂ : ES xs (bs ++ zs)} -> e₁ ~ e₂ -> Ins x e₁ ~ Ins y e₂
  Ins₁ : ∀ {as xs ys zs a} {e₁ : ES xs (as ++ ys)} {e₂ : ES xs zs} {{i : ¬Ins e₂}} (x : View as a) -> e₁ ~ e₂ -> Ins x e₁ ~ e₂
  Ins₂ : ∀ {as xs ys zs a} {e₁ : ES xs ys} {e₂ : ES xs (as ++ zs)} {{i : ¬Ins e₁}} (x : View as a) -> e₁ ~ e₂ -> e₁ ~ Ins x e₂

-- The ~ relation is symmetric
~-sym : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES zs ws} -> e₁ ~ e₂ -> e₂ ~ e₁
~-sym End = End
~-sym (DelDel x p) = DelDel x (~-sym p)
~-sym (UpdUpd x y z p) = UpdUpd x z y (~-sym p)
~-sym (DelUpd x y p) = UpdDel x y (~-sym p)
~-sym (UpdDel x y p) = DelUpd x y (~-sym p)
~-sym (InsIns x y p) = InsIns y x (~-sym p)
~-sym (Ins₁ x p) = Ins₂ x (~-sym p)
~-sym (Ins₂ x p) = Ins₁ x (~-sym p)

-- The ~ relation is reflexive
~-refl : ∀ {xs ys} -> (e : ES xs ys) -> e ~ e
~-refl (Ins x e) = InsIns x x (~-refl e)
~-refl (Del x e) = DelDel x (~-refl e)
~-refl (Upd x y e) = UpdUpd x y y (~-refl e)
~-refl End = End

-- Roughly says that ~ means that the scripts refer to the same source object. 
~-⟪⟫ : ∀ {xs ys zs} {e₁ : ES xs ys} {e₂ : ES xs zs} -> e₁ ~ e₂
       -> ⟪ e₁ ⟫ ≡ ⟪ e₂ ⟫
~-⟪⟫ End = refl
~-⟪⟫ (DelDel x p) rewrite ~-⟪⟫ p = refl
~-⟪⟫ (UpdUpd x y z p) rewrite ~-⟪⟫ p = refl
~-⟪⟫ (DelUpd x y p) rewrite ~-⟪⟫ p = refl
~-⟪⟫ (UpdDel x y p) rewrite ~-⟪⟫ p = refl
~-⟪⟫ (InsIns x y p) rewrite ~-⟪⟫ p = refl
~-⟪⟫ (Ins₁ x p) rewrite ~-⟪⟫ p = refl
~-⟪⟫ (Ins₂ x p) rewrite ~-⟪⟫ p = refl

-- What are the sufficient conditions on e₁ and e₂ so that diff3 e₁ e₂ is well-typed?
data _⇊_ : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES zs ws} -> e₁ ~ e₂ -> List Set -> Set₁ where
  End : End ⇊ []
  InsIns : ∀ {xs ys zs ws us a} {e₁ : ES xs (ys ++ zs)} {e₂ : ES xs (ys ++ ws)} {p : e₁ ~ e₂}
           -> (x : View ys a) -> p ⇊ (ys ++ us) -> InsIns x x p ⇊ (a ∷ us)  -- Same x
  UpdUpd : ∀ {xs ys zs ws us ts a} {e₁ : ES (xs ++ zs) (ys ++ ws)} {e₂ : ES (xs ++ zs) (ys ++ us)} {p : e₁ ~ e₂} 
           -> (x : View xs a) (y : View ys a) -> p ⇊ (ys ++ ts) -> UpdUpd x y y p ⇊ (a ∷ ts)
  DelDel : ∀ {xs ys zs ws ts a} {e₁ : ES (xs ++ ys) zs} {e₂ : ES (xs ++ ys) ws} {p : e₁ ~ e₂} 
           -> (x : View xs a) -> p ⇊ ts -> DelDel x p ⇊ ts
  DelCpy : ∀ {xs ys zs us ws a} {e₁ : ES (xs ++ ys) zs} {e₂ : ES (xs ++ ys) (xs ++ ws)} {p : e₁ ~ e₂} 
           -> (x : View xs a) -> p ⇊ us -> DelUpd x x p ⇊ us
  CpyDel : ∀ {xs ys zs us ws a} {e₁ : ES (xs ++ ys) (xs ++ ws)} {e₂ : ES (xs ++ ys) zs} {p : e₁ ~ e₂} 
           -> (x : View xs a) -> p ⇊ us -> UpdDel x x p ⇊ us
  Ins₁ : ∀ {xs ys zs us ws a} {e₁ : ES ys (xs ++ zs)} {e₂ : ES ys us} {p : e₁ ~ e₂} {{i : ¬Ins e₂}}
         -> (x : View xs a) -> p ⇊ (xs ++ ws) -> Ins₁ x p ⇊ (a ∷ ws)
  Ins₂ : ∀ {xs ys zs us ws a} {e₁ : ES ys us} {e₂ : ES ys (xs ++ zs)} {p : e₁ ~ e₂} {{i : ¬Ins e₁}} 
         -> (x : View xs a) -> p ⇊ (xs ++ ws) -> Ins₂ x p ⇊ (a ∷ ws)
