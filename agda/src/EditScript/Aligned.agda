module EditScript.Aligned where

open import EditScript.Core

open import Data.Empty
open import Data.Unit
open import Data.List
open import Relation.Binary.PropositionalEquality

-- e₁ ~ e₂ is the proof that e₁ and e₂ are aligned, meaning that they e₁ and e₂ refer to the same
-- original tree. All the Del/Cpy constructors for each are appropriately paired.
data _⋎_ : ∀ {xs ys zs ws} -> (e₁ : ES xs ys) (e₂ : ES zs ws) -> Set₁ where
  nil : [] ⋎ []
  cons : ∀ {as bs cs ds es fs xs ys zs} {v : Val as bs} {w : Val cs ds} {z : Val es fs}
           {e₁ : ES (as ++ xs) (cs ++ ys)} {e₂ : ES (as ++ xs) (es ++ zs)} 
           (x : v ~> w) (y : v ~> z) -> e₁ ⋎ e₂ -> x ∷ e₁ ⋎ y ∷ e₂ 
          
infixr 3 _⋎_

-- The ~ relation is symmetric
⋎-sym : ∀ {xs ys zs} {e₁ : ES xs ys} {e₂ : ES xs zs} -> e₁ ⋎ e₂ -> e₂ ⋎ e₁
⋎-sym nil = nil
⋎-sym (cons x y p) = cons y x (⋎-sym p)

-- The ⋎ relation is reflexive
⋎-refl : ∀ {xs ys} -> (e : ES xs ys) -> e ⋎ e
⋎-refl (x ∷ e) = cons x x (⋎-refl e)
⋎-refl [] = nil

-- Roughly says that ⋎ means that the scripts refer to the same source object. 
⋎-⟪⟫ : ∀ {xs ys zs} {e₁ : ES xs ys} {e₂ : ES xs zs} -> e₁ ⋎ e₂
       -> ⟪ e₁ ⟫ ≡ ⟪ e₂ ⟫
⋎-⟪⟫ nil = refl
⋎-⟪⟫ (cons (Ins α) (Ins β) p) = ⋎-⟪⟫ p
⋎-⟪⟫ (cons (Ins α) Nop p) = ⋎-⟪⟫ p
⋎-⟪⟫ (cons (Del α) (Del .α) p) rewrite ⋎-⟪⟫ p = refl
⋎-⟪⟫ (cons (Del α) (Upd .α β) p) rewrite ⋎-⟪⟫ p = refl
⋎-⟪⟫ (cons (Upd α β) (Del .α) p) rewrite ⋎-⟪⟫ p = refl
⋎-⟪⟫ (cons (Upd α β) (Upd .α γ) p) rewrite ⋎-⟪⟫ p = refl
⋎-⟪⟫ (cons Nop (Ins α) p) = ⋎-⟪⟫ p
⋎-⟪⟫ (cons Nop Nop p) = ⋎-⟪⟫ p

-- What are the sufficient conditions on e₁ and e₂ so that diff3 e₁ e₂ is well-typed?
-- I think now we can just have one ↓ relation.
-- data _⇊_ : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES zs ws} -> e₁ ⋎ e₂ -> List Set -> Set₁ where
--   nil : nil ⇊ []
--   cons : ∀ {xs ys zs ws ts} {e₁ : ES xs (ys ++ zs)} {e₂ : ES xs (ys ++ ws)} {p : e₁ ⋎ e₂} ->
--            p ⇊ (ys ++ ts) -> cons (Ins {!!}) {!Ins!} p ⇊ {!!}

  -- InsIns : ∀ {xs ys zs ws us a} {e₁ : ES xs (ys ++ zs)} {e₂ : ES xs (ys ++ ws)} {p : e₁ ⋎ e₂}
  --          -> (x : View ys a) -> p ⇊ (ys ++ us) -> InsIns x x p ⇊ (a ∷ us)  -- Same x
  -- UpdUpd : ∀ {xs ys zs ws us ts a} {e₁ : ES (xs ++ zs) (ys ++ ws)} {e₂ : ES (xs ++ zs) (ys ++ us)} {p : e₁ ⋎ e₂} 
  --          -> (x : View xs a) (y : View ys a) -> p ⇊ (ys ++ ts) -> UpdUpd x y y p ⇊ (a ∷ ts)
  -- DelDel : ∀ {xs ys zs ws ts a} {e₁ : ES (xs ++ ys) zs} {e₂ : ES (xs ++ ys) ws} {p : e₁ ⋎ e₂} 
  --          -> (x : View xs a) -> p ⇊ ts -> DelDel x p ⇊ ts
  -- DelCpy : ∀ {xs ys zs us ws a} {e₁ : ES (xs ++ ys) zs} {e₂ : ES (xs ++ ys) (xs ++ ws)} {p : e₁ ⋎ e₂} 
  --          -> (x : View xs a) -> p ⇊ us -> DelUpd x x p ⇊ us
  -- CpyDel : ∀ {xs ys zs us ws a} {e₁ : ES (xs ++ ys) (xs ++ ws)} {e₂ : ES (xs ++ ys) zs} {p : e₁ ⋎ e₂} 
  --          -> (x : View xs a) -> p ⇊ us -> UpdDel x x p ⇊ us
  -- Ins₁ : ∀ {xs ys zs us ws a} {e₁ : ES ys (xs ++ zs)} {e₂ : ES ys us} {p : e₁ ⋎ e₂} {{i : ¬Ins e₂}}
  --        -> (x : View xs a) -> p ⇊ (xs ++ ws) -> Ins₁ x p ⇊ (a ∷ ws)
  -- Ins₂ : ∀ {xs ys zs us ws a} {e₁ : ES ys us} {e₂ : ES ys (xs ++ zs)} {p : e₁ ⋎ e₂} {{i : ¬Ins e₁}} 
  --        -> (x : View xs a) -> p ⇊ (xs ++ ws) -> Ins₂ x p ⇊ (a ∷ ws)

