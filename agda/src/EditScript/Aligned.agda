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

--------------------------------------------------------------------------------

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

