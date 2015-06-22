module EditScript2.Core where

open import Data.List
open import Data.Product
open import Data.DTree public hiding ([_])

data Val : List Set -> List Set -> Set₁ where
  ⊥ : Val [] []
  ⟨_⟩ : ∀ {as a} (α : View as a) -> Val as [ a ] 

data _~>_ : ∀ {as bs cs ds} -> Val as bs -> Val cs ds -> Set where
  Ins : ∀ {as a} (α : View as a) -> ⊥ ~> ⟨ α ⟩
  Del : ∀ {as a} (α : View as a) -> ⟨ α ⟩ ~> ⊥
  Upd : ∀ {as bs a} (α : View as a) (β : View bs a) -> ⟨ α ⟩ ~> ⟨ β ⟩
  Nop : ⊥ ~> ⊥

data ES : List Set -> List Set -> Set₁ where
  _∷_ : ∀ {xs ys as bs cs ds} {v : Val as bs} {w : Val cs ds} -> 
          (x : v ~> w) -> (e : ES (as ++ xs) (cs ++ ys)) -> ES (bs ++ xs) (ds ++ ys)
  [] : ES [] []
  
--------------------------------------------------------------------------------

⟦_⟧ : ∀ {xs ys} -> ES xs ys -> DList ys
⟦ Ins α ∷ e ⟧ with dsplit ⟦ e ⟧
... | ds₁ , ds₂ = Node α ds₁ ∷ ds₂
⟦ Del α ∷ e ⟧ = ⟦ e ⟧
⟦ Upd α β ∷ e ⟧ with dsplit ⟦ e ⟧
... | ds₁ , ds₂ = Node β ds₁ ∷ ds₂
⟦ Nop ∷ e ⟧ = ⟦ e ⟧
⟦ [] ⟧ = []

⟪_⟫ : ∀ {xs ys} -> ES xs ys -> DList xs
⟪ Ins α ∷ e ⟫ = ⟪ e ⟫
⟪ Del α ∷ e ⟫ with dsplit ⟪ e ⟫
... | ds₁ , ds₂ = Node α ds₁ ∷ ds₂
⟪ Upd α β ∷ e ⟫ with dsplit ⟪ e ⟫
... | ds₁ , ds₂ = Node α ds₁ ∷ ds₂
⟪ Nop ∷ e ⟫ = ⟪ e ⟫
⟪ [] ⟫ = []

--------------------------------------------------------------------------------

open import Relation.Nullary
open import Data.Unit
import Data.Empty as E

-- Does the transformation perform a change?
change : ∀ {as bs cs ds} {v : Val as bs} {w : Val cs ds} -> v ~> w -> Set
change (Ins α) = ⊤
change (Del α) = ⊤
change (Upd α β) with α =?= β
change (Upd α .α) | yes refl = E.⊥
change (Upd α β) | no ¬p = ⊤
change Nop = E.⊥


--------------------------------------------------------------------------------
-- Membership

data _∈ₑ_ : ∀ {as bs cs ds xs ys} {v : Val as bs} {w : Val cs ds} -> v ~> w -> ES xs ys -> Set₁ where
  here : ∀ {as bs cs ds xs ys} {v : Val as bs} {w : Val cs ds} {e : ES (as ++ xs) (cs ++ ys)} -> (c : v ~> w) -> c ∈ₑ c ∷ e
  there : ∀ {as bs cs ds es fs gs hs xs ys} {u : Val as bs} {v : Val cs ds} {w : Val es fs} {z : Val gs hs} {c : u ~> v} 
            {e : ES (es ++ xs) (gs ++ ys)} (d : w ~> z) -> c ∈ₑ e -> c ∈ₑ d ∷ e

infixl 3 _∈ₑ_

--------------------------------------------------------------------------------

-- Comes-before relation for edit scripts

data _⊢ₑ_⊏_ : ∀ {xs ys as bs cs ds es fs gs hs} {u : Val as cs} {v : Val bs ds} {w : Val es gs} {z : Val fs hs} -> 
                ES xs ys -> u ~> v -> w ~> z -> Set₁ where
  here : ∀ {as bs cs ds es fs gs hs xs ys} {u : Val es fs} {v : Val gs hs} {d : u ~> v} 
           {w : Val as bs} {z : Val cs ds} {e : ES (as ++ xs) (cs ++ ys)} 
           (c : w ~> z) -> (o : d ∈ₑ e) -> c ∷ e ⊢ₑ c ⊏ d 
  there : ∀ {as bs cs ds es fs gs hs is ls ms ns xs ys} {u : Val es fs} {v : Val gs hs} {d : u ~> v} {w : Val as bs} 
          {z : Val cs ds} {c : w ~> z} {e : ES (is ++ xs) (ms ++ ys)} {s : Val is ls} {t : Val ms ns} -> (a : s ~> t)
          (o : e ⊢ₑ c ⊏ d) -> a ∷ e ⊢ₑ c ⊏ d 

infixl 3 _⊢ₑ_⊏_

⊏ₑ-∈₁ : ∀ {xs ys as bs cs ds es fs gs hs} {e : ES xs ys} 
          {u : Val as cs} {v : Val bs ds} {w : Val es gs} {z : Val fs hs}
          {d : w ~> z} {c : u ~> v} -> e ⊢ₑ c ⊏ d -> c ∈ₑ e
⊏ₑ-∈₁ (here c o) = here c
⊏ₑ-∈₁ (there e p) = there e (⊏ₑ-∈₁ p)

⊏ₑ-∈₂ : ∀ {xs ys as bs cs ds es fs gs hs} {e : ES xs ys} 
          {u : Val as cs} {v : Val bs ds} {w : Val es gs} {z : Val fs hs}
          {d : w ~> z} {c : u ~> v} -> e ⊢ₑ c ⊏ d -> d ∈ₑ e
⊏ₑ-∈₂ (here c o) = there c o
⊏ₑ-∈₂ (there e p) = there e (⊏ₑ-∈₂ p)

--------------------------------------------------------------------------------

∈-here-⟪⟫ : ∀ {a as bs cs xs ys} {α : View as a} {v : Val bs cs} {e : ES (as ++ xs) (bs ++ ys)} (c : ⟨ α ⟩ ~> v) -> α ∈ ⟪ c ∷ e ⟫
∈-here-⟪⟫ (Del α) = ∈-here α
∈-here-⟪⟫ (Upd α β) = ∈-here α

∈-there-⟪⟫ :  ∀ {as bs cs ds ms m xs ys} {v : Val as bs} {w : Val cs ds} {e : ES (as ++ xs) (cs ++ ys)} {α : View ms m} -> 
               (d : v ~> w) -> α ∈ ⟪ e ⟫ -> α ∈ ⟪ d ∷ e ⟫
∈-there-⟪⟫ (Ins α) p = p
∈-there-⟪⟫ (Del α) p = ∈-there (∈-dsplit _ p)
∈-there-⟪⟫ (Upd α β) p = ∈-there (∈-dsplit _ p)
∈-there-⟪⟫ Nop p = p

--------------------------------------------------------------------------------

∈-there-⟦⟧ :  ∀ {as bs cs ds ms m xs ys} {v : Val as bs} {w : Val cs ds} {e : ES (as ++ xs) (cs ++ ys)} {α : View ms m} -> 
               (d : v ~> w) -> α ∈ ⟦ e ⟧ -> α ∈ ⟦ d ∷ e ⟧
∈-there-⟦⟧ (Ins α) p = ∈-there (∈-dsplit _ p)
∈-there-⟦⟧ (Del α) p = p
∈-there-⟦⟧ (Upd α β) p = ∈-there (∈-dsplit _ p)
∈-there-⟦⟧ Nop p = p

∈-here-⟦⟧ : ∀ {a as bs cs xs ys} {α : View cs a} {v : Val as bs} {e : ES (as ++ xs) (cs ++ ys)} (c : v ~> ⟨ α ⟩) -> α ∈ ⟦ c ∷ e ⟧
∈-here-⟦⟧ (Ins α) = ∈-here α
∈-here-⟦⟧ (Upd α β) = ∈-here β

--------------------------------------------------------------------------------
