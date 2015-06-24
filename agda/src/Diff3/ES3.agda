module Diff3.ES3 where

open import Diff.Core public
open import EditScript.Core public
open import EditScript.Aligned public
open import EditScript.Mapping

open import Data.List
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product hiding (swap)

--------------------------------------------------------------------------------

-- Technical remark
-- Note that we do not want to store inequalities here, otherwise proving that c₁ ≡ c₂
-- would require extensionality. 
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

data ES₃ : List Set -> Set₁ where
  [] : ES₃ []
  _∷_ : ∀ {as bs cs ds xs} {v : Val as bs} {w : Val cs ds} -> v ~> w -> ES₃ (as ++ xs) -> ES₃ (bs ++ xs)
  _∷ᶜ_ : ∀ {as bs cs ds es fs xs} {u : Val as bs} {v : Val cs ds} {w : Val es fs} -> 
           (c : Conflict u v w) -> ES₃ (as ++ xs) -> ES₃ (bs ++ xs)

sym₃ : ∀ {xs} -> ES₃ xs -> ES₃ xs
sym₃ [] = []
sym₃ (x ∷ e) = x ∷ sym₃ e
sym₃ (c ∷ᶜ e) = swap c ∷ᶜ sym₃ e

⟪_⟫₃ : ∀ {xs} -> ES₃ xs -> DList xs
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
-- Membership in ES₃

-- The proof that a conflict is present in ES₃
data _∈ᶜ_ {as bs cs ds es fs } {u : Val as bs} {v : Val cs ds} {w : Val es fs} 
          : ∀ {xs} -> Conflict u v w -> ES₃ xs -> Set₁ where
  here : ∀ {xs} {e : ES₃ (as ++ xs)} (c : Conflict u v w) -> c ∈ᶜ (c ∷ᶜ e)
  there : ∀ {as' bs' cs' ds' xs} {u' : Val as' bs'} {v' : Val cs' ds'} {c : Conflict u v w} 
              {e : ES₃ (as' ++ xs)} (x : u' ~> v' ) -> c ∈ᶜ e -> c ∈ᶜ x ∷ e
  thereᶜ : ∀ {as' bs' cs' ds' es' fs' xs} {u' : Val as' bs'} {v' : Val cs' ds'} {w' : Val es' fs'} {c : Conflict u v w} 
             {e : ES₃ (as' ++ xs)} (c' : Conflict u' v' w') -> c ∈ᶜ e -> c ∈ᶜ (c' ∷ᶜ e)

infixr 3 _∈ᶜ_ 

-- The proof that a transformation is present in ES₃
data _∈₃_ {as bs cs ds} {u : Val as bs} {v : Val cs ds} : ∀ {xs} -> u ~> v -> ES₃ xs -> Set₁ where
  here : ∀ {xs} {e : ES₃ (as ++ xs)} (f : u ~> v) -> f ∈₃ (f ∷ e)
  there : ∀ {as' bs' cs' ds' xs} {u' : Val as' bs'} {v' : Val cs' ds'} {f : u ~> v} 
              {e : ES₃ (as' ++ xs)} (g : u' ~> v') -> f ∈₃ e -> f ∈₃ g ∷ e
  thereᶜ : ∀ {as' bs' cs' ds' es' fs' xs} {u' : Val as' bs'} {v' : Val cs' ds'} {w' : Val es' fs'} 
             {e : ES₃ (as' ++ xs)} {f : u ~> v} (c : Conflict u' v' w') -> f ∈₃ e -> f ∈₃ (c ∷ᶜ e)

infixr 3 _∈₃_

--------------------------------------------------------------------------------

-- The proof that an ES₃ does not contain any conflict
data NoCnf : ∀ {xs} -> ES₃ xs -> Set where
  [] : NoCnf []
  _∷_ : ∀ {as bs cs ds xs} {v : Val as bs} {w : Val cs ds} {e : ES₃ (as ++ xs)} 
          (f : v ~> w) -> NoCnf e -> NoCnf (f ∷ e)

-- NoCnf is preserved by sym₃
NoCnf-sym : ∀ {xs} {e : ES₃ xs} -> NoCnf e -> NoCnf (sym₃ e)
NoCnf-sym [] = []
NoCnf-sym (f ∷ p) = f ∷ (NoCnf-sym p)

-- When no conflict occurs an ES₃ corresponds to its symmetric
NoCnf-≡ : ∀ {xs} {e : ES₃ xs} -> NoCnf e -> e ≡ sym₃ e
NoCnf-≡ [] = refl
NoCnf-≡ (f ∷ p) = cong (_∷_ f) (NoCnf-≡ p)

-- NoCnf and ∈ᶜ are contradictory.
⊥-NoCnf : ∀ {xs as bs cs ds es fs} {e : ES₃ xs} {u : Val as bs} {v : Val cs ds} {w : Val es fs}
                 {c : Conflict u v w} -> NoCnf e -> ¬ (c ∈ᶜ e)
⊥-NoCnf () (here c)
⊥-NoCnf (x ∷ p) (there .x q) = ⊥-NoCnf p q
⊥-NoCnf () (thereᶜ c' q)
