module EditScript.Mapping where

open import EditScript.Core public
open import Data.List
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
import Data.Sum as S

data Val : Set₁ where
  ⊥ : Val
  ⟨_⟩ : ∀ {a as} -> View as a -> Val
  -- This is supposed to be used only with ⊥ ⟨_⟩ 
  [_,_∥_] : ∀ (v w : Val) -> ¬ (v ≡ w) -> Val    
 


⟨_,_∥_⟩ : ∀ {as a bs b} -> (α : View as a) (β : View bs b) -> ¬ (α ⋍ β) -> Val
⟨ α , β ∥ α≠β ⟩ = [ ⟨ α ⟩ , ⟨ β ⟩ ∥ aux α≠β ] 
    where aux : ∀ {as a bs b} {α : View as a} {β : View bs b} -> ¬ (α ⋍ β) -> ¬ ( ⟨ α ⟩ ≡ ⟨ β ⟩ )
          aux p refl = p refl

data _⊢ₑ_~>_  {xs ys} (e : ES xs ys) : Val -> Val -> Set₁ where
  Cpy : ∀ {as a} (α : View as a) -> Cpy α ∈ₑ e -> e ⊢ₑ ⟨ α ⟩ ~> ⟨ α ⟩
  Upd : ∀ {as bs a} (α : View as a) (β : View bs a) -> Upd α β ∈ₑ e -> e ⊢ₑ ⟨ α ⟩ ~> ⟨ β ⟩ 
  Del : ∀ {as a} (α : View as a) -> Del α ∈ₑ e -> e ⊢ₑ ⟨ α ⟩ ~> ⊥
  Ins : ∀ {as a} (α : View as a) -> Ins α ∈ₑ e -> e ⊢ₑ ⊥ ~> ⟨ α ⟩

infixr 3 _⊢ₑ_~>_

--------------------------------------------------------------------------------

-- Convenient way to deal with Edits
-- TODO add conflict constructor
data _~>_ : Val -> Val -> Set where
  Ins : ∀ {as a} -> (α : View as a) -> ⊥ ~> ⟨ α ⟩
  Del : ∀ {as a} -> (α : View as a) -> ⟨ α ⟩ ~> ⊥
  Cpy : ∀ {as a} -> (α : View as a) -> ⟨ α ⟩ ~> ⟨ α ⟩
  Upd : ∀ {as a bs} -> (α : View as a) (β : View bs a) -> ⟨ α ⟩ ~> ⟨ β ⟩
  End : ⊥ ~> ⊥

infixr 3 _~>_

source : ∀ {as bs cs ds} -> Edit as bs cs ds -> Val
source (Ins x) = ⊥
source (Del x) = ⟨ x ⟩
source (Cpy x) = ⟨ x ⟩
source (Upd x y) = ⟨ x ⟩
source End = ⊥

target : ∀ {as bs cs ds} -> Edit as bs cs ds -> Val
target (Ins x) = ⟨ x ⟩
target (Del x) = ⊥
target (Cpy x) = ⟨ x ⟩
target (Upd x y) = ⟨ y ⟩
target End = ⊥

toMap : ∀ {as bs cs ds} -> (c : Edit as bs cs ds) -> source c ~> target c
toMap (Ins x) = Ins x
toMap (Del x) = Del x
toMap (Cpy x) = Cpy x
toMap (Upd x y) = Upd x y
toMap End = End

--------------------------------------------------------------------------------

data Mapping : Set₁ where
  [] : Mapping
  _∷_ : ∀ {v w} -> v ~> w -> Mapping -> Mapping

infixr 3 _∷_

mapping : ∀ {xs ys} -> ES xs ys -> Mapping
mapping (Ins x e) = Ins x ∷ mapping e
mapping (Del x e) = Del x ∷ mapping e
mapping (Cpy x e) = Cpy x ∷ mapping e
mapping (Upd x y e) = Upd x y ∷ mapping e
mapping End = []

open import Data.Unit
import Data.Empty

¬Insᵐ : Mapping -> Set
¬Insᵐ [] = ⊤
¬Insᵐ (Ins α ∷ m) = Data.Empty.⊥
¬Insᵐ (Del α ∷ m) = ⊤
¬Insᵐ (Cpy α ∷ m) = ⊤
¬Insᵐ (Upd α β ∷ m) = ⊤
¬Insᵐ (End ∷ m) = ⊤

--------------------------------------------------------------------------------

-- Edit scripts preserve ⊏ relation.
data _↦_⊏_ {xs ys as a bs b} (e : ES xs ys) (α : View as a) (β : View bs b) : Set₁ where
  Del₁ : e ⊢ₑ ⟨ α ⟩ ~> ⊥ -> e ↦ α ⊏ β
  Del₂ : e ⊢ₑ ⟨ β ⟩ ~> ⊥ -> e ↦ α ⊏ β
  Map₂ : ∀ {cs ds c d} {γ : View cs c} {φ : View ds d} 
             -> e ⊢ₑ ⟨ α ⟩ ~> ⟨ γ ⟩ -> e ⊢ₑ ⟨ β ⟩ ~> ⟨ φ ⟩ -> ⟦ e ⟧ ⊢ γ ⊏ φ -> e ↦ α ⊏ β
 
data Mapˢ {xs ys as a bs cs ds es} (e : ES xs ys) (α : View as a) (c : Edit bs cs ds es) : Set₁ where
  source~> : {{o : output c}} -> e ⊢ₑ ⟨ α ⟩ ~> ⟨ ⌜ c ⌝ ⟩ -> Mapˢ e α c

there~> : ∀ {xs ys as bs cs ds} {v₁ v₂ : Val} (c : Edit as bs cs ds) {e : ES (as ++ xs) (bs ++ ys)}
                -> e ⊢ₑ v₁ ~> v₂ -> c ∻ e ⊢ₑ v₁ ~> v₂
there~> c (Cpy α x) = Cpy α (there c x)
there~> c (Upd α β x) = Upd α β (there c x)
there~> c (Del α x) = Del α (there c x)
there~> c (Ins α x) = Ins α (there c x)

thereMapˢ : ∀ {xs ys as a bs cs ds es fs gs hs is} {e : ES (fs ++ xs) (gs ++ ys)} {α : View as a} {c : Edit bs cs ds es} 
            (d : Edit fs gs hs is) -> Mapˢ e α c -> Mapˢ (d ∻ e) α c
thereMapˢ d (source~> x) = source~> (there~> d x)

--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- These functions convert an edit that belongs to an edit script, 
-- e ⊢ₑ_~>_ statement.

-- If the edit script has an input then, that value is either deleted, or there
-- is a value to which it is mapped.
∈⟨⟩~> : ∀ {xs ys as bs cs ds} {e : ES xs ys} {d : Edit as bs cs ds} 
         {{i : input d }} 
         -> d ∈ₑ e -> (e ⊢ₑ ⟨ ⌞ d ⌟ ⟩ ~> ⊥) ⊎ (Mapˢ e ⌞ d ⌟ d)
∈⟨⟩~> {{i = ()}} (here (Ins x))
∈⟨⟩~> (here (Del x)) = inj₁ (Del x (here (Del x)))
∈⟨⟩~> (here (Cpy x)) = inj₂ (source~> (Cpy x (here (Cpy x))))
∈⟨⟩~> (here (Upd x y)) = inj₂ (source~> (Upd x y (here (Upd x y))))
∈⟨⟩~> {{i = ()}} (here End)
∈⟨⟩~> (there d p) = S.map (there~> d) (thereMapˢ d) (∈⟨⟩~> p)

--------------------------------------------------------------------------------
-- The symmetric theorem

data _↤_⊏_ {xs ys as a bs b} (e : ES xs ys) (α : View as a) (β : View bs b) : Set₁ where
  Ins₁ : e ⊢ₑ ⊥ ~> ⟨ α ⟩ -> e ↤ α ⊏ β
  Ins₂ : e ⊢ₑ ⊥ ~> ⟨ β ⟩ -> e ↤ α ⊏ β
  Map₂ : ∀ {cs ds c d} {γ : View cs c} {φ : View ds d} 
             -> e ⊢ₑ ⟨ γ ⟩ ~> ⟨ α ⟩ -> e ⊢ₑ ⟨ φ ⟩ ~> ⟨ β ⟩ -> ⟪ e ⟫ ⊢ γ ⊏ φ -> e ↤ α ⊏ β

data Mapₒ {xs ys as a bs cs ds es} (e : ES xs ys) (α : View as a) (c : Edit bs cs ds es) : Set₁ where
  target~> : {{o : input c}} -> e ⊢ₑ ⟨ ⌞ c ⌟ ⟩ ~> ⟨ α ⟩ -> Mapₒ e α c

thereMapₒ : ∀ {xs ys as a bs cs ds es fs gs hs is} {e : ES (fs ++ xs) (gs ++ ys)} {α : View as a} {c : Edit bs cs ds es} 
            (d : Edit fs gs hs is) -> Mapₒ e α c -> Mapₒ (d ∻ e) α c
thereMapₒ d (target~> x) = target~> (there~> d x)

-- If the edit script has an output then, that value is either inserted or there
-- is a value from which it was generated.
∈~>⟨⟩ : ∀ {xs ys as bs cs ds} {e : ES xs ys} {d : Edit as bs cs ds} {{o : output d }} 
         -> d ∈ₑ e -> (e ⊢ₑ ⊥ ~> ⟨ ⌜ d ⌝ ⟩) ⊎ (Mapₒ e ⌜ d ⌝ d)
∈~>⟨⟩ (here (Ins x)) = inj₁ (Ins x (here (Ins x)))
∈~>⟨⟩ {{o = ()}} (here (Del x))
∈~>⟨⟩ (here (Cpy x)) = inj₂ (target~> (Cpy x (here (Cpy x))))
∈~>⟨⟩ (here (Upd x y)) = inj₂ (target~> (Upd x y (here (Upd x y))))
∈~>⟨⟩ {{o = ()}} (here End)
∈~>⟨⟩ (there d p) = S.map (there~> d) (thereMapₒ d) (∈~>⟨⟩ p)

--------------------------------------------------------------------------------

import Data.Empty
open import Data.Unit

data _~ᵐ_ : Mapping -> Mapping -> Set where
  cons : ∀ {xs ys a b c} (x : a ~> b) (y : a ~> c) -> xs ~ᵐ ys -> (x ∷ xs) ~ᵐ (y ∷ ys)
  ins₁ : ∀ {xs ys b} {{i : ¬Insᵐ ys}} (x : ⊥ ~> b) -> xs ~ᵐ ys -> x ∷ xs ~ᵐ ys
  ins₂ : ∀ {xs ys c} {{i : ¬Insᵐ xs}} (y : ⊥ ~> c) -> xs ~ᵐ ys -> xs ~ᵐ y ∷ ys
  nil : [] ~ᵐ []

infixl 3 _~ᵐ_
