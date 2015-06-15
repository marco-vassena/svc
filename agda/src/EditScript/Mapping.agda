module EditScript.Mapping where

open import EditScript.Core public
open import Data.List
open import Data.Sum
import Data.Sum as S

data Val : Set₁ where
  ⊥ : Val
  ⟨_⟩ : ∀ {a as} -> View as a -> Val

data _⊢ₑ_~>_  {xs ys} (e : ES xs ys) : Val -> Val -> Set₁ where
  Cpy : ∀ {as a} (α : View as a) -> Cpy α ∈ₑ e -> e ⊢ₑ ⟨ α ⟩ ~> ⟨ α ⟩
  Upd : ∀ {as bs a} (α : View as a) (β : View bs a) -> Upd α β ∈ₑ e -> e ⊢ₑ ⟨ α ⟩ ~> ⟨ β ⟩ 
  Del : ∀ {as a} (α : View as a) -> Del α ∈ₑ e -> e ⊢ₑ ⟨ α ⟩ ~> ⊥
  Ins : ∀ {as a} (α : View as a) -> Ins α ∈ₑ e -> e ⊢ₑ ⊥ ~> ⟨ α ⟩

infixr 3 _⊢ₑ_~>_

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
