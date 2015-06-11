-- This module explicits the mapping between nodes induced by an edit script

module Mapping where

open import Diff
open import View
open import Data.List
open import Data.Unit
open import Relation.Binary.PropositionalEquality hiding ([_])

data Val : Set₁ where
  ⊥ : Val
  ⟨_⟩ : ∀ {a as} -> View as a -> Val

args : Val -> List Set
args ⊥ = []
args (⟨_⟩ {as = as} x) = as

ty : Val -> List Set
ty ⊥ = []
ty (⟨_⟩ {a = a} x) = [ a ]

data _⊢ₑ_~>_  {xs ys} (e : ES xs ys) : Val -> Val -> Set₁ where
  Cpy : ∀ {as a} (α : View as a) -> Cpy α ∈ₑ e -> e ⊢ₑ ⟨ α ⟩ ~> ⟨ α ⟩
  Upd : ∀ {as bs a} (α : View as a) (β : View bs a) -> Upd α β ∈ₑ e -> e ⊢ₑ ⟨ α ⟩ ~> ⟨ β ⟩ 
  Del : ∀ {as a} (α : View as a) -> Del α ∈ₑ e -> e ⊢ₑ ⟨ α ⟩ ~> ⊥
  Ins : ∀ {as a} (α : View as a) -> Ins α ∈ₑ e -> e ⊢ₑ ⊥ ~> ⟨ α ⟩

infixr 3 _⊢ₑ_~>_

edit : ∀ {xs ys} {x y : Val} {e : ES xs ys} -> e ⊢ₑ x ~> y -> Edit (args x) (args y) (ty x) (ty y)
edit (Cpy α x) = Cpy α
edit (Upd α β x) = Upd α β
edit (Del α x) = Del α
edit (Ins α x) = Ins α

edit-input : ∀ {xs ys as a v} {e : ES xs ys} {α : View as a} -> (p : e ⊢ₑ ⟨ α ⟩ ~> v) -> input (edit p)
edit-input (Cpy α x) = tt
edit-input (Upd α β x) = tt
edit-input (Del α x) = tt

edit-output : ∀ {xs ys as a v} {e : ES xs ys} {α : View as a} -> (p : e ⊢ₑ v ~> ⟨ α ⟩) -> output (edit p)
edit-output (Cpy α x) = tt
edit-output (Upd α β x) = tt
edit-output (Ins α x) = tt

-- get-∈ : ∀ {xs ys} {x y : Val} {e : ES xs ys} -> (p : e ⊢ₑ x ~> y) -> edit p ∈ₑ e
-- get-∈ (Cpy α x) = x
-- get-∈ (Upd α β x) = x
-- get-∈ (Del α x) = x
-- get-∈ (Ins α x) = x

--------------------------------------------------------------------------------

-- TODO this part actually belongs to Embedding ... here to avoid recompiling all the other proofs
open import Embedding
open import Diff3
open import DTree
open import Data.Product
open import Data.List

open import Data.Nat

label : ∀ {xs as a} {α : View as a} {d : DList xs} -> α ∈ d -> ℕ
label (∈-here α) = 0
label (∈-there p) = suc (label p)

open import Function
open import Data.Sum
open import Data.Empty hiding (⊥)
open import Safety

-- TODO better name
data Map₂ {xs ys as a bs b} (e : ES xs ys) (α : View as a) (β : View bs b) : Set₁ where
  M₂ : ∀ {cs ds c d} {γ : View cs c} {φ : View ds d} 
      -> e ⊢ₑ ⟨ α ⟩ ~> ⟨ γ ⟩ -> e ⊢ₑ ⟨ β ⟩ ~> ⟨ φ ⟩ -> ⟦ e ⟧ ⊢ γ ⊏ φ -> Map₂ e α β
 
-- > Try to add both c and α in the paramteres/indexes
-- It seems to forget that output c ≡ output (edit f)
data Map₁ {xs ys as a bs cs ds es} (e : ES xs ys) (α : View as a) (c : Edit bs cs ds es): Set₁ where
  M₁ : ∀ {i : input c} {o : output c} -> e ⊢ₑ ⟨ α ⟩ ~> ⟨ ⌞ c ⌟ ⟩ -> Map₁ e α c

aux : ∀ {xs ys as bs cs ds} {v₁ v₂ : Val} (c : Edit as bs cs ds) {e : ES (as ++ xs) (bs ++ ys)}-> e ⊢ₑ v₁ ~> v₂ -> c ∻ e ⊢ₑ v₁ ~> v₂
aux c (Cpy α x) = Cpy α (there c x)
aux c (Upd α β x) = Upd α β (there c x)
aux c (Del α x) = Del α (there c x)
aux c (Ins α x) = Ins α (there c x)

aux₂ : ∀ {xs ys as a bs cs ds es fs gs hs is} {e : ES (fs ++ xs) (gs ++ ys)} {α : View as a} {c : Edit bs cs ds es} 
         (d : Edit fs gs hs is) -> Map₁ e α c -> Map₁ (d ∻ e) α c
aux₂ d (M₁ {i = i} {o = o} x) = M₁ {i = i} {o = o} (aux d x)

map₁ : ∀ {xs ys as bs cs ds es fs gs hs} {e : ES xs ys} {c : Edit as bs cs ds} {d : Edit es fs gs hs} {{ i : input c }} 
         -> e ⊢ₑ c ⊏ d -> e ⊢ₑ ⟨ ⌜ c ⌝ ⟩ ~> ⊥ ⊎ Map₁ e ⌜ c ⌝ c
map₁ {{i = ()}} (here (Ins x) o)
map₁ (here (Del x) o) = inj₁ (Del x (here (Del x)))
map₁ (here (Cpy x) o) = inj₂ (M₁ (Cpy x (here (Cpy x))))
map₁ (here (Upd x y) o) = inj₂ (M₁ (Upd x y (here (Upd x y))))
map₁ {{i = ()}} (here End o)
map₁ (there a p) = Data.Sum.map (aux a) (aux₂ a) (map₁ p)

map₃ : ∀ {xs ys as bs cs ds} {e : ES xs ys} {d : Edit as bs cs ds} 
         {{i : input d }} 
         -> d ∈ₑ e -> e ⊢ₑ ⟨ ⌜ d ⌝ ⟩ ~> ⊥ ⊎ Map₁ e ⌜ d ⌝ d
map₃ {{i = ()}} (here (Ins x))
map₃ (here (Del x)) = inj₁ (Del x (here (Del x)))
map₃ (here (Cpy x)) = inj₂ (M₁ (Cpy x (here (Cpy x))))
map₃ (here (Upd x y)) = inj₂ (M₁ (Upd x y (here (Upd x y))))
map₃ {{i = ()}} (here End)
map₃ (there d p) = Data.Sum.map (aux d) (aux₂ d) (map₃ p)

map₂ : ∀ {xs ys as bs cs ds es fs gs hs} {e : ES xs ys} {c : Edit as bs cs ds} {d : Edit es fs gs hs} 
         {{ i₂ : input d }} 
         -> e ⊢ₑ c ⊏ d -> e ⊢ₑ ⟨ ⌜ d ⌝ ⟩ ~> ⊥ ⊎ Map₁ e ⌜ d ⌝ d
map₂ (here c o) = Data.Sum.map (aux c) (aux₂ c) (map₃ o)
map₂ (there c p) = Data.Sum.map (aux c) (aux₂ c) (map₂ p)

lemma₁ : ∀ {xs ys as bs cs ds es fs gs hs} {e : ES xs ys} {c : Edit as bs cs ds} {d : Edit es fs gs hs}
           {{i₁ : input c}} {{o₁ : output c}} {{i₂ : input d}} {{o₂ : output d}}
           {α : View (inputArgs c) (inputTy c)} {β : View (inputArgs d) (inputTy d)} 
           {γ : View (outputArgs c) (outputTy c)} {φ : View (outputArgs d) (outputTy d)}
           -> ⌜ c ⌝ ≡ α ->  ⌞ c ⌟ ≡ γ -> ⌜ d ⌝ ≡ β -> ⌞ d ⌟ ≡ φ -> e ⊢ₑ c ⊏ d -> ⟦ e ⟧ ⊢ γ ⊏ φ           
lemma₁ {c = c} refl refl refl refl r = ⟦⟧-⊏ c r

lemma : ∀ {as bs xs ys a} {α : View as a} {β : View bs a} {e : ES xs ys} -> (p : e ⊢ₑ ⟨ α ⟩ ~> ⟨ β ⟩) 
          {o : output (edit p)} {i : input (edit p)} -> outputTy (edit p) ≡ inputTy (edit p)
lemma (Cpy α x) = refl
lemma (Upd α β x) = refl

eqTy-edit : ∀ {as bs cs ds} (c : Edit as bs cs ds) {{i : input c}} {{o : output c}} -> inputTy c ≡ outputTy c
eqTy-edit (Ins x) {{()}}
eqTy-edit (Del x) {{tt}} {{()}}
eqTy-edit (Cpy x) = refl
eqTy-edit (Upd x y) = refl
eqTy-edit End {{()}}

outputMap₁ : ∀ {xs ys as bs cs ds ls l} {e : ES xs ys} {c : Edit as bs cs ds} {α : View ls l}
             -> Map₁ e α c -> output c
outputMap₁ (M₁ {o = o} x) = o

preserve-lemma : ∀ {xs ys as bs cs ds es fs gs hs} {e : ES xs ys} (c : Edit as bs cs ds) (d : Edit es fs gs hs)
                   {{i₁ : input c}} {{i₂ : input d}} {{o₁ : output c}} {{o₂ : output d}}
                   {α : View (inputArgs c) (inputTy c)} {β : View (inputArgs d) (inputTy d)} -> α ≡ ⌜ c ⌝ -> β ≡ ⌜ d ⌝ 
                   -> Map₁ e α c -> Map₁ e β d
                   -> e ⊢ₑ c ⊏ d -> Map₂ e α β
preserve-lemma c d {{o₁ = o₁}} {{o₂ = o₂}} refl refl (M₁ f) (M₁ g) p 
  = M₂ {γ = ⌞_⌟ c {{o₁}}} {φ = ⌞_⌟ d {{o₂}}} f g (⟦⟧-⊏ {d = d} c {{o₁}} {{o₂}} p)

-- Final lemma
preserve-⊏ : ∀ {xs ys as bs a b} {e : ES xs ys}  
              {α : View as a} {β : View bs b} -- {γ : View cs a} {φ : View ds b } ->
              (p : ⟪ e ⟫ ⊢ α ⊏ β) -> (e ⊢ₑ ⟨ α ⟩ ~> ⊥) ⊎ (e ⊢ₑ ⟨ β ⟩ ~> ⊥) ⊎ (Map₂ e α β) 
preserve-⊏ {e = e} p with diff-⊏ˢ p (mkDiff e)
preserve-⊏ p | source-⊏ {c = c} x  with map₁ {c = c} x
preserve-⊏ p | source-⊏ {c = c} x | inj₁ a = inj₁ a -- inj₁ (Del {!⌜ c ⌝!} {!!})
preserve-⊏ p | source-⊏ {c = c} {d = d} x | inj₂ m with map₂ {c = c} {d = d} x
preserve-⊏ p | source-⊏ x | inj₂ m | inj₁ b = inj₂ (inj₁ b)
preserve-⊏ p | source-⊏ {c = c} {d = d} {i₁ = i₁} {i₂ = i₂}  x | inj₂ m | inj₂ n 
  = inj₂ (inj₂ (preserve-lemma c d {{i₁ = i₁}} {{i₂ = i₂}} {{o₁ = outputMap₁ m}} {{o₂ = outputMap₁ n}} refl refl m n x))
