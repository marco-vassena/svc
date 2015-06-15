module Diff.Safety where

open import Diff.Core public
open import EditScript.Safety
open import Data.DTree
open import Lemmas

open import Function
open import Data.Empty
open import Data.Product
open import Data.List
open import Relation.Binary
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality hiding ([_])

--------------------------------------------------------------------------------
-- Safety properties
--------------------------------------------------------------------------------

-- TODO noErase and noMadeUp are more about ES than diff3

-- Source View present in edit script
data _∈ˢ_ : ∀ {xs ys as a} -> View as a -> ES xs ys -> Set₁ where
  source-∈ : ∀ {as bs cs ds xs ys} {c : Edit as bs cs ds} {i : input c} {e : ES xs ys}
           -> c ∈ₑ e -> ⌞ c ⌟ ∈ˢ e 

-- Every term in the input tree is found as source in the edit script
noEraseˢ : ∀ {xs ys as a} {α : View as a} {x : DList xs} {y : DList ys} {e : ES xs ys}
            -> Diff x y e -> α ∈ x -> α ∈ˢ e
noEraseˢ (Del α p) (∈-here .α) = source-∈ (here (Del α))
noEraseˢ (Upd α y p) (∈-here .α) = source-∈ (here (Upd α y))
noEraseˢ (Cpy α p) (∈-here .α) = source-∈ (here (Cpy α))
noEraseˢ (Ins y p) (∈-here α) with noEraseˢ p (∈-here α)
noEraseˢ (Ins y p₁) (∈-here ._) | source-∈ {i = i} x = source-∈ {i = i} (there (Ins y) x)
noEraseˢ (Del y p) (∈-there q) with noEraseˢ p q
noEraseˢ (Del y p) (∈-there q) | source-∈ {i = i} x = source-∈ {i = i} (there (Del y) x)
noEraseˢ (Upd y z p) (∈-there q) with noEraseˢ p q
noEraseˢ (Upd y z p) (∈-there q) | source-∈ {i = i} x = source-∈ {i = i} (there (Upd y z) x)
noEraseˢ (Cpy y p) (∈-there q) with noEraseˢ p q
noEraseˢ (Cpy y p) (∈-there q) | source-∈ {i = i} x = source-∈ {i = i} (there (Cpy y) x)
noEraseˢ (Ins y p) (∈-there q) with noEraseˢ p (∈-there q)
noEraseˢ (Ins y p) (∈-there q) | source-∈ {i = i} x = source-∈ {i = i} (there (Ins y) x)

open import Data.Unit

-- Inverse of noErase
-- This lemma cannot be proved directly because of the abstraction introduced by ∈ˢ,
-- therefore the auxiliary lemma noMadeUpAuxˢ, which requires explicit equality proofs,
-- is used.
noMadeUpˢ : ∀ {xs ys as a} {t₀ : DList xs} {t₁ : DList ys} {e : ES xs ys}
              {α : View as a} -> α ∈ˢ e -> Diff t₀ t₁ e -> α ∈ t₀
noMadeUpˢ (source-∈ x) q rewrite mkDiff⟪ q ⟫ = ∈-⟪⟫ x

--------------------------------------------------------------------------------
-- Target view present in edit script

data _∈ₒ_ : ∀ {xs ys as a} -> View as a -> ES xs ys -> Set₁ where
  target-∈ : ∀ {as bs cs ds xs ys} {c : Edit as bs cs ds} {o : output c} {e : ES xs ys}
           -> c ∈ₑ e -> ⌜ c ⌝ ∈ₒ e 

noEraseₒ : ∀ {xs ys as a} {α : View as a} {x : DList xs} {y : DList ys} {e : ES xs ys}
            -> Diff x y e -> α ∈ y -> α ∈ₒ e
noEraseₒ End ()
noEraseₒ (Del x p) q with noEraseₒ p q
noEraseₒ (Del x p) q | target-∈ {o = o} r = target-∈ {o = o} (there (Del x) r)
noEraseₒ (Upd x α p) (∈-here .α) = target-∈ (here (Upd x α))
noEraseₒ (Upd x y p) (∈-there q) with noEraseₒ p q
noEraseₒ (Upd x y p) (∈-there q) | target-∈ {o = o} r = target-∈ {o = o} (there (Upd x y) r)
noEraseₒ (Cpy α p) (∈-here .α) = target-∈ (here (Cpy α))
noEraseₒ (Cpy x p) (∈-there q) with noEraseₒ p q
noEraseₒ (Cpy x p) (∈-there q) | target-∈ {o = o} r = target-∈ {o = o} (there (Cpy x) r)
noEraseₒ (Ins α p) (∈-here .α) = target-∈ (here (Ins α))
noEraseₒ (Ins y p) (∈-there q) with noEraseₒ p q 
noEraseₒ (Ins y p) (∈-there q) | target-∈ {o = o} r = target-∈ {o = o} (there (Ins y) r)

noMadeUpₒ : ∀ {xs ys as a} {α : View as a} {x : DList xs} {y : DList ys} {e : ES xs ys}
            -> α ∈ₒ e -> Diff x y e -> α ∈ y 
noMadeUpₒ (target-∈ x) q rewrite mkDiff⟦ q ⟧ = ∈-⟦⟧ x
