module Diff.Safety where

open import Diff.Core public
open import EditScript.Safety
open import Data.DTree
open import Lemmas

open import Function
open import Data.Product
open import Data.List
open import Relation.Binary
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality hiding ([_])

--------------------------------------------------------------------------------
-- Safety properties
--------------------------------------------------------------------------------

-- High level statements using Mapping

open import EditScript.Mapping 
import Data.Product as P

-- Let e be the edit script that maps the source tree x in the target tree y (Diff x y e).
-- If some value v is mapped to α in e, then α is a node present in the target tree y.
noTargetMadeUp : ∀ {xs ys as a v} {α : View as a} {x : DList xs} {y : DList ys} {e : ES xs ys}
            -> e ⊢ₑ v ~> ⟨ α ⟩ -> Diff x y e -> α ∈ y 
noTargetMadeUp p q rewrite mkDiff⟦ q ⟧ = targetOrigin p

-- Inverse of noTargetMadeUp.
-- Let e be the edit script that maps the source tree x in the target tree y (Diff x y e).
-- If a node α is present in the target tree y, than there is a value v which is mapped to α
-- in e.
noTargetErase : ∀ {xs ys as a} {α : View as a} {x : DList xs} {y : DList ys} {e : ES xs ys}
            -> Diff x y e -> α ∈ y -> ∃ λ v -> e ⊢ₑ v ~> ⟨ α ⟩
noTargetErase (Del x p) (∈-here α) = P.map id (there~> (Del x)) (noTargetErase p (∈-here α))
noTargetErase (Upd α β p) (∈-here .β) = ⟨ α ⟩ , Upd α β (here (Upd α β))
noTargetErase (Cpy α p) (∈-here .α) = ⟨ α ⟩ , (Cpy α (here (Cpy α)))
noTargetErase (Ins α p) (∈-here .α) = ⊥ , Ins α (here (Ins α))
noTargetErase (Del x p) (∈-there q) = P.map id (there~> (Del x)) (noTargetErase p (∈-there q))
noTargetErase (Upd x y p) (∈-there q) = P.map id (there~> (Upd x y)) (noTargetErase p q)
noTargetErase (Cpy y p) (∈-there q) = P.map id (there~> (Cpy y)) (noTargetErase p q)
noTargetErase (Ins y p) (∈-there q) = P.map id (there~> (Ins y)) (noTargetErase p q)

-- Let e be the edit script that maps the source tree x in the target tree y (Diff x y e).
-- If α is is mapped to some value v e, then α is a node present in the source tree x.
noSourceMadeUp : ∀ {xs ys as a v} {α : View as a} {x : DList xs} {y : DList ys} {e : ES xs ys}
               -> e ⊢ₑ ⟨ α ⟩ ~> v -> Diff x y e -> α ∈ x 
noSourceMadeUp p q rewrite mkDiff⟪ q ⟫ = sourceOrigin p

-- Inverse of noSourceMadeUp.
-- Let e be the edit script that maps the source tree x in the target tree y (Diff x y e).
-- If a node α is present in the source tree x, than there is a value v that is mapped to α
-- in e.
noSourceErase : ∀ {xs ys as a} {α : View as a} {x : DList xs} {y : DList ys} {e : ES xs ys} -> 
                  Diff x y e -> α ∈ x -> ∃ λ v -> e ⊢ₑ ⟨ α ⟩ ~> v
noSourceErase (Del α p) (∈-here .α) = ⊥ , Del α (here (Del α))
noSourceErase (Upd α β p) (∈-here .α) = ⟨ β ⟩ , (Upd α β (here (Upd α β)))
noSourceErase (Cpy α p) (∈-here .α) = ⟨ α ⟩ , (Cpy α (here (Cpy α)))
noSourceErase (Ins y p) (∈-here α) = P.map id (there~> (Ins y)) (noSourceErase p (∈-here α))
noSourceErase (Del y p) (∈-there q) = P.map id (there~> (Del y)) (noSourceErase p q)
noSourceErase (Upd x y p) (∈-there q) = P.map id (there~> (Upd x y)) (noSourceErase p q)
noSourceErase (Cpy y p) (∈-there q) = P.map id (there~> (Cpy y)) (noSourceErase p q)
noSourceErase (Ins y p) (∈-there q) = P.map id (there~> (Ins y)) (noSourceErase p (∈-there q))

--------------------------------------------------------------------------------
-- The same lemmas are proved using specific data-types.
-- This are more convienient to work with, when considering Embedding properties.

-- Source View present in edit script
data _∈ˢ_ : ∀ {xs ys as a} -> View as a -> ES xs ys -> Set₁ where
  source-∈ : ∀ {as bs cs ds xs ys} {c : Edit as bs cs ds} {i : input c} {e : ES xs ys}
           -> c ∈ₑ e -> ⌞ c ⌟ ∈ˢ e 

-- Every term in the input tree is found as source in the edit script
noEraseˢ : ∀ {xs ys as a} {α : View as a} {x : DList xs} {y : DList ys} {e : ES xs ys}
            -> Diff x y e -> α ∈ x -> α ∈ˢ e
noEraseˢ p q with noSourceErase p q
noEraseˢ p q | .(⟨ α ⟩) , Cpy α x = source-∈ x
noEraseˢ p q | .(⟨ β ⟩) , Upd α β x = source-∈ x
noEraseˢ p q | .⊥ , Del α x = source-∈ x

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

noMadeUpₒ : ∀ {xs ys as a} {α : View as a} {x : DList xs} {y : DList ys} {e : ES xs ys}
            -> α ∈ₒ e -> Diff x y e -> α ∈ y 
noMadeUpₒ (target-∈ x) q rewrite mkDiff⟦ q ⟧ = ∈-⟦⟧ x

noEraseₒ : ∀ {xs ys as a} {α : View as a} {x : DList xs} {y : DList ys} {e : ES xs ys} ->
             Diff x y e -> α ∈ y -> α ∈ₒ e
noEraseₒ p q with noTargetErase p q
noEraseₒ p q | .(⟨ α ⟩) , Cpy α x = target-∈ x
noEraseₒ p q | .(⟨ α ⟩) , Upd α β x = target-∈ x
noEraseₒ p q | .⊥ , Ins α x = target-∈ x

