module View where

open import Data.List
open import Relation.Binary
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality hiding ([_])

postulate View : List Set -> Set -> Set

-- A View-specific instance of equality.
-- Using propositional equality is not an option because then it's not possible to
-- relate views with different indexes.
-- Using heterogeneous equality is not an option either because it refuse
-- recognize refl, failing to solve the underlying constraint about the indexes.
data _⋍_ : ∀ {xs ys a b} -> View xs a -> View ys b -> Set where
  refl : ∀ {xs a} {x : View xs a} -> x ⋍ x

postulate eq? : (a b : Set) -> Dec (a ≡ b)
postulate _=?=_ : ∀ {a xs ys} -> (x : View xs a) (y : View ys a) -> Dec (x ⋍ y)

--------------------------------------------------------------------------------
-- Even though it would be more convenient to work using a single 
-- comparison function rather than eq? followed by =?=, it turns out
-- that this produces ill-typed with clause with, preventing any proof. 

-- data _≅_ : ∀ {xs ys a b} -> View xs a -> View ys b -> Set where
--   refl : ∀ {xs a} {x : View xs a} -> x ≅ x

-- postulate _≟_ : ∀ {a b xs ys} -> (x : View xs a) (y : View ys b) -> Dec (x ≅ y)

--------------------------------------------------------------------------------

open import Data.Nat

postulate distance : ∀ {xs ys a} -> View xs a -> View ys a -> ℕ
