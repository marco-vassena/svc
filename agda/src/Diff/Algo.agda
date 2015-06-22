module Diff.Algo where

open import Data.DTree
open import Diff.Core
open import Lemmas

--------------------------------------------------------------------------------
-- Diff algorithm
--------------------------------------------------------------------------------

open import Data.Nat hiding (eq?)
open import Relation.Binary.PropositionalEquality

del-size : ∀ {zs ws us as n} (xs : DList zs) (ts₁ : DList ws) (ys : DList as) (ts₂ : DList us) 
           -> size xs + size ts₁ + suc (size ys + size ts₂) ≤ n -> size (xs +++ ts₁) + suc (size ys + size ts₂) ≤ n
del-size xs ts₁ ys ts₂ p rewrite sym (size-+++ xs ts₁) = p

ins-size : ∀ {zs ws us as n} (xs : DList zs) (ts₁ : DList ws) (ys : DList as) (ts₂ : DList us) 
           -> size xs + size ts₁ + suc (size ys + size ts₂) ≤ n -> suc (size xs + size ts₁ + size (ys +++ ts₂)) ≤ n
ins-size xs ts₁ ys ts₂ p rewrite 
    sym (size-+++ ys ts₂)
  | +-distr3 (size xs) (size ts₁) (size (ys +++ ts₂)) = p

upd-size : ∀ {zs ws us as n} (xs : DList zs) (ts₁ : DList ws) (ys : DList as) (ts₂ : DList us) 
         -> size xs + size ts₁ + suc (size ys + size ts₂) ≤ n -> size (xs +++ ts₁) + size (ys +++ ts₂) ≤ n
upd-size xs ts₁ ys ts₂ p rewrite 
    sym (size-+++ xs ts₁) 
  | sym (size-+++ ys ts₂) = ≤-lemma (size (xs +++ ts₁)) (size (ys +++ ts₂)) p

-- Computes the length of an edit script.
cost : ∀ {xs ys} -> ES xs ys -> ℕ
cost (Ins x ∷ e) = 1 + cost e
cost (Del x ∷ e) = 1 + cost e
cost (Upd x y ∷ e) = distance x y + cost e 
cost (Nop ∷ e) = cost e
cost [] = 0

open import Relation.Nullary

_⨅_ : ∀ {xs ys} -> ES xs ys -> ES xs ys -> ES xs ys
e₁ ⨅ e₂ with cost e₁ ≤? cost e₂
e₁ ⨅ e₂ | yes p = e₁
e₁ ⨅ e₂ | no ¬p = e₂

infixl 3 _⨅_

-- Sized-diff
-- In order to convince the type-checker that diff is terminating, we introduce as an invariant
-- an upper-bound on the number of nodes contained in the lists.
sdiff : ∀ {xs ys n} -> (x : DList xs) (y : DList ys) -> size x + size y ≤ n -> ES xs ys
sdiff [] [] z≤n = []
sdiff [] (Node y ys ∷ ts) (s≤s p) rewrite sym (size-+++ ys ts) = Ins y ∷ (sdiff [] (ys +++ ts) p)
sdiff (Node x xs ∷ ts) [] (s≤s p) rewrite sym (size-+++ xs ts) = Del x ∷ (sdiff (xs +++ ts) [] p)
sdiff {n = suc n} (Node {a = a} x xs ∷ ts₁) (Node {a = b} y ys ∷ ts₂) (s≤s p) 
  with eq? a b
sdiff {._} {._} {suc n} (Node x xs ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | yes refl 
  = Del x ∷ (sdiff (xs +++ ts₁) (Node y ys ∷ ts₂) (del-size xs ts₁ ys ts₂ p)) 
  ⨅ Ins y ∷ (sdiff (Node x xs ∷ ts₁) (ys +++ ts₂) (ins-size xs ts₁ ys ts₂ p))
  ⨅ Upd x y ∷ (sdiff (xs +++ ts₁) (ys +++ ts₂) (upd-size xs ts₁ ys ts₂ p))
sdiff {._} {._} {suc n} (Node x xs ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | no ¬p 
  = Del x ∷ (sdiff (xs +++ ts₁) (Node y ys ∷ ts₂) (del-size xs ts₁ ys ts₂ p)) 
  ⨅ Ins y ∷ (sdiff (Node x xs ∷ ts₁) (ys +++ ts₂) (ins-size xs ts₁ ys ts₂ p))

-- Computes the minimal-length edit-script.
-- It calls sdiff with an appropriate upper bound on the number of nodes. 
diff : ∀ {xs ys} -> DList xs -> DList ys -> ES xs ys
diff x y = sdiff {n = size x + size y} x y (≤-refl (size x + size y))

--------------------------------------------------------------------------------

open import Data.Sum

lemma-⨅ : ∀ {xs ys} -> (e₁ : ES xs ys) (e₂ : ES xs ys) -> (e₁ ⨅ e₂) ≡ e₁ ⊎ (e₁ ⨅ e₂) ≡ e₂
lemma-⨅ e₁ e₂ with cost e₁ ≤? cost e₂
lemma-⨅ e₁ e₂ | yes p = inj₁ refl
lemma-⨅ e₁ e₂ | no ¬p = inj₂ refl

lemma-⨅₃ : ∀ {xs ys} (e₁ : ES xs ys) (e₂ : ES xs ys) (e₃ : ES xs ys) -> 
           let e = e₁ ⨅ e₂ ⨅ e₃ in e ≡ e₁ ⊎ e ≡ e₂ ⊎ e ≡ e₃ 
lemma-⨅₃ e₁ e₂ e₃ with e₁ ⨅ e₂ | lemma-⨅ e₁ e₂
lemma-⨅₃ e₁ e₂ e₃ | .e₁ | inj₁ refl with e₁ ⨅ e₃ | lemma-⨅ e₁ e₃
lemma-⨅₃ e₁ e₂ e₃ | .e₁ | inj₁ refl | .e₁ | inj₁ refl = inj₁ refl
lemma-⨅₃ e₁ e₂ e₃ | .e₁ | inj₁ refl | .e₃ | inj₂ refl = inj₂ (inj₂ refl)
lemma-⨅₃ e₁ e₂ e₃ | .e₂ | inj₂ refl with e₂ ⨅ e₃ | lemma-⨅ e₂ e₃
lemma-⨅₃ e₁ e₂ e₃ | .e₂ | inj₂ refl | .e₂ | inj₁ refl = inj₂ (inj₁ refl)
lemma-⨅₃ e₁ e₂ e₃ | .e₂ | inj₂ refl | .e₃ | inj₂ refl = inj₂ (inj₂ refl)

Diff-suf' : ∀ {xs ys n} (x : DList xs) (y : DList ys) (p : size x + size y ≤ n) -> Diff x y (sdiff x y p)
Diff-suf' [] [] z≤n = End
Diff-suf' [] (Node y ys ∷ b) (s≤s p) 
  rewrite sym (size-+++ ys b) = Ins y (Diff-suf' [] (ys +++ b) p)
Diff-suf' (Node x xs ∷ a) [] (s≤s p) 
  rewrite sym (size-+++ xs a) = Del x (Diff-suf' (xs +++ a) [] p)
Diff-suf' (Node {a = a₁} x xs ∷ a) (Node {a = b₁} y ys ∷ b) (s≤s p) with eq? a₁ b₁
Diff-suf' (Node x xs ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | yes refl
  with     Del x ∷ (sdiff (xs +++ ts₁) (Node y ys ∷ ts₂) (del-size xs ts₁ ys ts₂ p)) 
         ⨅ Ins y ∷ (sdiff (Node x xs ∷ ts₁) (ys +++ ts₂) (ins-size xs ts₁ ys ts₂ p))
         ⨅ Upd x y ∷ (sdiff (xs +++ ts₁) (ys +++ ts₂) (upd-size xs ts₁ ys ts₂ p))
       | lemma-⨅₃ (Del x ∷ (sdiff (xs +++ ts₁) (Node y ys ∷ ts₂) (del-size xs ts₁ ys ts₂ p)))
                  (Ins y ∷ (sdiff (Node x xs ∷ ts₁) (ys +++ ts₂) (ins-size xs ts₁ ys ts₂ p)))
                  (Upd x y ∷ (sdiff (xs +++ ts₁) (ys +++ ts₂) (upd-size xs ts₁ ys ts₂ p)))
Diff-suf' (Node x xs ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | yes refl | .(Del x ∷ _) | inj₁ refl 
  = Del x (Diff-suf' (xs +++ ts₁) (Node y ys ∷ ts₂) (del-size xs ts₁ ys ts₂ p))
Diff-suf' (Node x xs₃ ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | yes refl | .(Ins y ∷ _) | inj₂ (inj₁ refl) 
  = Ins y (Diff-suf' (Node x xs₃ ∷ ts₁) (ys +++ ts₂) (ins-size xs₃ ts₁ ys ts₂ p))
Diff-suf' (Node x xs₃ ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | yes refl | .(Upd x y ∷ _) | inj₂ (inj₂ refl) 
  = Upd x y (Diff-suf' (xs₃ +++ ts₁) (ys +++ ts₂) (upd-size xs₃ ts₁ ys ts₂ p))
Diff-suf' (Node x xs ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | no ¬p with
        Del x ∷ (sdiff (xs +++ ts₁) (Node y ys ∷ ts₂) (del-size xs ts₁ ys ts₂ p)) 
      ⨅ Ins y ∷ (sdiff (Node x xs ∷ ts₁) (ys +++ ts₂) (ins-size xs ts₁ ys ts₂ p))
    | lemma-⨅ (Del x ∷ (sdiff (xs +++ ts₁) (Node y ys ∷ ts₂) (del-size xs ts₁ ys ts₂ p)))
              (Ins y ∷ (sdiff (Node x xs ∷ ts₁) (ys +++ ts₂) (ins-size xs ts₁ ys ts₂ p)))
Diff-suf' (Node x xs₂ ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | no ¬p | .(Del x ∷ _) | inj₁ refl 
  = Del x (Diff-suf' (xs₂ +++ ts₁) (Node y ys ∷ ts₂) (del-size xs₂ ts₁ ys ts₂ p))
Diff-suf' (Node x xs₂ ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | no ¬p | .(Ins y ∷ _) | inj₂ refl 
  = Ins y (Diff-suf' (Node x xs₂ ∷ ts₁) (ys +++ ts₂) (ins-size xs₂ ts₁ ys ts₂ p))

-- Note that the opposite does not hold in general.
-- The reason is that diff finds the edit script which minimizes cost.
-- Therefore given Diff x y e, e ≠ diff x y as e might be one of the non-optimal scripts.
-- Diff could be adapted to include additional proofs object that thake these issues into account,
-- but this is not really important for the properties I am going to prove.
-- In other words, the proofs about Diff are valid regardless of the fact that the edit-script is optimal.

Diff-suf : ∀ {xs ys} (x : DList xs) (y : DList ys) -> Diff x y (diff x y)
Diff-suf x y = Diff-suf' x y (≤-refl (size x + size y))
