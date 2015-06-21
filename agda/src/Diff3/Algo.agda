module Diff3.Algo where

open import Diff3.Core

open import Data.List
open import Data.Empty
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality hiding ([_])

-- Untyped version of diff3.
-- Well-typedness is check afterwards, and produces separate conflcits
diff3 : ∀ {xs ys zs} -> (e₁ : ES xs ys) (e₂ : ES xs zs) -> e₁ ~ e₂ -> ES₃
diff3 .End .End End = End
diff3 ._ ._ (DelDel x p) = Del x (diff3 _ _ p)
diff3 ._ ._ (UpdUpd x y z p) with y =?= z
diff3 ._ ._ (UpdUpd x y .y p) | yes refl = Upd x y (diff3 _ _ p)
diff3 ._ ._ (UpdUpd x y z p) | no ¬p = Cnf (UpdUpd y z) (diff3 _ _ p)
diff3 ._ ._ (DelUpd x y p) with x =?= y
diff3 ._ ._ (DelUpd x .x p) | yes refl = Del x (diff3 _ _ p)
diff3 ._ ._ (DelUpd x y p) | no ¬p = Cnf (DelUpd x y) (diff3 _ _ p)
diff3 ._ ._ (UpdDel x y p) with x =?= y 
diff3 ._ ._ (UpdDel x .x p) | yes refl = Del x (diff3 _ _ p)
diff3 ._ ._ (UpdDel x y p) | no ¬p = Cnf (UpdDel x y) (diff3 _ _ p)
diff3 ._ ._ (InsIns {a = a} {b = b} x y p) with eq? a b
diff3 ._ ._ (InsIns x y p) | yes refl with x =?= y
diff3 ._ ._ (InsIns x .x p) | yes refl | yes refl = Ins x (diff3 _ _ p)
diff3 ._ ._ (InsIns x y p) | yes refl | no ¬p = Cnf (InsIns x y) (diff3 _ _ p)
diff3 ._ ._ (InsIns x y p) | no ¬p = Cnf (InsIns x y) (diff3 _ _ p)
diff3 ._ e₂ (Ins₁ x p) = Ins x (diff3 _ _ p)
diff3 e₁ ._ (Ins₂ x p) = Ins x (diff3 _ _ p)

--------------------------------------------------------------------------------
-- When ES₃ is well typed ?
--------------------------------------------------------------------------------

-- ES₃ is well typed
data _↓_ : ES₃ -> List Set -> Set where
  End : End ↓ []
  Ins : ∀ {xs ys a e} -> (x : View xs a) -> e ↓ (xs ++ ys) -> Ins x e ↓ (a ∷ ys)
  Del : ∀ {xs ys a e} -> (x : View xs a) -> e ↓ ys -> Del x e ↓ ys
  Upd : ∀ {xs ys zs a e} -> (x : View xs a) (y : View ys a) -> e ↓ (ys ++ zs) -> Upd x y e ↓ (a ∷ zs)

open import Data.Empty


-- Sufficient condition for well-typedness of diff3.
-- If p ⇊ ws then diff3 e1 e2 p is well-typed.
mergeSuff : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {p : e₁ ~ e₂} -> p ⇊ ws -> diff3 e₁ e₂ p ↓ ws
mergeSuff End = End
mergeSuff (InsIns {a = a} x q) with eq? a a
mergeSuff (InsIns x q) | yes refl with x =?= x
mergeSuff (InsIns x q) | yes refl | yes refl = Ins x (mergeSuff q)
mergeSuff (InsIns x q) | yes refl | no ¬p = ⊥-elim (¬p refl)
mergeSuff (InsIns x q) | no ¬p = ⊥-elim (¬p refl)
mergeSuff (UpdUpd x y q) with y =?= y
mergeSuff (UpdUpd x y q) | yes refl = Upd x y (mergeSuff q)
mergeSuff (UpdUpd x y q) | no ¬p = ⊥-elim (¬p refl)
mergeSuff (DelDel x q) = Del x (mergeSuff q)
mergeSuff (DelCpy x q) with x =?= x
mergeSuff (DelCpy x q) | yes refl = Del x (mergeSuff q)
mergeSuff (DelCpy x q) | no ¬p = ⊥-elim (¬p refl)
mergeSuff (CpyDel x q) with x =?= x
mergeSuff (CpyDel x q) | yes refl = Del x (mergeSuff q)
mergeSuff (CpyDel x q) | no ¬p = ⊥-elim (¬p refl)
mergeSuff (Ins₁ x q) = Ins x (mergeSuff q)
mergeSuff (Ins₂ x q) = Ins x (mergeSuff q)

-- Necessary condition for well-typedness of diff3.
-- If diff3 e1 e2 p is well-typed and produce ws then p ⇊ ws. 
mergeNec : ∀ {xs ys zs ws} {e₁ : ES xs ys}{e₂ : ES xs zs} -> (p : e₁ ~ e₂) -> diff3 e₁ e₂ p ↓ ws -> p ⇊ ws
mergeNec End End = End
mergeNec (DelDel x p) (Del .x q) = DelDel x (mergeNec p q)
mergeNec (UpdUpd x y z p) q with y =?= z
mergeNec (UpdUpd x y .y p) (Upd .x .y q) | yes refl = UpdUpd x y (mergeNec p q)
mergeNec (UpdUpd x y z p) () | no ¬p
mergeNec (DelUpd x y p) q with x =?= y
mergeNec (DelUpd x .x p) (Del .x q) | yes refl = DelCpy x (mergeNec p q)
mergeNec (DelUpd x y p) () | no ¬p
mergeNec (UpdDel x y p) q with x =?= y
mergeNec (UpdDel x .x p) (Del .x q) | yes refl = CpyDel x (mergeNec p q)
mergeNec (UpdDel x y p) () | no ¬p
mergeNec (InsIns {a = a} {b = b} x y p) q with eq? a b
mergeNec (InsIns x y p) q | yes refl with x =?= y
mergeNec (InsIns x .x p) (Ins .x q) | yes refl | yes refl = InsIns x (mergeNec p q)
mergeNec (InsIns x y p) () | yes refl | no ¬p
mergeNec (InsIns x y p) () | no ¬p
mergeNec (Ins₁ x p) (Ins .x q) = Ins₁ x (mergeNec p q)
mergeNec (Ins₂ x p) (Ins .x q) = Ins₂ x (mergeNec p q)

--------------------------------------------------------------------------------

data NoCnf : ES₃ -> Set₁ where
  End : NoCnf End
  Ins : ∀ {e xs a} (x : View xs a) -> NoCnf e -> NoCnf (Ins x e)
  Del : ∀ {e xs a} (x : View xs a) -> NoCnf e -> NoCnf (Del x e)
  Upd : ∀ {e xs ys a} (x : View xs a) (y : View ys a) -> NoCnf e -> NoCnf (Upd x y e) 

-- Well-typed implies no conflicts
diff3-wt : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} -> (p : e₁ ~ e₂) -> diff3 e₁ e₂ p ↓ ws -> NoCnf (diff3 e₁ e₂ p)
diff3-wt End End = End
diff3-wt (DelDel x p) (Del .x q) = Del x (diff3-wt p q)
diff3-wt (UpdUpd x y z p) q with y =?= z
diff3-wt (UpdUpd x y .y p) (Upd .x .y q) | yes refl = Upd x y (diff3-wt p q)
diff3-wt (UpdUpd x y z p) () | no ¬p
diff3-wt (DelUpd x y p) q with x =?= y
diff3-wt (DelUpd x .x p) (Del .x q) | yes refl = Del x (diff3-wt p q)
diff3-wt (DelUpd x y p) () | no ¬p
diff3-wt (UpdDel x y p) q with x =?= y
diff3-wt (UpdDel x .x p) (Del .x q) | yes refl = Del x (diff3-wt p q)
diff3-wt (UpdDel x y p) () | no ¬p
diff3-wt (InsIns {a = a} {b = b} x y p) q with eq? a b
diff3-wt (InsIns x y p) q | yes refl with x =?= y
diff3-wt (InsIns x .x p) (Ins .x q) | yes refl | yes refl = Ins x (diff3-wt p q)
diff3-wt (InsIns x y p) () | yes refl | no ¬p
diff3-wt (InsIns x y p) () | no ¬p
diff3-wt (Ins₁ x p) (Ins .x q) = Ins x (diff3-wt p q)
diff3-wt (Ins₂ x p) (Ins .x q) = Ins x (diff3-wt p q)

-- Well-typed ES₃ can be converted to well-typed ES
toES : ∀ {xs ys zs ws} {e₀₁ : ES xs ys} {e₀₂ : ES xs zs} (p : e₀₁ ~ e₀₂) -> 
       let e₀₁₂ = diff3 e₀₁ e₀₂ p in (q : e₀₁₂ ↓ ws) -> ES xs ws
toES End End = End
toES (DelDel x p) (Del .x q) = Del x (toES p q)
toES (UpdUpd x y z p) q with y =?= z
toES (UpdUpd x y .y p) (Upd .x .y q) | yes refl = Upd x y (toES p q)
toES (UpdUpd x y z p) () | no ¬p
toES (DelUpd x y p) q with x =?= y
toES (DelUpd x .x p) (Del .x q) | yes refl = Del x (toES p q)
toES (DelUpd x y p) () | no ¬p
toES (UpdDel x y p) q with x =?= y
toES (UpdDel x .x p) (Del .x q) | yes refl = Del x (toES p q)
toES (UpdDel x y p) () | no ¬p
toES (InsIns {a = a} {b = b} x y p) q with eq? a b
toES (InsIns x y p) q | yes refl with x =?= y
toES (InsIns x .x p) (Ins .x q) | yes refl | yes refl = Ins x (toES p q)
toES (InsIns x y p) () | yes refl | no ¬p
toES (InsIns x y p) () | no ¬p
toES (Ins₁ x p) (Ins .x q) = Ins x (toES p q)
toES (Ins₂ x p) (Ins .x q) = Ins x (toES p q)

--------------------------------------------------------------------------------

-- diff3 is reflexive. Any edit script run against itself succeeds
diff3-refl : ∀ {xs ys} (e : ES xs ys) -> diff3 e e (~-refl e) ↓ ys
diff3-refl (Ins {a = a} x e) with eq? a a
diff3-refl (Ins x e) | yes refl with x =?= x
diff3-refl (Ins x e) | yes refl | yes refl = Ins x (diff3-refl e)
diff3-refl (Ins x e) | yes refl | no ¬p = ⊥-elim (¬p refl)
diff3-refl (Ins x e) | no ¬p = ⊥-elim (¬p refl)
diff3-refl (Del x e) = Del x (diff3-refl e)
diff3-refl (Upd x y e) with y =?= y
diff3-refl (Upd x y e) | yes refl = Upd x y (diff3-refl e)
diff3-refl (Upd x y e) | no ¬p = ⊥-elim (¬p refl)
diff3-refl End = End

diff3-sym : ∀ {xs ys zs} {e₁ : ES xs ys} {e₂ : ES xs zs} -> (p : e₁ ~ e₂) -> 
             let e₁₂ = diff3 e₁ e₂ p in NoCnf e₁₂ -> e₁₂ ≡ diff3 e₂ e₁ (~-sym p)
diff3-sym End End = refl
diff3-sym (DelDel x p) (Del .x q) = cong (Del x) (diff3-sym p q)
diff3-sym (UpdUpd x y z p) q with y =?= z
diff3-sym (UpdUpd x y .y p) q | yes refl with y =?= y
diff3-sym (UpdUpd x y .y p) (Upd .x .y q) | yes refl | yes refl = cong (Upd x y) (diff3-sym p q)
diff3-sym (UpdUpd x y .y p) q | yes refl | no ¬p = ⊥-elim (¬p refl)
diff3-sym (UpdUpd x y z p) () | no ¬p
diff3-sym (DelUpd x y p) q with x =?= y
diff3-sym (DelUpd x .x p) (Del .x q) | yes refl = cong (Del x) (diff3-sym p q)
diff3-sym (DelUpd x y p) () | no ¬p
diff3-sym (UpdDel x y p) q with x =?= y
diff3-sym (UpdDel x .x p) (Del .x q) | yes refl = cong (Del x) (diff3-sym p q)
diff3-sym (UpdDel x y p) () | no ¬p
diff3-sym (InsIns {a = a} {b = b} x y p) q with eq? a b
diff3-sym (InsIns x y p) q | yes refl with x =?= y
diff3-sym (InsIns {a = a} x .x p) q | yes refl | yes refl with eq? a a
diff3-sym (InsIns x .x p) q | yes refl | yes refl | yes refl with x =?= x
diff3-sym (InsIns x .x p) (Ins .x q) | yes refl | yes refl | yes refl | yes refl = cong (Ins x) (diff3-sym p q)
diff3-sym (InsIns x .x p) q | yes refl | yes refl | yes refl | no ¬p = ⊥-elim (¬p refl)
diff3-sym (InsIns x .x p) q | yes refl | yes refl | no ¬p = ⊥-elim (¬p refl)
diff3-sym (InsIns x y p) () | yes refl | no ¬p
diff3-sym (InsIns x y p) () | no ¬p
diff3-sym (Ins₁ x p) (Ins .x q) = cong (Ins x) (diff3-sym p q)
diff3-sym (Ins₂ x p) (Ins .x q) = cong (Ins x) (diff3-sym p q)

-- Troubles to define this. The issue is that the with
-- clause produces an ill-typed function ... but how do I fix it?
-- postulate toES-sym : ∀ {xs ys zs ws} {e₀₁ : ES xs ys} {e₀₂ : ES xs zs} (p : e₀₁ ~ e₀₂) -> 
--            let e₀₁₂ = diff3 e₀₁ e₀₂ p in (q : e₀₁₂ ↓ ws) -> toES p q ≡ toES (~-sym p) (↓-sym p q)
-- toES-sym p q 
--  rewrite sym (diff3-sym p (diff3-wt p q)) = {!!}

--  with diff3 _ _ p | diff3-sym p (diff3-wt p q)
-- ... | e | a = {!!}


--------------------------------------------------------------------------------

-- well-typedness is symmetric
↓-sym : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} -> (p : e₁ ~ e₂) -> diff3 e₁ e₂ p ↓ ws -> diff3 e₂ e₁ (~-sym p) ↓ ws
↓-sym p q rewrite sym (diff3-sym p (diff3-wt p q)) = q

--------------------------------------------------------------------------------

-- aux : ∀ {xs ys 

-- Shows that a well typed diff3 corresponds to Diff3
diff₃-suf : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} -> (p : e₁ ~ e₂) ->
            (q : diff3 e₁ e₂ p ↓ ws) -> Diff₃ e₁ e₂ (toES p q)
diff₃-suf End End = End
diff₃-suf (DelDel x p) (Del .x q) = DelDel x (diff₃-suf p q)
diff₃-suf (UpdUpd x y z p) q with y =?= z
diff₃-suf (UpdUpd x y .y p) (Upd .x .y q) | yes refl = UpdUpd x y (diff₃-suf p q)
diff₃-suf (UpdUpd x y z p) () | no ¬p
diff₃-suf (DelUpd x y p) q with x =?= y
diff₃-suf (DelUpd x .x p) (Del .x q) | yes refl = DelCpy x (diff₃-suf p q)
diff₃-suf (DelUpd x y p) () | no ¬p
diff₃-suf (UpdDel x y p) q with x =?= y
diff₃-suf (UpdDel x .x p) (Del .x q) | yes refl = CpyDel x (diff₃-suf p q)
diff₃-suf (UpdDel x y p) () | no ¬p
diff₃-suf (InsIns {a = a} {b = b} x y p) q with eq? a b
diff₃-suf (InsIns x y p) q | yes refl with x =?= y
diff₃-suf (InsIns x .x p) (Ins .x q) | yes refl | yes refl = InsIns x (diff₃-suf p q)
diff₃-suf (InsIns x y p) () | yes refl | no ¬p
diff₃-suf (InsIns x y p) () | no ¬p
diff₃-suf (Ins₁ x p) (Ins .x q) = Ins₁ x (diff₃-suf p q)
diff₃-suf (Ins₂ x p) (Ins .x q) = Ins₂ x (diff₃-suf p q)

-- Show the inverse fact : 
diff₃-nec : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} -> (p : e₁ ~ e₂) ->
            let e₁₂ = diff3 e₁ e₂ p in (q : e₁₂ ↓ ws) -> Diff₃ e₁ e₂ e₃ -> e₃ ≡ toES p q
diff₃-nec End End End = refl
diff₃-nec (DelDel x p) (Del .x q) (DelDel .x d) = cong (Del x) (diff₃-nec p q d)
diff₃-nec (UpdUpd x y z p) q d with y =?= z
diff₃-nec (UpdUpd x y .y p) (Upd .x .y q) (UpdUpd .x .y d) | yes refl = cong (Upd x y) (diff₃-nec p q d)
diff₃-nec (UpdUpd x y z p) () d | no ¬p
diff₃-nec (DelUpd x y p) q d with x =?= y
diff₃-nec (DelUpd x .x p) (Del .x q) (DelCpy .x d) | yes refl = cong (Del x) (diff₃-nec p q d)
diff₃-nec (DelUpd x y p) () d | no ¬p
diff₃-nec (UpdDel x y p) q d with x =?= y
diff₃-nec (UpdDel x .x p₁) (Del .x q) (CpyDel .x d) | yes refl = cong (Del x) (diff₃-nec p₁ q d)
diff₃-nec (UpdDel x y p) () d | no ¬p
diff₃-nec (InsIns {a = a} {b = b} x y p) q d with eq? a b
diff₃-nec (InsIns x y p) q d | yes refl with x =?= y
diff₃-nec (InsIns x .x p) (Ins .x q) (InsIns .x d) | yes refl | yes refl = cong (Ins x) (diff₃-nec p q d)
diff₃-nec (InsIns x .x p) (Ins .x q) (Ins₁ {{i = ()}} .x d) | yes refl | yes refl
diff₃-nec (InsIns x .x p) (Ins .x q) (Ins₂ {{i = ()}} .x d) | yes refl | yes refl
diff₃-nec (InsIns x y p) () d | yes refl | no ¬p
diff₃-nec (InsIns x y p) () d | no ¬p
diff₃-nec (Ins₁ {{i = ()}} x p) (Ins .x q) (InsIns .x d)
diff₃-nec (Ins₁ x p) (Ins .x q) (Ins₁ .x d) = cong (Ins x) (diff₃-nec p q d)
diff₃-nec (Ins₁ x p) (Ins .x q) (Ins₂ {{i = ()}} x₁ d)
diff₃-nec (Ins₂ {{i = ()}} x p) (Ins .x q) (InsIns .x d)
diff₃-nec (Ins₂ x p) (Ins .x q) (Ins₁ {{i = ()}} x₁ d)
diff₃-nec (Ins₂ x p) (Ins .x q) (Ins₂ .x d) = cong (Ins x) (diff₃-nec p q d)

-- Now scripts produced by diff3 are in a one-to-one relationship with the Diff₃ data-type.
-- Therefore, being uniquely determined by Diff₃, we can prove facts about 
-- diff3 using Diff₃, which is much convinient as it results in simpler
-- and shorter proofs.

--------------------------------------------------------------------------------
-- Relates Diff and Diff₃ and diff3

diff₃-Diff-suf : ∀ {xs ys zs ws} {x : DList xs} {y : DList ys} {z : DList zs}
                 {e₁ : ES xs ys} {e₂ : ES xs zs} (d₁ : Diff x y e₁) (d₂ : Diff x z e₂) ->
                 let p = Diff~ d₁ d₂ in
                 let e₃ = diff3 e₁ e₂ p in (q : e₃ ↓ ws) -> Diff₃ e₁ e₂ (toES p q)
diff₃-Diff-suf d₁ d₂ q = diff₃-suf (Diff~ d₁ d₂) q

diff₃-Diff-nec : ∀ {xs ys zs ws} {x : DList xs} {y : DList ys} {z : DList zs}
                 {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} (d₁ : Diff x y e₁) (d₂ : Diff x z e₂) ->
                 let p = Diff~ d₁ d₂ in
                 let e₁₂ = diff3 e₁ e₂ p in (q : e₁₂ ↓ ws) -> Diff₃ e₁ e₂ e₃ -> e₃ ≡ toES p q
diff₃-Diff-nec d₁ d₂ q = diff₃-nec (Diff~ d₁ d₂) q

diff3↓ : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} 
           -> (d : Diff₃ e₁ e₂ e₃) -> diff3 e₁ e₂ (Diff₃~ d) ↓ ws
diff3↓ End = End
diff3↓ (InsIns {a = a} x d) with eq? a a
diff3↓ (InsIns x d) | yes refl with x =?= x
diff3↓ (InsIns x d) | yes refl | yes refl = Ins x (diff3↓ d)
diff3↓ (InsIns x d) | yes refl | no ¬p = ⊥-elim (¬p refl)
diff3↓ (InsIns x d) | no ¬p = ⊥-elim (¬p refl)
diff3↓ (Ins₁ x d) = Ins x (diff3↓ d)
diff3↓ (Ins₂ x d) = Ins x (diff3↓ d)
diff3↓ (DelDel x d) = Del x (diff3↓ d)
diff3↓ (DelCpy x d) with x =?= x
diff3↓ (DelCpy x d) | yes refl = Del x (diff3↓ d)
diff3↓ (DelCpy x d) | no ¬p = ⊥-elim (¬p refl)
diff3↓ (CpyDel x d) with x =?= x
diff3↓ (CpyDel x d) | yes refl = Del x (diff3↓ d)
diff3↓ (CpyDel x d) | no ¬p = ⊥-elim (¬p refl)
diff3↓ (UpdUpd x y d) with y =?= y
diff3↓ (UpdUpd x y d) | yes refl = Upd x y (diff3↓ d)
diff3↓ (UpdUpd x y d) | no ¬p = ⊥-elim (¬p refl)

--------------------------------------------------------------------------------

