module Diff3 where

open import Diff
open import View

open import Data.Product
open import Data.Sum
open import Data.List
open import Relation.Binary
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality hiding ([_])

data Conflict : Set₁ where
  UpdUpd : ∀ {xs ys a} -> View xs a -> View ys a -> Conflict
  DelUpd : ∀ {xs ys a} -> View xs a -> View ys a -> Conflict
  UpdDel : ∀ {xs ys a} -> View xs a -> View ys a -> Conflict
  InsIns : ∀ {xs ys a b} -> View xs a -> View ys b -> Conflict

-- Untytped version of ES3
data ES₃ : Set₁ where
  End : ES₃
  Ins : ∀ {xs a} -> View xs a -> ES₃ -> ES₃
  Del : ∀ {xs a} -> View xs a -> ES₃ -> ES₃
  Upd : ∀ {xs ys a} -> View xs a -> View ys a -> ES₃ -> ES₃
  Cpy : ∀ {xs a} -> View xs a -> ES₃ -> ES₃
  Cnf : Conflict -> ES₃ -> ES₃

-- Untyped version of diff3.
-- Well-typedness is check afterwards, and produces separate conflcits
diff3 : ∀ {xs ys zs} -> (e₁ : ES xs ys) (e₂ : ES xs zs) -> e₁ ~ e₂ -> ES₃
diff3 .End .End End = End
diff3 ._ ._ (DelDel x p) = Del x (diff3 _ _ p)
diff3 ._ ._ (UpdUpd x y z p) with y =?= z
diff3 ._ ._ (UpdUpd x y .y p) | yes refl = Upd x y (diff3 _ _ p)
diff3 ._ ._ (UpdUpd x y z p) | no ¬p = Cnf (UpdUpd y z) (diff3 _ _ p)
diff3 ._ ._ (CpyCpy x p) = Cpy x (diff3 _ _ p)
diff3 ._ ._ (CpyDel x p) = Del x (diff3 _ _ p)
diff3 ._ ._ (DelCpy x p) = Del x (diff3 _ _ p)
diff3 ._ ._ (CpyUpd x y p) = Upd x y (diff3 _ _ p)
diff3 ._ ._ (UpdCpy x y p) = Upd x y (diff3 _ _ p)
diff3 ._ ._ (DelUpd x y p) = Cnf (DelUpd x y) (diff3 _ _ p)
diff3 ._ ._ (UpdDel x y p) = Cnf (UpdDel x y) (diff3 _ _ p)
diff3 ._ ._ (InsIns {a = a} {b = b} x y p) with eq? a b
diff3 ._ ._ (InsIns x y p) | yes refl with x =?= y
diff3 ._ ._ (InsIns x .x p) | yes refl | yes refl = Ins x (diff3 _ _ p)
diff3 ._ ._ (InsIns x y p) | yes refl | no ¬p = Cnf (InsIns x y) (diff3 _ _ p)
diff3 ._ ._ (InsIns x y p) | no ¬p = Cnf (InsIns x y) (diff3 _ _ p)
diff3 ._ e₂ (Ins₁ x p) = Ins x (diff3 _ _ p)
diff3 e₁ ._ (Ins₂ x p) = Ins x (diff3 _ _ p)

-- If the returned ES₃ is not empty the remaining nodes are tagged as conflicts.

-- Here we try to reconstruct a value of the desired type.
-- {-# NON_TERMINATING #-}
-- toDTree : (A : Set) -> ES₃ -> (DTree A × ES₃)
-- toDList : (xs : List Set) -> ES₃ -> (DList xs × ES₃)

-- toDTree A End = MTree , End
-- toDTree A (Node {xs = xs} {a = B} x e) with toDList xs e | eq? A B
-- toDTree a (Node x e) | ds , e₁ | yes refl = (Node x ds) , e₁
-- toDTree A (Node x e) | ds , e₁ | no ¬p = (TCnf x ds) , e₁
-- -- When a conflict occurs we follow the first edit script types
-- toDTree A (Cnf (UpdUpd {xs = xs} x y) e) with toDList xs e
-- ... | ds , e₁ = (Cnf (UpdUpd x y) ds) , e₁
-- toDTree A (Cnf (DelUpd {xs = xs} x y) e) with toDList xs e
-- toDTree A (Cnf (DelUpd x y) e) | ds , e₁ = (Cnf (DelUpd x y) ds) , e₁
-- toDTree A (Cnf (UpdDel {xs = xs} x y) e) with toDList xs e
-- toDTree A (Cnf (UpdDel x y) e) | ds , e₁ = (Cnf (UpdDel x y) ds) , e₁
-- toDTree A (Cnf (InsIns {xs = xs} x y) e) with toDList xs e
-- toDTree A (Cnf (InsIns x y) e) | ds , e₁ = (Cnf (InsIns x y) ds) , e₁ 

-- toDList [] e = DNil , e
-- toDList (x ∷ xs) e with toDTree x e
-- toDList (x ∷ xs) e | t , e₁ with toDList xs e₁
-- toDList (x ∷ xs) e | t , e₁ | ts , e₂ = (DCons t ts) , e₂
  
--------------------------------------------------------------------------------
-- When ES₃ is well typed ?
--------------------------------------------------------------------------------

open import HList
postulate build : ∀ {xs a} -> View xs a -> HList xs -> a

-- TODO consider haveing also input type-list in ↓
-- We can of course prove that in any diff3 that is always the common xs,
-- but maybe we can decouple ES₃ from e₁ and e₂.
-- ES₃ is well typed
data _↓_ : ES₃ -> List Set -> Set where
  End : End ↓ []
  Ins : ∀ {xs ys a e} -> (x : View xs a) -> e ↓ (xs ++ ys) -> Ins x e ↓ (a ∷ ys)
  Del : ∀ {xs ys a e} -> (x : View xs a) -> e ↓ ys -> Del x e ↓ ys
  Upd : ∀ {xs ys zs a e} -> (x : View xs a) (y : View ys a) -> e ↓ (ys ++ zs) -> Upd x y e ↓ (a ∷ zs)
  Cpy : ∀ {xs ys a e} -> (x : View xs a) -> e ↓ (xs ++ ys) -> Cpy x e ↓ (a ∷ ys)

-- Patch. If ES₃ is well typed then we can produce the desired result
toHList : ∀ {xs} -> (e : ES₃) -> e ↓ xs -> HList xs
toHList .End End = []
toHList (Ins .x e) (Ins {xs = xs} {ys = ys} x p) with split {xs} {ys} (toHList e p)
toHList (Ins .x e) (Ins x p) | hs₁ , hs₂ = (build x hs₁) ∷ hs₂
toHList (Del .x e) (Del x p) = toHList e p
toHList (Upd .x .y e) (Upd {ys = ys} {zs = zs} x y p) with split {ys} {zs} (toHList e p)
toHList (Upd .x .y e) (Upd x y p) | hs₁ , hs₂ = (build y hs₁) ∷ hs₂
toHList (Cpy .x e) (Cpy {xs = xs} {ys = ys} x p) with split {xs} {ys} (toHList e p)
toHList (Cpy .x e) (Cpy x p) | hs₁ , hs₂ = (build x hs₁) ∷ hs₂


open import DTree

-- What are the sufficient conditions on e₁ and e₂ so that diff3 e₁ e₂ is well-typed?
data _⇊_ : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES zs ws} -> e₁ ~ e₂ -> List Set -> Set₁ where
  End : End ⇊ []
  InsIns : ∀ {xs ys zs ws us a} {e₁ : ES xs (ys ++ zs)} {e₂ : ES xs (ys ++ ws)} {p : e₁ ~ e₂}
           -> (x : View ys a) -> p ⇊ (ys ++ us) -> InsIns x x p ⇊ (a ∷ us)  -- Same x
  UpdUpd : ∀ {xs ys zs ws us ts a} {e₁ : ES (xs ++ zs) (ys ++ ws)} {e₂ : ES (xs ++ zs) (ys ++ us)} {p : e₁ ~ e₂} 
           -> (x : View xs a) (y : View ys a) -> p ⇊ (ys ++ ts) -> UpdUpd x y y p ⇊ (a ∷ ts)
  CpyCpy : ∀ {xs ys zs ws ts a} {e₁ : ES (xs ++ ys) (xs ++ zs)} {e₂ : ES (xs ++ ys) (xs ++ ws)} {p : e₁ ~ e₂} 
           -> (x : View xs a) -> p ⇊ (xs ++ ts) -> CpyCpy x p ⇊ (a ∷ ts)
  DelDel : ∀ {xs ys zs ws ts a} {e₁ : ES (xs ++ ys) zs} {e₂ : ES (xs ++ ys) ws} {p : e₁ ~ e₂} 
           -> (x : View xs a) -> p ⇊ ts -> DelDel x p ⇊ ts
  DelCpy : ∀ {xs ys zs us ws a} {e₁ : ES (xs ++ ys) zs} {e₂ : ES (xs ++ ys) (xs ++ ws)} {p : e₁ ~ e₂} 
           -> (x : View xs a) -> p ⇊ us -> DelCpy x p ⇊ us
  CpyDel : ∀ {xs ys zs us ws a} {e₁ : ES (xs ++ ys) (xs ++ ws)} {e₂ : ES (xs ++ ys) zs} {p : e₁ ~ e₂} 
           -> (x : View xs a) -> p ⇊ us -> CpyDel x p ⇊ us
  CpyUpd : ∀ {xs ys zs us ws ts a} {e₁ : ES (xs ++ zs) (xs ++ ws)} {e₂ : ES (xs ++ zs) (ys ++ us)} {p : e₁ ~ e₂} 
           ->  (x : View xs a) (y : View ys a) -> p ⇊ (ys ++ ts) -> CpyUpd x y p ⇊ (a ∷ ts)
  UpdCpy : ∀ {xs ys zs us ws ts a} {e₁ : ES (xs ++ zs) (ys ++ us)} {e₂ : ES (xs ++ zs) (xs ++ ws)} {p : e₁ ~ e₂} 
           -> (x : View xs a) (y : View ys a) -> p ⇊ (ys ++ ts) -> UpdCpy x y p ⇊ (a ∷ ts)
  Ins₁ : ∀ {xs ys zs us ws a} {e₁ : ES ys (xs ++ zs)} {e₂ : ES ys us} {p : e₁ ~ e₂} 
         -> (x : View xs a) -> p ⇊ (xs ++ ws) -> Ins₁ x p ⇊ (a ∷ ws)
  Ins₂ : ∀ {xs ys zs us ws a} {e₁ : ES ys us} {e₂ : ES ys (xs ++ zs)} {p : e₁ ~ e₂} 
         -> (x : View xs a) -> p ⇊ (xs ++ ws) -> Ins₂ x p ⇊ (a ∷ ws)

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
mergeSuff (CpyCpy x q) = Cpy x (mergeSuff q)
mergeSuff (DelDel x q) = Del x (mergeSuff q)
mergeSuff (DelCpy x q) = Del x (mergeSuff q)
mergeSuff (CpyDel x q) = Del x (mergeSuff q)
mergeSuff (CpyUpd x y q) = Upd x y (mergeSuff q)
mergeSuff (UpdCpy x y q) = Upd x y (mergeSuff q)
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
mergeNec (CpyCpy x p) (Cpy .x q) = CpyCpy x (mergeNec p q)
mergeNec (CpyDel x p) (Del .x q) = CpyDel x (mergeNec p q)
mergeNec (DelCpy x p) (Del .x q) = DelCpy x (mergeNec p q)
mergeNec (CpyUpd x y p) (Upd .x .y q) = CpyUpd x y (mergeNec p q)
mergeNec (UpdCpy x y p) (Upd .x .y q) = UpdCpy x y (mergeNec p q)
mergeNec (DelUpd x y p) ()
mergeNec (UpdDel x y p) ()
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
  Cpy : ∀ {e xs a} (x : View xs a) -> NoCnf e -> NoCnf (Cpy x e)
  Upd : ∀ {e xs ys a} (x : View xs a) (y : View ys a) -> NoCnf e -> NoCnf (Upd x y e) 

-- Well-typed implies no conflicts
diff3-wt : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} -> (p : e₁ ~ e₂) -> diff3 e₁ e₂ p ↓ ws -> NoCnf (diff3 e₁ e₂ p)
diff3-wt End End = End
diff3-wt (DelDel x p) (Del .x q) = Del x (diff3-wt p q)
diff3-wt (UpdUpd x y z p) q with y =?= z
diff3-wt (UpdUpd x y .y p) (Upd .x .y q) | yes refl = Upd x y (diff3-wt p q)
diff3-wt (UpdUpd x y z p) () | no ¬p
diff3-wt (CpyCpy x p) (Cpy .x q) = Cpy x (diff3-wt p q)
diff3-wt (CpyDel x p) (Del .x q) = Del x (diff3-wt p q)
diff3-wt (DelCpy x p) (Del .x q) = Del x (diff3-wt p q)
diff3-wt (CpyUpd x y p) (Upd .x .y q) = Upd x y (diff3-wt p q)
diff3-wt (UpdCpy x y p) (Upd .x .y q) = Upd x y (diff3-wt p q)
diff3-wt (DelUpd x y p) ()
diff3-wt (UpdDel x y p) ()
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
toES (CpyCpy x p) (Cpy .x q) = Cpy x (toES p q)
toES (CpyDel x p) (Del .x q) = Del x (toES p q)
toES (DelCpy x p) (Del .x q) = Del x (toES p q)
toES (CpyUpd x y p) (Upd .x .y q) = Upd x y (toES p q)
toES (UpdCpy x y p) (Upd .x .y q) = Upd x y (toES p q)
toES (DelUpd x y p) ()
toES (UpdDel x y p) ()
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
diff3-refl (Cpy x e) = Cpy x (diff3-refl e)
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
diff3-sym (CpyCpy x p) (Cpy .x q) = cong (Cpy x) (diff3-sym p q)
diff3-sym (CpyDel x p) (Del .x q) = cong (Del x) (diff3-sym p q)
diff3-sym (DelCpy x p) (Del .x q) = cong (Del x) (diff3-sym p q)
diff3-sym (CpyUpd x y p) (Upd .x .y q) = cong (Upd x y) (diff3-sym p q)
diff3-sym (UpdCpy x y p) (Upd .x .y q) = cong (Upd x y) (diff3-sym p q)
diff3-sym (DelUpd x y p) ()
diff3-sym (UpdDel x y p) ()
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

--------------------------------------------------------------------------------
