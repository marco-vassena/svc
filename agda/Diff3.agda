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
  Ins₁ : ∀ {xs ys zs us ws a} {e₁ : ES ys (xs ++ zs)} {e₂ : ES ys us} {p : e₁ ~ e₂} {{i : ¬Ins e₂}}
         -> (x : View xs a) -> p ⇊ (xs ++ ws) -> Ins₁ x p ⇊ (a ∷ ws)
  Ins₂ : ∀ {xs ys zs us ws a} {e₁ : ES ys us} {e₂ : ES ys (xs ++ zs)} {p : e₁ ~ e₂} {{i : ¬Ins e₁}} 
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

-- Refifies result of diff3
data Diff₃ : ∀ {xs ys zs ws} -> ES xs ys -> ES xs zs -> ES xs ws -> Set where
  End : Diff₃ End End End
  InsIns : ∀ {xs ys zs ws as a} {e₁ : ES xs (as ++ ys)} {e₂ : ES xs (as ++ zs)} {e₃ : ES xs (as ++ ws)}
           -> (x : View as a) -> Diff₃ e₁ e₂ e₃ -> Diff₃ (Ins x e₁) (Ins x e₂) (Ins x e₃)
  Ins₁ : ∀ {xs ys zs ws as a} {e₁ : ES xs (as ++ ys)} {e₂ : ES xs zs} {e₃ : ES xs (as ++ ws)} {{i : ¬Ins e₂}}
           -> (x : View as a) -> Diff₃ e₁ e₂ e₃ -> Diff₃ (Ins x e₁) e₂ (Ins x e₃)
  Ins₂ : ∀ {xs ys zs ws as a} {e₁ : ES xs ys} {e₂ : ES xs (as ++ zs)} {e₃ : ES xs (as ++ ws)} {{i : ¬Ins e₁}} 
           -> (x : View as a) -> Diff₃ e₁ e₂ e₃ -> Diff₃ e₁ (Ins x e₂) (Ins x e₃)
  DelDel : ∀ {xs ys zs ws as a} {e₁ : ES (as ++ xs) ys} {e₂ : ES (as ++ xs) zs} {e₃ : ES (as ++ xs) ws}
           -> (x : View as a) -> Diff₃ e₁ e₂ e₃ -> Diff₃ (Del x e₁) (Del x e₂) (Del x e₃)
  DelCpy : ∀ {xs ys zs ws as a} {e₁ : ES (as ++ xs) ys} {e₂ : ES (as ++ xs) (as ++ zs)} {e₃ : ES (as ++ xs) ws}
           ->  (x : View as a) -> Diff₃ e₁ e₂ e₃ -> Diff₃ (Del x e₁) (Cpy x e₂) (Del x e₃)
  CpyDel : ∀ {xs ys zs ws as a} {e₁ : ES (as ++ xs) (as ++ ys)} {e₂ : ES (as ++ xs) zs} {e₃ : ES (as ++ xs) ws}
           ->  (x : View as a) -> Diff₃ e₁ e₂ e₃ -> Diff₃ (Cpy x e₁) (Del x e₂) (Del x e₃)
  CpyCpy : ∀ {xs ys zs ws as a} {e₁ : ES (as ++ xs) (as ++ ys)} {e₂ : ES (as ++ xs) (as ++ zs)} {e₃ : ES (as ++ xs) (as ++ ws)}
           -> (x : View as a) -> Diff₃ e₁ e₂ e₃ -> Diff₃ (Cpy x e₁) (Cpy x e₂) (Cpy x e₃)
  CpyUpd : ∀ {xs ys zs ws as bs a} {e₁ : ES (as ++ xs) (as ++ ys)} {e₂ : ES (as ++ xs) (bs ++ zs)} {e₃ : ES (as ++ xs) (bs ++ ws)} 
           -> (x : View as a) (y : View bs a) -> Diff₃ e₁ e₂ e₃ -> Diff₃ (Cpy x e₁) (Upd x y e₂) (Upd x y e₃)
  UpdCpy : ∀ {xs ys zs ws as bs a} {e₁ : ES (as ++ xs) (bs ++ ys)} {e₂ : ES (as ++ xs) (as ++ zs)} {e₃ : ES (as ++ xs) (bs ++ ws)} 
           -> (x : View as a) (y : View bs a) -> Diff₃ e₁ e₂ e₃ -> Diff₃ (Upd x y e₁) (Cpy x e₂) (Upd x y e₃)
  UpdUpd : ∀ {xs ys zs ws as bs a} {e₁ : ES (as ++ xs) (bs ++ ys)} {e₂ : ES (as ++ xs) (bs ++ zs)} {e₃ : ES (as ++ xs) (bs ++ ws)} 
           -> (x : View as a) (y : View bs a) -> Diff₃ e₁ e₂ e₃ -> Diff₃ (Upd x y e₁) (Upd x y e₂) (Upd x y e₃)

-- Shows that a well typed diff3 corresponds to Diff3
diff₃-suf : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} -> (p : e₁ ~ e₂) ->
        let e₁₂ = diff3 e₁ e₂ p in (q : e₁₂ ↓ ws) -> Diff₃ e₁ e₂ (toES p q)
diff₃-suf End End = End
diff₃-suf (DelDel x p) (Del .x q) = DelDel x (diff₃-suf p q)
diff₃-suf (UpdUpd x y z p) q with y =?= z
diff₃-suf (UpdUpd x y .y p) (Upd .x .y q) | yes refl = UpdUpd x y (diff₃-suf p q)
diff₃-suf (UpdUpd x y z p) () | no ¬p
diff₃-suf (CpyCpy x p) (Cpy .x q) = CpyCpy x (diff₃-suf p q)
diff₃-suf (CpyDel x p) (Del .x q) = CpyDel x (diff₃-suf p q)
diff₃-suf (DelCpy x p) (Del .x q) = DelCpy x (diff₃-suf p q)
diff₃-suf (CpyUpd x y p) (Upd .x .y q) = CpyUpd x y (diff₃-suf p q)
diff₃-suf (UpdCpy x y p) (Upd .x .y q) = UpdCpy x y (diff₃-suf p q)
diff₃-suf (DelUpd x y p) ()
diff₃-suf (UpdDel x y p) ()
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
diff₃-nec (CpyCpy x p) (Cpy .x q) (CpyCpy .x d) = cong (Cpy x) (diff₃-nec p q d)
diff₃-nec (CpyDel x p) (Del .x q) (CpyDel .x d) = cong (Del x) (diff₃-nec p q d)
diff₃-nec (DelCpy x p) (Del .x q) (DelCpy .x d) = cong (Del x) (diff₃-nec p q d)
diff₃-nec (CpyUpd x y p) (Upd .x .y q) (CpyUpd .x .y d) = cong (Upd x y) (diff₃-nec p q d)
diff₃-nec (UpdCpy x y p) (Upd .x .y q) (UpdCpy .x .y d) = cong (Upd x y) (diff₃-nec p q d)
diff₃-nec (DelUpd x y p) () d
diff₃-nec (UpdDel x y p) () d
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

diff3~ : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} 
           -> Diff₃ e₁ e₂ e₃ -> e₁ ~ e₂
diff3~ End = End
diff3~ (InsIns x d) = InsIns x x (diff3~ d)
diff3~ (Ins₁ x d) = Ins₁ x (diff3~ d)
diff3~ (Ins₂ x d) = Ins₂ x (diff3~ d)
diff3~ (DelDel x d) = DelDel x (diff3~ d)
diff3~ (DelCpy x d) = DelCpy x (diff3~ d)
diff3~ (CpyDel x d) = CpyDel x (diff3~ d)
diff3~ (CpyCpy x d) = CpyCpy x (diff3~ d)
diff3~ (CpyUpd x y d) = CpyUpd x y (diff3~ d)
diff3~ (UpdCpy x y d) = UpdCpy x y (diff3~ d)
diff3~ (UpdUpd x y d) = UpdUpd x y y (diff3~ d)

diff3↓ : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} 
           -> (d : Diff₃ e₁ e₂ e₃) -> diff3 e₁ e₂ (diff3~ d) ↓ ws
diff3↓ End = End
diff3↓ (InsIns {a = a} x d) with eq? a a
diff3↓ (InsIns x d) | yes refl with x =?= x
diff3↓ (InsIns x d) | yes refl | yes refl = Ins x (diff3↓ d)
diff3↓ (InsIns x d) | yes refl | no ¬p = ⊥-elim (¬p refl)
diff3↓ (InsIns x d) | no ¬p = ⊥-elim (¬p refl)
diff3↓ (Ins₁ x d) = Ins x (diff3↓ d)
diff3↓ (Ins₂ x d) = Ins x (diff3↓ d)
diff3↓ (DelDel x d) = Del x (diff3↓ d)
diff3↓ (DelCpy x d) = Del x (diff3↓ d)
diff3↓ (CpyDel x d) = Del x (diff3↓ d)
diff3↓ (CpyCpy x d) = Cpy x (diff3↓ d)
diff3↓ (CpyUpd x y d) = Upd x y (diff3↓ d)
diff3↓ (UpdCpy x y d) = Upd x y (diff3↓ d)
diff3↓ (UpdUpd x y d) with y =?= y
diff3↓ (UpdUpd x y d) | yes refl = Upd x y (diff3↓ d)
diff3↓ (UpdUpd x y d) | no ¬p = ⊥-elim (¬p refl)

-- I would like to prove symmetricity of Diff₃ reusing diff3-sym
-- but at best I stumble upon ill-formed with clause
-- diff3-sym' : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} 
--              -> Diff₃ e₁ e₂ e₃ -> Diff₃ e₂ e₁ e₃
-- diff3-sym' d  with diff3~ d | diff3↓ d
-- ... | p | q with inspect (diff3 _ _) p | inspect (diff3 _ _) (~-sym p)
-- diff3-sym' d | p | q | Reveal_is_.[ refl ] | Reveal_is_.[ refl ] with diff₃-suf p q | diff₃-suf (~-sym p) (↓-sym p q)
-- ... | a | b with diff₃-nec p q a | diff₃-nec (~-sym p) (↓-sym p q) b
-- diff3-sym' d | p | q | Reveal_is_.[ refl ] | Reveal_is_.[ refl ] | a | b | refl | refl 
--   with diff₃-nec p q a | diff₃-nec (~-sym p) (↓-sym p q) b
-- diff3-sym' d | p | q | Reveal_is_.[ refl ] | Reveal_is_.[ refl ] | a | b | refl | refl | refl | refl = {!!}

-- diff3-sym' d | p | q | Reveal_is_.[ refl ] with inspect (toES p) q
-- diff3-sym' d | p | q | Reveal_is_.[ refl ] | Reveal_is_.[ refl ] with diff₃-nec p q d
-- ... | r = {!!}

-- with toES (diff3~ d) (diff3↓ d) | diff₃-nec (diff3~ d) (diff3↓ d) d
-- diff3-sym' d | e₃ | p with diff3-sym (diff3~ d) (diff3-wt (diff3~ d) (diff3↓ d)) 
-- ... | a = {!!}

Diff₃-sym : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} 
            -> Diff₃ e₁ e₂ e₃ -> Diff₃ e₂ e₁ e₃
Diff₃-sym End = End
Diff₃-sym (InsIns x d) = InsIns x (Diff₃-sym d)
Diff₃-sym (Ins₁ x d) = Ins₂ x (Diff₃-sym d)
Diff₃-sym (Ins₂ x d) = Ins₁ x (Diff₃-sym d)
Diff₃-sym (DelDel x d) = DelDel x (Diff₃-sym d)
Diff₃-sym (DelCpy x d) = CpyDel x (Diff₃-sym d)
Diff₃-sym (CpyDel x d) = DelCpy x (Diff₃-sym d)
Diff₃-sym (CpyCpy x d) = CpyCpy x (Diff₃-sym d)
Diff₃-sym (CpyUpd x y d) = UpdCpy x y (Diff₃-sym d)
Diff₃-sym (UpdCpy x y d) = CpyUpd x y (Diff₃-sym d)
Diff₃-sym (UpdUpd x y d) = UpdUpd x y (Diff₃-sym d)
