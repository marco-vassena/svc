module Diff where

open import DTree hiding ([_])
open import View
open import Data.List
open import Data.Product
open import Lemmas

data ES : (xs : List Set) (ys : List Set) -> Set₁ where
  Ins : ∀ {xs ys zs a} -> View xs a -> ES ys (xs ++ zs) -> ES ys (a ∷ zs)
  Del : ∀ {xs ys zs a} -> View xs a -> ES (xs ++ ys) zs -> ES (a ∷ ys) zs
  Cpy : ∀ {xs ys zs a} -> View xs a -> ES (xs ++ ys) (xs ++ zs) -> ES (a ∷ ys) (a ∷ zs)
  Upd : ∀ {xs ys ws zs a} -> (x : View xs a) -> (y : View ys a) -> ES (xs ++ zs) (ys ++ ws) -> ES (a ∷ zs) (a ∷ ws)
  End : ES [] []

-- Patch
⟦_⟧ : ∀ {xs ys} -> ES xs ys -> DList ys
⟦ Ins {xs} {zs = zs} x e ⟧ with dsplit ⟦ e ⟧
... | ds₁ , ds₂ = (Node x ds₁) ∷ ds₂
⟦ Del x e ⟧ = ⟦ e ⟧
⟦ Cpy {xs} {zs = zs} x e ⟧ with dsplit ⟦ e ⟧
... | ds₁ , ds₂ = (Node x ds₁) ∷ ds₂
⟦ Upd {ys = ys} {ws = ws} x y e ⟧ with dsplit ⟦ e ⟧
... | ds₁ , ds₂ = (Node y ds₁) ∷ ds₂
⟦ End ⟧ = []

--------------------------------------------------------------------------------
-- Edit abstracts over the concret edit operation

data Edit : List Set -> List Set -> List Set -> List Set -> Set₁ where
  Ins : ∀ {as a} -> View as a -> Edit [] as [] [ a ]
  Del : ∀ {as a} -> View as a -> Edit as [] [ a ] []
  Cpy : ∀ {as a} -> View as a -> Edit as as [ a ] [ a ]
  Upd : ∀ {xs ys a} -> (x : View xs a) -> (y : View ys a) -> Edit xs ys [ a ] [ a ]
  End : Edit [] [] [] []

-- Adds an edit in a well-typed script.
-- Well-typedness of ES is preserved 

_∻_ : ∀ {as bs cs ds xs ys} -> Edit as bs cs ds -> ES (as ++ xs) (bs ++ ys) -> ES (cs ++ xs) (ds ++ ys) 
(Ins x) ∻ es = Ins x es
(Del x) ∻ es = Del x es
(Cpy x) ∻ es = Cpy x es
(Upd x y) ∻ es = Upd x y es
End ∻ es = es

infixr 7 _∻_

--------------------------------------------------------------------------------
-- Classification of edits using types

open import Data.Empty
open import Data.Unit hiding (_≤_ ; _≤?_)

output : ∀ {as bs cs ds} -> Edit as bs cs ds -> Set
output (Ins x) = ⊤
output (Del x) = ⊥
output (Cpy x) = ⊤
output (Upd x x₁) = ⊤
output End = ⊥

outputArgs : ∀ {as bs cs ds} -> (e : Edit as bs cs ds) -> output e -> List Set
outputArgs {bs = bs} (Ins x) tt = bs
outputArgs (Del x) ()
outputArgs {as = as} (Cpy x) tt = as
outputArgs {bs = bs} (Upd x y) tt = bs
outputArgs End ()

outputTy : ∀ {as bs cs ds} -> (e : Edit as bs cs ds) -> output e -> Set
outputTy (Ins {a = a} x) tt = a
outputTy (Del x) ()
outputTy (Cpy {a = a} x) tt = a
outputTy (Upd {a = a} x y) tt = a
outputTy End ()

-- Returns the output View object
⌞_⌟ : ∀ {as bs cs ds} (e : Edit as bs cs ds) -> {{p : output e}} -> View (outputArgs e p) (outputTy e p)
⌞ Ins x ⌟ = x
⌞_⌟ (Del x) {{()}}
⌞ Cpy x ⌟ = x
⌞ Upd x y ⌟ = y
⌞_⌟ End {{()}}

--------------------------------------------------------------------------------

input : ∀ {as bs cs ds} -> Edit as bs cs ds -> Set
input (Ins x) = ⊥
input (Del x) = ⊤
input (Cpy x) = ⊤
input (Upd x y) = ⊤
input End = ⊥ 

inputTy : ∀ {as bs cs ds} -> (e : Edit as bs cs ds) -> {{p : input e}} -> Set
inputTy (Ins x) {{()}}
inputTy (Del {a = a} x) = a
inputTy (Cpy {a = a} x) = a
inputTy (Upd {a = a} x y) = a
inputTy End {{()}}

inputArgs : ∀ {as bs cs ds} -> (e : Edit as bs cs ds) -> {{p : input e}} -> List Set
inputArgs (Ins x) {{()}}
inputArgs (Del {as = as} x) = as
inputArgs (Cpy {as = as} x) = as
inputArgs (Upd {xs = xs} x y) = xs
inputArgs End {{()}}

⌜_⌝ : ∀ {as bs cs ds} -> (e : Edit as bs cs ds) -> {{p : input e}} -> View (inputArgs e) (inputTy e)
⌜_⌝ (Ins x) {{()}}
⌜ Del x ⌝ = x
⌜ Cpy x ⌝ = x
⌜ Upd x y ⌝ = x
⌜_⌝ End {{()}}

--------------------------------------------------------------------------------

-- The edit performs a change?
change : ∀ {as bs cs ds} -> Edit as bs cs ds -> Set
change (Ins x) = ⊤
change (Del x) = ⊤
change (Cpy x) = ⊥
change (Upd x y) = ⊤
change End = ⊥

--------------------------------------------------------------------------------
-- Membership

data _∈ₑ_ : ∀ {as bs cs ds xs ys} -> Edit as bs cs ds -> ES xs ys -> Set₁ where
  here : ∀ {as bs cs ds xs ys} {e : ES (as ++ xs) (bs ++ ys)} -> (c : Edit as bs cs ds) -> c ∈ₑ c ∻ e
  there : ∀ {as bs cs ds es fs gs hs xs ys} {c : Edit as bs cs ds} {e : ES (es ++ xs) (fs ++ ys)} (d : Edit es fs gs hs)
          -> c ∈ₑ e -> c ∈ₑ d ∻ e

infixl 3 _∈ₑ_

--------------------------------------------------------------------------------
-- Comes-before relation for edit scripts

data _⊢ₑ_⊏_ : ∀ {xs ys as bs cs ds es fs gs hs} -> ES xs ys -> Edit as bs cs ds -> Edit es fs gs hs -> Set₁ where
  here : ∀ {as bs cs ds es fs gs hs xs ys} {d : Edit es fs gs hs} {e : ES (as ++ xs) (bs ++ ys)} 
         -> (c : Edit as bs cs ds) -> (o : d ∈ₑ e) -> c ∻ e ⊢ₑ c ⊏ d 
  there : ∀ {as bs cs ds es fs gs hs is ls ms ns xs ys} {d : Edit es fs gs hs} {c : Edit as bs cs ds} {e : ES (is ++ xs) (ls ++ ys)}
          (a : Edit is ls ms ns) -> (o : e ⊢ₑ c ⊏ d) -> a ∻ e ⊢ₑ c ⊏ d 

infixl 3 _⊢ₑ_⊏_

--------------------------------------------------------------------------------
 
-- e₁ ~ e₂ is the proof that e₁ and e₂ are aligned, meaning that they e₁ and e₂ refer to the same
-- original tree. All the Del/Cpy constructors for each are appropriately paired.
data _~_ : ∀ {xs ys zs ws} -> (e₁ : ES xs ys) (e₂ : ES zs ws) -> Set₁ where
  End : End ~ End
  DelDel : ∀ {as xs ys zs a} {e₁ : ES (as ++ xs) ys} {e₂ : ES (as ++ xs) zs} (x : View as a) -> 
           e₁ ~ e₂ -> Del x e₁ ~ Del x e₂
  UpdUpd : ∀ {as bs cs xs ys zs a} (x : View as a) (y : View bs a) (z : View cs a)
           {e₁ : ES (as ++ xs) (bs ++ ys)} {e₂ : ES (as ++ xs) (cs ++ zs)} -> e₁ ~ e₂ -> Upd x y e₁ ~ Upd x z e₂
  CpyCpy : ∀ {xs ys zs as a} (x : View as a) {e₁ : ES (as ++ xs) (as ++ ys)} {e₂ : ES (as ++ xs) (as ++ zs)}
           -> e₁ ~ e₂ -> Cpy x e₁ ~ Cpy x e₂
  CpyDel : ∀ {xs ys zs as a} (x : View as a) {e₁ : ES (as ++ xs) (as ++ ys)} {e₂ : ES (as ++ xs) zs}
           -> e₁ ~ e₂ -> Cpy x e₁ ~ Del x e₂
  DelCpy : ∀ {xs ys zs as a} (x : View as a) {e₁ : ES (as ++ xs) ys} {e₂ : ES (as ++ xs) (as ++ zs)}
           -> e₁ ~ e₂ -> Del x e₁ ~ Cpy x e₂
  CpyUpd : ∀ {xs ys zs as bs a} (x : View as a) (y : View bs a) {e₁ : ES (as ++ xs) (as ++ ys)} {e₂ : ES (as ++ xs) (bs ++ zs)}
           -> e₁ ~ e₂ -> Cpy x e₁ ~ Upd x y e₂
  UpdCpy : ∀ {xs ys zs as bs a} (x : View as a) (y : View bs a) {e₁ : ES (as ++ xs) (bs ++ ys)} {e₂ : ES (as ++ xs) (as ++ zs)}
           -> e₁ ~ e₂ -> Upd x y e₁ ~ Cpy x e₂
  DelUpd : ∀ {as bs xs ys zs a} (x : View as a) (y : View bs a) 
           {e₁ : ES (as ++ xs) ys} {e₂ : ES (as ++ xs) (bs ++ zs)} -> e₁ ~ e₂ -> Del x e₁ ~ Upd x y e₂
  UpdDel : ∀ {as bs xs ys zs a} (x : View as a) (y : View bs a) 
           {e₁ : ES (as ++ xs) (bs ++ ys)} {e₂ : ES (as ++ xs) zs} -> e₁ ~ e₂ -> Upd x y e₁ ~ Del x e₂
  InsIns : ∀ {as bs xs ys zs a b} (x : View as a) (y : View bs b) 
           {e₁ : ES xs (as ++ ys)} {e₂ : ES xs (bs ++ zs)} -> e₁ ~ e₂ -> Ins x e₁ ~ Ins y e₂
  Ins₁ : ∀ {as xs ys zs a} (x : View as a) {e₁ : ES xs (as ++ ys)} {e₂ : ES xs zs} -> e₁ ~ e₂ -> Ins x e₁ ~ e₂
  Ins₂ : ∀ {as xs ys zs a} (x : View as a) {e₁ : ES xs ys} {e₂ : ES xs (as ++ zs)} -> e₁ ~ e₂ -> e₁ ~ Ins x e₂

-- The ~ relation is symmetric
~-sym : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES zs ws} -> e₁ ~ e₂ -> e₂ ~ e₁
~-sym End = End
~-sym (DelDel x p) = DelDel x (~-sym p)
~-sym (UpdUpd x y z p) = UpdUpd x z y (~-sym p)
~-sym (CpyCpy x p) = CpyCpy x (~-sym p)
~-sym (CpyDel x p) = DelCpy x (~-sym p)
~-sym (DelCpy x p) = CpyDel x (~-sym p)
~-sym (CpyUpd x y p) = UpdCpy x y (~-sym p)
~-sym (UpdCpy x y p) = CpyUpd x y (~-sym p)
~-sym (DelUpd x y p) = UpdDel x y (~-sym p)
~-sym (UpdDel x y p) = DelUpd x y (~-sym p)
~-sym (InsIns x y p) = InsIns y x (~-sym p)
~-sym (Ins₁ x p) = Ins₂ x (~-sym p)
~-sym (Ins₂ x p) = Ins₁ x (~-sym p)

-- The ~ relation is reflexive
~-refl : ∀ {xs ys} -> (e : ES xs ys) -> e ~ e
~-refl (Ins x e) = InsIns x x (~-refl e)
~-refl (Del x e) = DelDel x (~-refl e)
~-refl (Cpy x e) = CpyCpy x (~-refl e)
~-refl (Upd x y e) = UpdUpd x y y (~-refl e)
~-refl End = End

--------------------------------------------------------------------------------
-- Diff algorithm
--------------------------------------------------------------------------------

open import Data.Nat hiding (eq?)
open import Relation.Binary.PropositionalEquality

ins-size : ∀ {as zs ws us a n} (xs : DList zs) (ts₁ : DList ws) (y : View as a) (ys : DList as) (ts₂ : DList us) 
           -> size xs + size ts₁ + suc (size ys + size ts₂) ≤ n -> size (xs +++ ts₁) + suc (size ys + size ts₂) ≤ n
ins-size xs ts₁ x ys ts₂ p rewrite sym (size-+++ xs ts₁) = p

del-size : ∀ {as zs ws us a n} (xs : DList zs) (ts₁ : DList ws) (y : View as a) (ys : DList as) (ts₂ : DList us) 
           -> size xs + size ts₁ + suc (size ys + size ts₂) ≤ n -> suc (size xs + size ts₁ + size (ys +++ ts₂)) ≤ n
del-size xs ts₁ x ys ts₂ p rewrite 
    sym (size-+++ ys ts₂)
  | +-distr3 (size xs) (size ts₁) (size (ys +++ ts₂)) = p

upd-size : ∀ {as zs ws us a n} (xs : DList zs) (ts₁ : DList ws) (y : View as a) (ys : DList as) (ts₂ : DList us) 
         -> size xs + size ts₁ + suc (size ys + size ts₂) ≤ n -> size (xs +++ ts₁) + size (ys +++ ts₂) ≤ n
upd-size xs ts₁ x ys ts₂ p rewrite 
    sym (size-+++ xs ts₁) 
  | sym (size-+++ ys ts₂) = ≤-lemma (size (xs +++ ts₁)) (size (ys +++ ts₂)) p

-- Computes the length of an edit script.
cost : ∀ {xs ys} -> ES xs ys -> ℕ
cost (Ins x e) = 1 + cost e
cost (Del x e) = 1 + cost e
cost (Cpy x e) = cost e
cost (Upd x y e) = distance x y + cost e 
cost End = 0

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
sdiff [] [] z≤n = End
sdiff [] (Node y ys ∷ ts) (s≤s p) rewrite sym (size-+++ ys ts) = Ins y (sdiff [] (ys +++ ts) p)
sdiff (Node x xs ∷ ts) [] (s≤s p) rewrite sym (size-+++ xs ts) = Del x (sdiff (xs +++ ts) [] p)
sdiff {n = suc n} (Node {a = a} x xs ∷ ts₁) (Node {a = b} y ys ∷ ts₂) (s≤s p) 
  with eq? a b
sdiff {._} {._} {suc n} (Node x xs ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | yes refl with x =?= y
sdiff {._} {._} {suc n} (Node x xs ∷ ts₁) (Node .x ys ∷ ts₂) (s≤s p) | yes refl | yes refl 
  = Del x (sdiff (xs +++ ts₁) (Node x ys ∷ ts₂) (ins-size xs ts₁ x ys ts₂ p)) 
  ⨅ Ins x (sdiff (Node x xs ∷ ts₁) (ys +++ ts₂) (del-size xs ts₁ x ys ts₂ p))
  ⨅ Cpy x (sdiff (xs +++ ts₁) (ys +++ ts₂) (upd-size xs ts₁ x ys ts₂ p))
sdiff {._} {._} {suc n} (Node x xs ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | yes refl | no ¬p 
  = Del x (sdiff (xs +++ ts₁) (Node y ys ∷ ts₂) (ins-size xs ts₁ y ys ts₂ p)) 
  ⨅ Ins y (sdiff (Node x xs ∷ ts₁) (ys +++ ts₂) (del-size xs ts₁ y ys ts₂ p))
  ⨅ Upd x y (sdiff (xs +++ ts₁) (ys +++ ts₂) (upd-size xs ts₁ y ys ts₂ p))
sdiff {._} {._} {suc n} (Node x xs ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | no ¬p 
  = Del x (sdiff (xs +++ ts₁) (Node y ys ∷ ts₂) (ins-size xs ts₁ y ys ts₂ p)) 
  ⨅ Ins y (sdiff (Node x xs ∷ ts₁) (ys +++ ts₂) (del-size xs ts₁ y ys ts₂ p))
  

--     sdiff (xs +++ ts₁) (Node y ys ∷ ts₂) (ins-size xs ts₁ y ys ts₂ p)
--   | sdiff (Node x xs ∷ ts₁) (ys +++ ts₂) (del-size xs ts₁ y ys ts₂ p)
--   | sdiff (xs +++ ts₁) (ys +++ ts₂) (upd-size xs ts₁ y ys ts₂ p)
-- ... | i | d | u with eq? a b
-- sdiff {._} {._} {suc n} (Node x xs ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p₁) | d | i | u | yes refl with x =?= y
-- sdiff {._} {._} {suc n} (Node x xs ∷ ts₁) (Node .x ys ∷ ts₂) (s≤s p₁) | d | i | u | yes refl | yes refl = Cpy x u ⨅ Ins x i ⨅ Del x d
-- sdiff {._} {._} {suc n} (Node x xs ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p₁) | d | i | u | yes refl | no ¬p = Upd x y u ⨅ Ins y i ⨅ Del x d
-- sdiff {._} {._} {suc n} (Node x xs ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | d | i | u | no ¬p = Ins y i ⨅ Del x d

-- Computes the minimal-length edit-script.
-- It calls sdiff with an appropriate upper bound on the number of nodes. 
diff : ∀ {xs ys} -> DList xs -> DList ys -> ES xs ys
diff x y = sdiff {n = size x + size y} x y (≤-refl (size x + size y))

--------------------------------------------------------------------------------

-- data SkipTill : ∀ {xs ys as a} -> View as a -> ES xs ys -> Set₁ where
--   Del : ∀ {as a xs ys} -> (x : View as a) -> (e : ES (as ++ xs) ys) -> SkipTill x (Del x e)
--   Upd : ∀ {as bs a xs ys} -> (x : View as a) (y : View bs a) -> (e : ES (as ++ xs) (bs ++ ys)) -> SkipTill x (Upd x y e)
--   Cpy : ∀ {as a xs ys} -> (x : View as a) (e : ES (as ++ xs) (as ++ ys)) -> SkipTill x (Cpy x e)
--   Ins : ∀ {as bs a b xs ys} {x : View as a} (y : View bs b) (e : ES xs (bs ++ ys)) -> SkipTill x e -> SkipTill x (Ins y e)

data Diff : ∀ {xs ys} ->  DList xs -> DList ys -> ES xs ys -> Set₁ where
  End : Diff [] [] End
  Del : ∀ {as a xs ys} {e : ES (as ++ xs) ys} {ts₁ : DList as} {ts₂ : DList xs} {ts : DList ys}
        ->  (x : View as a) -> Diff (ts₁ +++ ts₂) ts e -> Diff (Node x ts₁ ∷ ts₂ ) ts (Del x e)
  Upd : ∀ {as bs a xs ys} {e : ES (as ++ xs) (bs ++ ys)} {ts₁ : DList as} {ts₂ : DList xs} {ts₃ : DList bs} {ts₄ : DList ys}
      -> (x : View as a) (y : View bs a) -> Diff (ts₁ +++ ts₂) (ts₃ +++ ts₄) e -> Diff (Node x ts₁ ∷ ts₂) (Node y ts₃ ∷ ts₄) (Upd x y e)
  Cpy : ∀ {as a xs ys} {e : ES (as ++ xs) (as ++ ys)} {ts₁ : DList as} {ts₂ : DList xs} {ts₃ : DList as} {ts₄ : DList ys}
        -> (x : View as a) -> Diff (ts₁ +++ ts₂) (ts₃ +++ ts₄) e -> Diff (Node x ts₁ ∷ ts₂) (Node x ts₃ ∷ ts₄) (Cpy x e)
  Ins : ∀ {bs b xs ys} {e : ES xs (bs ++ ys)} {ts₁ : DList xs} {ts₂ : DList bs} {ts₃ : DList ys}   
        -> (y : View bs b) -> Diff ts₁ (ts₂ +++ ts₃) e -> Diff ts₁ (Node y ts₂ ∷ ts₃) (Ins y e)

open import Data.Sum

lemma-⨅ : ∀ {xs ys} -> (e₁ : ES xs ys) (e₂ : ES xs ys) -> (e₁ ⨅ e₂) ≡ e₁ ⊎ (e₁ ⨅ e₂) ≡ e₂
lemma-⨅ e₁ e₂ with cost e₁ ≤? cost e₂
lemma-⨅ e₁ e₂ | yes p = inj₁ refl
lemma-⨅ e₁ e₂ | no ¬p = inj₂ refl

-- aligned : ∀ {xs ys n} -> (a : DList xs) (b : DList ys) (p : size a + size b ≤ n) -> Diff a b (sdiff a b p)
-- aligned a b p = {!!}

-- skipTill [] [] z≤n = End
-- skipTill [] (Node y ys ∷ b) (s≤s p) 
--   rewrite sym (size-+++ ys b) = Ins y (skipTill [] (ys +++ b) p)
-- skipTill (Node x xs ∷ a) [] (s≤s p)
--   rewrite sym (size-+++ xs a) = Del x (skipTill (xs +++ a) [] p)
-- skipTill (Node {a = a} x xs ∷ ts₁) (Node {a = b} y ys ∷ ts₂) (s≤s p) with eq? a b
-- skipTill (Node x xs ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | yes refl with x =?= y
-- skipTill (Node x xs ∷ ts₁) (Node .x ys ∷ ts₂) (s≤s p) | yes refl | yes refl = {!!}
-- skipTill (Node x xs ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | yes refl | no ¬p 
--   with   (sdiff (xs +++ ts₁) (Node y ys ∷ ts₂) (ins-size xs ts₁ y ys ts₂ p)) 
--        | (sdiff (Node x xs ∷ ts₁) (ys +++ ts₂) (del-size xs ts₁ y ys ts₂ p))
--        | (sdiff (xs +++ ts₁) (ys +++ ts₂) (upd-size xs ts₁ y ys ts₂ p))
-- ... | d | i | u with Del x d ⨅ Ins y i | lemma-⨅ (Del x d) (Ins y i)  
-- skipTill (Node x xs₄ ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | yes refl | no ¬p | d | i | u | r | q 
--   with r ⨅ Upd x y u | lemma-⨅ r (Upd x y u)
-- skipTill (Node x xs₄ ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | yes refl | no ¬p | d | i | u 
--   | .(Del x d) | inj₁ refl | .(Del x d) | inj₁ refl = Del x {!!}
-- skipTill (Node x xs₄ ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | yes refl | no ¬p | d | i | u | r | inj₂ y₁ | .r | inj₁ refl = {!!}
-- skipTill (Node x xs₄ ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | yes refl | no ¬p | d | i | u | r | q | r' | inj₂ y₁ = {!!}
-- skipTill (Node x xs ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | no ¬p 
--   with    (Del x (sdiff (xs +++ ts₁) (Node y ys ∷ ts₂) (ins-size xs ts₁ y ys ts₂ p))) 
--         ⨅ (Ins y (sdiff (Node x xs ∷ ts₁) (ys +++ ts₂) (del-size xs ts₁ y ys ts₂ p))) 
--    | lemma-⨅ (Del x (sdiff (xs +++ ts₁) (Node y ys ∷ ts₂) (ins-size xs ts₁ y ys ts₂ p))) 
--              (Ins y (sdiff (Node x xs ∷ ts₁) (ys +++ ts₂) (del-size xs ts₁ y ys ts₂ p))) 
-- skipTill (Node x xs ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | no ¬p | .(Del x _) | inj₁ refl 
--   = Del x (skipTill (xs +++ ts₁) (Node y ys ∷ ts₂) (ins-size xs ts₁ y ys ts₂ p))
-- skipTill (Node x xs ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | no ¬p | .(Ins y _) | inj₂ refl 
--   = Ins y (skipTill (Node x xs ∷ ts₁) (ys +++ ts₂) (del-size xs ts₁ y ys ts₂ p))
-- with eq? a b 
-- skipTill (Node x xs ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p₁) | i | d | u | yes refl = {!!}
-- skipTill (Node x xs ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | i | d | u | no ¬p 
--   with (Ins y d) ⨅ (Del x i) | lemma-⨅ (Ins y d) (Del x i) 
-- skipTill (Node x xs ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | i | d | u | no ¬p | .(Ins y d) | inj₁ refl = Ins y (skipTill (Node x xs ∷ ts₁) {!ys +++ ts₂!} {!p!})
-- skipTill (Node x xs₄ ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | i | d | u | no ¬p | .(Del x i) | inj₂ refl = {!!}

-- diff~ : ∀ {xs ys zs} -> (x : DList xs) (y : DList ys) (z : DList zs) -> diff x y ~ diff x z
-- diff~ x y z with inspect sdiff x  -- (sdiff x y (≤-refl (size x + size y))) 
--             | aligned x y (≤-refl (size x + size y)) 
--             | inspect {!!} {!!} -- (sdiff x z (≤-refl (size x + size z))) 
--             | aligned x z (≤-refl (size x + size z))
-- ... | a | b | c | d = {!!}
-- diff~ .[] .[] .[] | .End | End | .End | End = End
-- diff~ .[] .[] .(Node y ts₂ ∷ ts₃) | .End | End | Ins .y e | Ins {ts₂ = ts₂} {ts₃ = ts₃} y d = Ins₂ y (diff~ [] [] {!ts₂ +++ ts₃!})
-- diff~ ._ y z | ._ | Del x b | c | d = {!!}
-- diff~ ._ ._ z | ._ | Upd x y b | c | d = {!!}
-- diff~ ._ ._ z | ._ | Cpy x b | c | d = {!!}
-- diff~ x ._ z | ._ | Ins y b₁ | c | d = {!!}

sdiff[] : ∀ {ys zs n m} -> (y : DList ys) (z : DList zs) (p : size y ≤ n) (q : size z ≤ m) -> sdiff [] y p ~ sdiff [] z q
sdiff[] [] [] z≤n z≤n = End
sdiff[] {n = n} [] (Node y ys ∷ ts) z≤n (s≤s q) 
  rewrite sym (size-+++ ys ts) = Ins₂ y (sdiff[] {n = n} [] (ys +++ ts) z≤n q)
sdiff[] {m = m} (Node x xs ∷ ts) [] (s≤s p) z≤n 
  rewrite sym (size-+++ xs ts) = Ins₁ x (sdiff[] {m = m} (xs +++ ts) [] p z≤n)
sdiff[] (Node x xs ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) (s≤s q) 
  rewrite sym (size-+++ xs ts₁) | sym (size-+++ ys ts₂) = InsIns x y (sdiff[] (xs +++ ts₁) (ys +++ ts₂) p q)

lemma-⨅₃ : ∀ {xs ys} (e₁ : ES xs ys) (e₂ : ES xs ys) (e₃ : ES xs ys) -> 
           let e = e₁ ⨅ e₂ ⨅ e₃ in e ≡ e₁ ⊎ e ≡ e₂ ⊎ e ≡ e₃ 
lemma-⨅₃ e₁ e₂ e₃ with e₁ ⨅ e₂ | lemma-⨅ e₁ e₂
lemma-⨅₃ e₁ e₂ e₃ | .e₁ | inj₁ refl with e₁ ⨅ e₃ | lemma-⨅ e₁ e₃
lemma-⨅₃ e₁ e₂ e₃ | .e₁ | inj₁ refl | .e₁ | inj₁ refl = inj₁ refl
lemma-⨅₃ e₁ e₂ e₃ | .e₁ | inj₁ refl | .e₃ | inj₂ refl = inj₂ (inj₂ refl)
lemma-⨅₃ e₁ e₂ e₃ | .e₂ | inj₂ refl with e₂ ⨅ e₃ | lemma-⨅ e₂ e₃
lemma-⨅₃ e₁ e₂ e₃ | .e₂ | inj₂ refl | .e₂ | inj₁ refl = inj₂ (inj₁ refl)
lemma-⨅₃ e₁ e₂ e₃ | .e₂ | inj₂ refl | .e₃ | inj₂ refl = inj₂ (inj₂ refl)

-- zip~ : ∀ {xs ys zs n m} -> (x : DList xs) (y : DList ys) (z : DList zs) (p : size x + size y ≤ n) (q : size x + size z ≤ m) -> 
--      let e₀₁ = sdiff x y p 
--          e₀₂ = sdiff x z q in Diff x y e₀₁ -> Diff x z e₀₂ -> e₀₁ ~ e₀₂
-- zip~ [] [] [] z≤n z≤n End End = End
-- zip~ [] [] (Node x ts ∷ z) z≤n (s≤s q) End b with size ts + size z | sym (size-+++ ts z)
-- zip~ {n = n} [] [] (Node x₁ ts ∷ z) z≤n (s≤s q) End (Ins .x₁ b) | .(size (ts +++ z)) | refl 
--   = Ins₂ x₁ (zip~ {n = n} [] [] (ts +++ z) z≤n q End b)
-- zip~ [] (Node x₁ ts ∷ y) [] (s≤s p) z≤n a End with size ts + size y | sym (size-+++ ts y)
-- zip~ {m = m} [] (Node x₁ ts ∷ y) [] (s≤s p) z≤n (Ins .x₁ a) End | .(size (ts +++ y)) | refl 
--   = Ins₁ x₁ (zip~ {m = m} [] (ts +++ y) [] p z≤n a End)
-- zip~ [] (Node y ys ∷ ts₁) (Node z zs ∷ ts₂) (s≤s p) (s≤s q) a₂ b 
--   with   size ys + size ts₁ | sym (size-+++ ys ts₁) 
--        | size zs + size ts₂ | sym (size-+++ zs ts₂)
-- zip~ [] (Node y ys ∷ ts₁) (Node z zs ∷ ts₂) (s≤s p) (s≤s q) (Ins .y a₂) (Ins .z b₁) 
--   | .(size (ys +++ ts₁)) | refl | .(size (zs +++ ts₂)) | refl 
--   = InsIns y z (zip~ [] (ys +++ ts₁) (zs +++ ts₂) p q a₂ b₁)
-- zip~ (Node x xs ∷ ts) [] [] (s≤s p) (s≤s q) a₁ b with size xs + size ts | sym (size-+++ xs ts)
-- zip~ (Node x xs ∷ ts) [] [] (s≤s p) (s≤s q) (Del .x a) (Del .x b) | .(size (xs +++ ts)) | refl 
--   = DelDel x (zip~ (xs +++ ts) [] [] p q a b)
-- zip~ (Node {a = a₁} x xs ∷ ts₀) [] (Node {a = b₁} z zs ∷ ts₂) (s≤s p) (s≤s q) a b 
--   with eq? a₁ b₁ 
-- zip~ (Node x xs ∷ ts₀) [] (Node z zs ∷ ts₂) (s≤s p) (s≤s q) a₂ b | yes refl with x =?= z
-- zip~ (Node x xs ∷ ts₀) [] (Node .x zs ∷ ts₂) (s≤s p) (s≤s q) a₂ b | yes refl | yes refl = {!!}
-- zip~ (Node x xs ∷ ts₀) [] (Node z zs ∷ ts₂) (s≤s p) (s≤s q) a₂ b | yes refl | no ¬p 
--   with   (Del x (sdiff (xs +++ ts₀) (Node z zs ∷ ts₂) (ins-size xs ts₀ z zs ts₂ q)))
--        ⨅ (Ins z (sdiff (Node x xs ∷ ts₀) (zs +++ ts₂) (del-size xs ts₀ z zs ts₂ q))) 
--        ⨅ (Upd x z (sdiff (xs +++ ts₀) (zs +++ ts₂) (upd-size xs ts₀ z zs ts₂ q)))
--        | lemma-⨅₃ (Del x (sdiff (xs +++ ts₀) (Node z zs ∷ ts₂) (ins-size xs ts₀ z zs ts₂ q)))
--                   (Ins z (sdiff (Node x xs ∷ ts₀) (zs +++ ts₂) (del-size xs ts₀ z zs ts₂ q)))
--                   (Upd x z (sdiff (xs +++ ts₀) (zs +++ ts₂) (upd-size xs ts₀ z zs ts₂ q)))
-- zip~ (Node x xs₃ ∷ ts₀) [] (Node z zs ∷ ts₂) (s≤s p) (s≤s q) a₂ b | yes refl | no ¬p | .(Del x _) | inj₁ refl 
--   with size xs₃ + size ts₀ | sym (size-+++ xs₃ ts₀) 
-- zip~ (Node x xs₃ ∷ ts₀) [] (Node z zs ∷ ts₂) (s≤s p) (s≤s q) (Del .x a₂) (Del .x b) | yes refl | no ¬p | ._ | inj₁ refl | ._ | refl 
--   = DelDel x (zip~ (xs₃ +++ ts₀) [] (Node z zs ∷ ts₂) p q a₂ b)
-- zip~ (Node x xs₃ ∷ ts₀) [] (Node z zs ∷ ts₂) (s≤s p) (s≤s q) a₂ (Ins .z b) | yes refl | no ¬p | .(Ins z _) | inj₂ (inj₁ refl) 
--   with size zs + size ts₂ | sym (size-+++ zs ts₂)
-- zip~ (Node x xs₄ ∷ ts₀) [] (Node z zs ∷ ts₂) (s≤s p) (s≤s q) a₂ (Ins .z b) | yes refl | no ¬p | ._ | inj₂ (inj₁ refl) | ._ | refl 
--   rewrite +-distr3 (size xs₄) (size ts₀) (size (zs +++ ts₂)) 
-- -- Strange Error here ...
-- --   with size xs₄ + size ts₀ | sym (size-+++ xs₄ ts₀)
-- -- ... | r | t = {!!}
-- zip~ (Node x xs₃ ∷ ts₀) [] (Node z zs ∷ ts₂) (s≤s p) (s≤s q) a₂ b | yes refl | no ¬p | r | inj₂ (inj₂ y) = {!!}
-- zip~ (Node x xs ∷ ts₀) [] (Node z zs ∷ ts₂) (s≤s p) (s≤s q) a₂ b | no ¬p 
--   with   (Del x (sdiff (xs +++ ts₀) (Node z zs ∷ ts₂) (ins-size xs ts₀ z zs ts₂ q)))
--        ⨅ (Ins z (sdiff (Node x xs ∷ ts₀) (zs +++ ts₂) (del-size xs ts₀ z zs ts₂ q))) 
--     | lemma-⨅  (Del x (sdiff (xs +++ ts₀) (Node z zs ∷ ts₂) (ins-size xs ts₀ z zs ts₂ q)))
--                (Ins z (sdiff (Node x xs ∷ ts₀) (zs +++ ts₂) (del-size xs ts₀ z zs ts₂ q))) 
-- zip~ (Node x xs₂ ∷ ts₀) [] (Node z zs ∷ ts₂) (s≤s p) (s≤s q) a₂ (Del .x b) | no ¬p | .(Del x _) | inj₁ refl 
--   with size xs₂ + size ts₀ | sym (size-+++ xs₂ ts₀) 
-- zip~ (Node x xs ∷ ts₀) [] (Node z zs ∷ ts₂) (s≤s p) (s≤s q) (Del .x a) (Del .x b) | no ¬p | ._ | inj₁ refl | ._ | refl 
--   = DelDel x (zip~ (xs +++ ts₀) [] (Node z zs ∷ ts₂) p q a b)
-- zip~ (Node x xs₂ ∷ ts₀) [] (Node z zs ∷ ts₂) (s≤s p) (s≤s q) a₂ b | no ¬p | r | inj₂ y = {!!}
-- zip~ (t ∷ x₁) (t₁ ∷ y) [] p q a b = {!!}
-- zip~ (t ∷ x₁) (t₁ ∷ y) (t₂ ∷ z) p q a b = {!!}

-- sdiff~ : ∀ {xs ys zs n m} -> (x : DList xs) (y : DList ys) (z : DList zs) (p : size x + size y ≤ n) (q : size x + size z ≤ m) 
--        -> sdiff x y p ~ sdiff x z q
-- sdiff~ x y z p q =  zip~ x y z p q (aligned x y p) (aligned x z q)

-- sdiff~ [] y z p q = sdiff[] y z p q
-- sdiff~ (t ∷ x₁) [] z p q = {!!}
-- sdiff~ (t ∷ x₁) (t₁ ∷ y) [] p q = {!!}
-- sdiff~ (Node x xs ∷ ts₀) (Node y ys ∷ ts₁) (Node z zs ∷ ts₂) (s≤s p) (s≤s q) 
--   with   sdiff (Node x xs ∷ ts₀) (Node y ys ∷ ts₁) (s≤s p)
--        | aligned (Node x xs ∷ ts₀) (Node y ys ∷ ts₁) (s≤s p)
--        | sdiff (Node x xs ∷ ts₀) (Node z zs ∷ ts₂) (s≤s q)
--        | aligned (Node x xs ∷ ts₀) (Node z zs ∷ ts₂) (s≤s q)
-- sdiff~ (Node x₃ xs₅ ∷ ts₀) (Node y ys ∷ ts₁) (Node z zs ∷ ts₂) (s≤s p) (s≤s q) | ._ | Del .x₃ b | ._ | Del .x₃ d = DelDel x₃ (sdiff~ {!xs₅ +++ ts₀!} {!!} {!!} {!!} {!!})
-- sdiff~ (Node x₃ xs₅ ∷ ts₀) (Node y ys ∷ ts₁) (Node z zs ∷ ts₂) (s≤s p) (s≤s q) | ._ | Del .x₃ b | ._ | Upd .x₃ .z d = {!!}
-- sdiff~ (Node x₃ xs₅ ∷ ts₀) (Node y ys ∷ ts₁) (Node .x₃ zs ∷ ts₂) (s≤s p) (s≤s q) | ._ | Del .x₃ b | ._ | Cpy .x₃ d = {!!}
-- sdiff~ (Node x₃ xs₅ ∷ ts₀) (Node y ys ∷ ts₁) (Node z zs ∷ ts₂) (s≤s p) (s≤s q) | ._ | Del .x₃ b | ._ | Ins .z d = {!!}
-- sdiff~ (Node x₂ xs₄ ∷ ts₀) (Node y ys ∷ ts₁) (Node z zs ∷ ts₂) (s≤s p) (s≤s q) | ._ | Upd .x₂ .y b | c | d = {!!}
-- sdiff~ (Node x₂ xs₄ ∷ ts₀) (Node .x₂ ys ∷ ts₁) (Node z zs ∷ ts₂) (s≤s p) (s≤s q) | ._ | Cpy .x₂ b | c | d = {!!}
-- sdiff~ (Node x₁ xs₂ ∷ ts₀) (Node y ys ∷ ts₁) (Node z zs ∷ ts₂) (s≤s p) (s≤s q) | ._ | Ins .y b | c | d = {!!}


-- sdiff~ : ∀ {xs ys zs n m} -> (x : DList xs) (y : DList ys) (z : DList zs) 
--          -> (p : size x + size y ≤ n) (q : size x + size z ≤ m) -> sdiff x y p ~ sdiff x z q
-- sdiff~ [] y z p q = sdiff[] y z p q
-- sdiff~ (Node x xs ∷ ts) [] [] (s≤s p) (s≤s q) 
--   rewrite sym (size-+++ xs ts) = DelDel x (sdiff~ (xs +++ ts) [] [] p q)
-- sdiff~ (Node {a = a} x xs ∷ ts₀) [] (Node {a = b} z zs ∷ ts₂) (s≤s p) (s≤s q) with eq? a b 
-- sdiff~ (Node x xs ∷ ts₀) [] (Node z zs ∷ ts₂) (s≤s p) (s≤s q) | yes refl with x =?= z

-- sdiff~ (Node x xs ∷ ts₀) [] (Node .x zs ∷ ts₂) (s≤s p₁) (s≤s q) | yes refl | yes refl 
--   with (Del x (sdiff (xs +++ ts₀) (Node x zs ∷ ts₂) (ins-size xs ts₀ x zs ts₂ q)))
--        ⨅ (Ins x (sdiff (Node x xs ∷ ts₀) (zs +++ ts₂) (del-size xs ts₀ x zs ts₂ q)))
--        ⨅ (Cpy x  (sdiff (xs +++ ts₀) (zs +++ ts₂) (upd-size xs ts₀ x zs ts₂ q)))
--        | lemma-⨅₃ (Del x (sdiff (xs +++ ts₀) (Node x zs ∷ ts₂) (ins-size xs ts₀ x zs ts₂ q))) 
--                  (Ins x (sdiff (Node x xs ∷ ts₀) (zs +++ ts₂) (del-size xs ts₀ x zs ts₂ q)))
--                  (Cpy x (sdiff (xs +++ ts₀) (zs +++ ts₂) (upd-size xs ts₀ x zs ts₂ q)))
-- sdiff~ (Node x xs₂ ∷ ts₀) [] (Node .x zs ∷ ts₂) (s≤s p₁) (s≤s q) | yes refl | yes refl | .(Del x _) | inj₁ refl 
--   rewrite sym (size-+++ xs₂ ts₀) = DelDel x (sdiff~ (xs₂ +++ ts₀) [] (Node x zs ∷ ts₂) p₁ q)
-- sdiff~ (Node x xs₂ ∷ ts₀) [] (Node .x zs ∷ ts₂) (s≤s p₁) (s≤s q) | yes refl | yes refl | .(Ins x _) | inj₂ (inj₁ refl) 
--   rewrite sym (size-+++ zs ts₂) | +-distr3 (size xs₂) (size ts₀) (size (zs +++ ts₂)) 
--   = Ins₂ x (sdiff~ (Node x xs₂ ∷ ts₀) [] (zs +++ ts₂) (s≤s p₁) q)
-- sdiff~ (Node x xs ∷ ts₀) [] (Node .x zs ∷ ts₂) (s≤s p₁) (s≤s q) | yes refl | yes refl | .(Cpy x _) | inj₂ (inj₂ refl) 
--   rewrite sym (size-+++ xs ts₀) | sym (size-+++ zs ts₂) 
--   = DelCpy x (sdiff~ (xs +++ ts₀) [] (zs +++ ts₂) p₁ (≤-lemma (size (xs +++ ts₀)) (size (zs +++ ts₂)) q))

-- sdiff~ (Node x xs ∷ ts₀) [] (Node z zs ∷ ts₂) (s≤s p) (s≤s q) | yes refl | no ¬p   
--   with   (Del x (sdiff (xs +++ ts₀) (Node z zs ∷ ts₂) (ins-size xs ts₀ z zs ts₂ q)))
--        ⨅ (Ins z (sdiff (Node x xs ∷ ts₀) (zs +++ ts₂) (del-size xs ts₀ z zs ts₂ q)))
--        ⨅ (Upd x z  (sdiff (xs +++ ts₀) (zs +++ ts₂) (upd-size xs ts₀ z zs ts₂ q)))
--        | lemma-⨅₃ (Del x (sdiff (xs +++ ts₀) (Node z zs ∷ ts₂) (ins-size xs ts₀ z zs ts₂ q))) 
--                  (Ins z (sdiff (Node x xs ∷ ts₀) (zs +++ ts₂) (del-size xs ts₀ z zs ts₂ q)))
--                  (Upd x z (sdiff (xs +++ ts₀) (zs +++ ts₂) (upd-size xs ts₀ z zs ts₂ q)))
-- sdiff~ (Node x xs ∷ ts₀) [] (Node z zs ∷ ts₂) (s≤s p) (s≤s q) | yes refl | no ¬p | .(Del x _) | inj₁ refl 
--   rewrite sym (size-+++ xs ts₀) = DelDel x (sdiff~ (xs +++ ts₀) [] (Node z zs ∷ ts₂) p q)
-- sdiff~ (Node x xs ∷ ts₀) [] (Node z zs ∷ ts₂) (s≤s p) (s≤s q) | yes refl | no ¬p | .(Ins z _) | inj₂ (inj₁ refl) 
--   rewrite sym (size-+++ zs ts₂) | +-distr3 (size xs) (size ts₀) (size (zs +++ ts₂))
--   = Ins₂ z (sdiff~ (Node x xs ∷ ts₀) [] (zs +++ ts₂) (s≤s p) q)
-- sdiff~ (Node x xs ∷ ts₀) [] (Node z zs ∷ ts₂) (s≤s p) (s≤s q) | yes refl | no ¬p | .(Upd x z _) | inj₂ (inj₂ refl) 
--   rewrite sym (size-+++ xs ts₀) | sym (size-+++ zs ts₂)
--   = DelUpd x z (sdiff~ (xs +++ ts₀) [] (zs +++ ts₂) p (≤-lemma (size (xs +++ ts₀)) (size (zs +++ ts₂)) q))
-- sdiff~ (Node x xs ∷ ts₀) [] (Node z zs ∷ ts₂) (s≤s p) (s≤s q) | no ¬p 
--   with (Del x ((sdiff (xs +++ ts₀) (Node z zs ∷ ts₂) (ins-size xs ts₀ z zs ts₂ q))))
--        ⨅ (Ins z ( (sdiff (Node x xs ∷ ts₀) (zs +++ ts₂) (del-size xs ts₀ z zs ts₂ q))))
--        | lemma-⨅ (Del x ((sdiff (xs +++ ts₀) (Node z zs ∷ ts₂) (ins-size xs ts₀ z zs ts₂ q)))) 
--                  (Ins z ( (sdiff (Node x xs ∷ ts₀) (zs +++ ts₂) (del-size xs ts₀ z zs ts₂ q))))
-- sdiff~ (Node x xs₂ ∷ ts₀) [] (Node z zs ∷ ts₂) (s≤s p) (s≤s q) | no ¬p | .(Del x _) | inj₁ refl 
--   rewrite sym (size-+++ xs₂ ts₀) = DelDel x (sdiff~ (xs₂ +++ ts₀) [] (Node z zs ∷ ts₂) p q)
-- sdiff~ (Node x xs₂ ∷ ts₀) [] (Node z zs ∷ ts₂) (s≤s p) (s≤s q) | no ¬p | .(Ins z _) | inj₂ refl 
--   rewrite sym (size-+++ zs ts₂) | +-distr3 (size xs₂) (size ts₀) (size (zs +++ ts₂)) = Ins₂ z (sdiff~ (Node x xs₂ ∷ ts₀) [] (zs +++ ts₂) (s≤s p) q)
-- sdiff~ (Node x xs ∷ ts₀) (Node y ys ∷ ts₁) [] p q = {!!}
-- sdiff~ (Node {a = a} x xs ∷ ts₀) (Node {a = b} y ys ∷ ts₁) (Node {a = c} z zs ∷ ts₂) (s≤s p) (s≤s q) with eq? a b | eq? a c
-- sdiff~ (Node x xs₂ ∷ ts₀) (Node y ys ∷ ts₁) (Node z zs ∷ ts₂) (s≤s p₂) (s≤s q) | yes p | yes p₁ = {!!}
-- sdiff~ (Node x xs₂ ∷ ts₀) (Node y ys ∷ ts₁) (Node z zs ∷ ts₂) (s≤s p₁) (s≤s q) | yes p | no ¬p = {!!}
-- sdiff~ (Node x xs₂ ∷ ts₀) (Node y ys ∷ ts₁) (Node z zs ∷ ts₂) (s≤s p₁) (s≤s q) | no ¬p | yes p = {!!}
-- sdiff~ (Node x xs ∷ ts₀) (Node y ys ∷ ts₁) (Node z zs ∷ ts₂) (s≤s p) (s≤s q) | no ¬p | no ¬p₁ 
--   with   (Del x ((sdiff (xs +++ ts₀) (Node z zs ∷ ts₂) (ins-size xs ts₀ z zs ts₂ q))))
--        ⨅ (Ins z ((sdiff (Node x xs ∷ ts₀) (zs +++ ts₂) (del-size xs ts₀ z zs ts₂ q))))
--        | lemma-⨅ (Del x ((sdiff (xs +++ ts₀) (Node z zs ∷ ts₂) (ins-size xs ts₀ z zs ts₂ q)))) 
--                  (Ins z ( (sdiff (Node x xs ∷ ts₀) (zs +++ ts₂) (del-size xs ts₀ z zs ts₂ q))))
--        | (Del x ((sdiff (xs +++ ts₀) (Node y ys ∷ ts₁) (ins-size xs ts₀ y ys ts₁ p))))
--        ⨅ (Ins y ((sdiff (Node x xs ∷ ts₀) (ys +++ ts₁) (del-size xs ts₀ y ys ts₁ p))))
--        | lemma-⨅ (Del x ((sdiff (xs +++ ts₀) (Node y ys ∷ ts₁) (ins-size xs ts₀ y ys ts₁ p)))) 
--                  (Ins y ((sdiff (Node x xs ∷ ts₀) (ys +++ ts₁) (del-size xs ts₀ y ys ts₁ p))))
-- sdiff~ (Node x xs₂ ∷ ts₀) (Node y ys ∷ ts₁) (Node z zs ∷ ts₂) (s≤s p) (s≤s q) | no ¬p | no ¬p₁ | a₃ | inj₁ x₁ | c | inj₁ x₂ = {!!}
-- sdiff~ (Node x xs₂ ∷ ts₀) (Node y ys ∷ ts₁) (Node z zs ∷ ts₂) (s≤s p) (s≤s q) | no ¬p | no ¬p₁ | a₃ | inj₁ x₁ | c | inj₂ y₁ = {!!}
-- sdiff~ (Node x xs₂ ∷ ts₀) (Node y ys ∷ ts₁) (Node z zs ∷ ts₂) (s≤s p) (s≤s q) | no ¬p | no ¬p₁ | a₃ | inj₂ y₁ | c | inj₁ x₁ = {!!}
-- sdiff~ (Node x xs₂ ∷ ts₀) (Node y ys ∷ ts₁) (Node z zs ∷ ts₂) (s≤s p) (s≤s q) | no ¬p | no ¬p₁ | a₃ | inj₂ y₁ | c | inj₂ y₂ = {!!}

--------------------------------------------------------------------------------

-- data SameOrder : ∀ {xs ys} -> DList xs -> ES xs ys -> Set₁ where
--   End : SameOrder [] End
--   Del : ∀ {xs as ys a} {ts₁ : DList as} {ts₂ : DList xs} {x : View as a} 
--           {e : ES (as ++ xs) ys} -> SameOrder (ts₁ +++ ts₂) e -> SameOrder (Node x ts₁ ∷ ts₂) (Del x e) 
--   Upd : ∀ {xs as bs ys a} {ts₁ : DList as} {ts₂ : DList xs} {x : View as a} {y : View bs a} 
--           {e : ES (as ++ xs) (bs ++ ys)} -> SameOrder (ts₁ +++ ts₂) e -> SameOrder (Node x ts₁ ∷ ts₂) (Upd x y e) 
--   Cpy : ∀ {xs as ys a} {ts₁ : DList as} {ts₂ : DList xs} {x : View as a} 
--           {e : ES (as ++ xs) (as ++ ys)} -> SameOrder (ts₁ +++ ts₂) e -> SameOrder (Node x ts₁ ∷ ts₂) (Cpy x e) 
--   Ins : ∀ {xs as ys a} {ts : DList xs} {x : View as a} 
--           {e : ES xs (as ++ ys)} -> SameOrder ts e -> SameOrder ts (Ins x e) 

-- order-lemma : ∀ {xs ys n} -> (x : DList xs) (y : DList ys) (p : size x + size y ≤ n) -> SameOrder x (sdiff x y p)
-- order-lemma [] [] z≤n = End
-- order-lemma [] (Node y ys ∷ ts) (s≤s p) 
--   rewrite sym (size-+++ ys ts) = Ins (order-lemma [] (ys +++ ts) p)
-- order-lemma (Node x₁ xs₂ ∷ ts) [] (s≤s p) 
--   rewrite sym (size-+++ xs₂ ts) = Del (order-lemma (xs₂ +++ ts) [] p)
-- order-lemma (Node {a = a} x xs ∷ ts₁) (Node {a = b} y ys ∷ ts₂) (s≤s p) with eq? a b
-- order-lemma (Node x xs ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | yes refl with x =?= y
-- order-lemma (Node x xs ∷ ts₁) (Node .x ys ∷ ts₂) (s≤s p) | yes refl | yes refl 
--   with (Del x (sdiff (xs +++ ts₁) (Node x ys ∷ ts₂) (ins-size xs ts₁ x ys ts₂ p)))
--        ⨅ (Ins x (sdiff (Node x xs ∷ ts₁) (ys +++ ts₂) (del-size xs ts₁ x ys ts₂ p)))
--        ⨅ (Cpy x  (sdiff (xs +++ ts₁) (ys +++ ts₂) (upd-size xs ts₁ x ys ts₂ p)))
--        | lemma-⨅₃ (Del x (sdiff (xs +++ ts₁) (Node x ys ∷ ts₂) (ins-size xs ts₁ x ys ts₂ p)))
--                   (Ins x (sdiff (Node x xs ∷ ts₁) (ys +++ ts₂) (del-size xs ts₁ x ys ts₂ p)))
--                   (Cpy x  (sdiff (xs +++ ts₁) (ys +++ ts₂) (upd-size xs ts₁ x ys ts₂ p)))
-- order-lemma (Node x xs₂ ∷ ts₁) (Node .x ys ∷ ts₂) (s≤s p) | yes refl | yes refl | .(Del x _) | inj₁ refl 
--   rewrite sym (size-+++ xs₂ ts₁) = Del (order-lemma (xs₂ +++ ts₁) (Node x ys ∷ ts₂) p)
-- order-lemma (Node x xs₂ ∷ ts₁) (Node .x ys ∷ ts₂) (s≤s p) | yes refl | yes refl | .(Ins x _) | inj₂ (inj₁ refl) 
--   rewrite sym (size-+++ ys ts₂) | +-distr3 (size xs₂) (size ts₁) (size (ys +++ ts₂)) 
--   = Ins (order-lemma (Node x xs₂ ∷ ts₁) (ys +++ ts₂) p)
-- order-lemma (Node x xs₂ ∷ ts₁) (Node .x ys ∷ ts₂) (s≤s p) | yes refl | yes refl | .(Cpy x _) | inj₂ (inj₂ refl) 
--   rewrite sym (size-+++ xs₂ ts₁) | sym (size-+++ ys ts₂) 
--   = Cpy (order-lemma (xs₂ +++ ts₁) (ys +++ ts₂) (≤-lemma (size (xs₂ +++ ts₁)) (size (ys +++ ts₂)) p))
-- order-lemma (Node x xs ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | yes refl | no ¬p = {!!}
-- order-lemma (Node x xs ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | no ¬p = {!!}

-- -- This version doesn't work because to pattern-match over order-lemma I need to abstract
-- -- over sdiff preventing the recursive call.
-- sdiff~ : ∀ {xs ys zs n m} -> (x : DList xs) (y : DList ys) (z : DList zs) 
--          -> (p : size x + size y ≤ n) (q : size x + size z ≤ m) -> sdiff x y p ~ sdiff x z q
-- sdiff~ x y z p q with sdiff x y p | order-lemma x y p | sdiff x z q | order-lemma x z q
-- sdiff~ .[] y z p q | .End | End | .End | End = End
-- sdiff~ .[] y z p q | .End | End | ._ | Ins d = Ins₂ _ {!!}
-- sdiff~ ._ y z p q | ._ | Del b | ._ | Del d = DelDel _ (sdiff~ {!!} {!!} {!!} {!!} {!!})
-- sdiff~ ._ y z p q | ._ | Del b | ._ | Upd d = {!!}
-- sdiff~ ._ y z p q | ._ | Del b | ._ | Cpy d = {!!}
-- sdiff~ ._ y z p q | ._ | Del b | ._ | Ins d = {!!}
-- sdiff~ ._ y z p q | ._ | Upd b | c | d = {!!}
-- sdiff~ ._ y z p q | ._ | Cpy b | c | d = {!!}
-- sdiff~ x y z p q | ._ | Ins b | c | d = {!!}

--------------------------------------------------------------------------------
