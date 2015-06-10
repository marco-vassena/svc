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

outputArgs : ∀ {as bs cs ds} -> (e : Edit as bs cs ds) -> {{p : output e}} -> List Set
outputArgs {bs = bs} (Ins x) = bs
outputArgs (Del x) {{()}}
outputArgs {as = as} (Cpy x) = as
outputArgs {bs = bs} (Upd x y) = bs
outputArgs End {{()}}

outputTy : ∀ {as bs cs ds} -> (e : Edit as bs cs ds) -> {{o : output e}} -> Set
outputTy (Ins {a = a} x) = a
outputTy (Del x) {{()}}
outputTy (Cpy {a = a} x) = a
outputTy (Upd {a = a} x y) = a
outputTy End {{()}}

-- Returns the output View object
⌞_⌟ : ∀ {as bs cs ds} (e : Edit as bs cs ds) -> {{p : output e}} -> View (outputArgs e) (outputTy e)
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
 
¬Ins : ∀ {xs ys} -> ES xs ys -> Set
¬Ins (Ins x e) = ⊥
¬Ins (Del x e) = ⊤
¬Ins (Cpy x e) = ⊤
¬Ins (Upd x y e) = ⊤
¬Ins End = ⊤

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
  Ins₁ : ∀ {as xs ys zs a} {e₁ : ES xs (as ++ ys)} {e₂ : ES xs zs} {{i : ¬Ins e₂}} (x : View as a) -> e₁ ~ e₂ -> Ins x e₁ ~ e₂
  Ins₂ : ∀ {as xs ys zs a} {e₁ : ES xs ys} {e₂ : ES xs (as ++ zs)} {{i : ¬Ins e₁}} (x : View as a) -> e₁ ~ e₂ -> e₁ ~ Ins x e₂

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

del-size : ∀ {as zs ws us a n} (xs : DList zs) (ts₁ : DList ws) (y : View as a) (ys : DList as) (ts₂ : DList us) 
           -> size xs + size ts₁ + suc (size ys + size ts₂) ≤ n -> size (xs +++ ts₁) + suc (size ys + size ts₂) ≤ n
del-size xs ts₁ x ys ts₂ p rewrite sym (size-+++ xs ts₁) = p

ins-size : ∀ {as zs ws us a n} (xs : DList zs) (ts₁ : DList ws) (y : View as a) (ys : DList as) (ts₂ : DList us) 
           -> size xs + size ts₁ + suc (size ys + size ts₂) ≤ n -> suc (size xs + size ts₁ + size (ys +++ ts₂)) ≤ n
ins-size xs ts₁ x ys ts₂ p rewrite 
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
  = Del x (sdiff (xs +++ ts₁) (Node x ys ∷ ts₂) (del-size xs ts₁ x ys ts₂ p)) 
  ⨅ Ins x (sdiff (Node x xs ∷ ts₁) (ys +++ ts₂) (ins-size xs ts₁ x ys ts₂ p))
  ⨅ Cpy x (sdiff (xs +++ ts₁) (ys +++ ts₂) (upd-size xs ts₁ x ys ts₂ p))
sdiff {._} {._} {suc n} (Node x xs ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | yes refl | no ¬p 
  = Del x (sdiff (xs +++ ts₁) (Node y ys ∷ ts₂) (del-size xs ts₁ y ys ts₂ p)) 
  ⨅ Ins y (sdiff (Node x xs ∷ ts₁) (ys +++ ts₂) (ins-size xs ts₁ y ys ts₂ p))
  ⨅ Upd x y (sdiff (xs +++ ts₁) (ys +++ ts₂) (upd-size xs ts₁ y ys ts₂ p))
sdiff {._} {._} {suc n} (Node x xs ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | no ¬p 
  = Del x (sdiff (xs +++ ts₁) (Node y ys ∷ ts₂) (del-size xs ts₁ y ys ts₂ p)) 
  ⨅ Ins y (sdiff (Node x xs ∷ ts₁) (ys +++ ts₂) (ins-size xs ts₁ y ys ts₂ p))

-- Computes the minimal-length edit-script.
-- It calls sdiff with an appropriate upper bound on the number of nodes. 
diff : ∀ {xs ys} -> DList xs -> DList ys -> ES xs ys
diff x y = sdiff {n = size x + size y} x y (≤-refl (size x + size y))

--------------------------------------------------------------------------------

data Diff : ∀ {xs ys} ->  DList xs -> DList ys -> ES xs ys -> Set₁ where
  End : Diff [] [] End
  Del : ∀ {as a xs ys} {e : ES (as ++ xs) ys} {ts₁ : DList as} {ts₂ : DList xs} {ts : DList ys}
        ->  (x : View as a) -> Diff (ts₁ +++ ts₂) ts e -> Diff (Node x ts₁ ∷ ts₂ ) ts (Del x e)
  Upd : ∀ {as bs a xs ys} {e : ES (as ++ xs) (bs ++ ys)} {ts₁ : DList as} {ts₂ : DList xs} {ts₃ : DList bs} {ts₄ : DList ys}
      -> (x : View as a) (y : View bs a) -> Diff (ts₁ +++ ts₂) (ts₃ +++ ts₄) e 
      -> Diff (Node x ts₁ ∷ ts₂) (Node y ts₃ ∷ ts₄) (Upd x y e)
  Cpy : ∀ {as a xs ys} {e : ES (as ++ xs) (as ++ ys)} {ts₁ : DList as} {ts₂ : DList xs} {ts₃ : DList as} {ts₄ : DList ys}
        -> (x : View as a) -> Diff (ts₁ +++ ts₂) (ts₃ +++ ts₄) e -> Diff (Node x ts₁ ∷ ts₂) (Node x ts₃ ∷ ts₄) (Cpy x e)
  Ins : ∀ {bs b xs ys} {e : ES xs (bs ++ ys)} {ts₁ : DList xs} {ts₂ : DList bs} {ts₃ : DList ys}   
        -> (y : View bs b) -> Diff ts₁ (ts₂ +++ ts₃) e -> Diff ts₁ (Node y ts₂ ∷ ts₃) (Ins y e)

open import Data.Sum

lemma-⨅ : ∀ {xs ys} -> (e₁ : ES xs ys) (e₂ : ES xs ys) -> (e₁ ⨅ e₂) ≡ e₁ ⊎ (e₁ ⨅ e₂) ≡ e₂
lemma-⨅ e₁ e₂ with cost e₁ ≤? cost e₂
lemma-⨅ e₁ e₂ | yes p = inj₁ refl
lemma-⨅ e₁ e₂ | no ¬p = inj₂ refl

-- Retrieves the source from the edit script
⟪_⟫ : ∀ {xs ys} -> ES xs ys -> DList xs
⟪ Ins x e ⟫ = ⟪ e ⟫
⟪ Del x e ⟫ with dsplit ⟪ e ⟫
... | ds₁ , ds₂ = (Node x ds₁) ∷ ds₂
⟪ Cpy x e ⟫ with dsplit ⟪ e ⟫
... | ds₁ , ds₂ = (Node x ds₁) ∷ ds₂
⟪ Upd x y e ⟫ with dsplit ⟪ e ⟫
... | ds₁ , ds₂ = Node x ds₁ ∷ ds₂
⟪ End ⟫ = []

-- Once more we need to have an explicit mapping with dsplit.
-- Simple rewriting fails because (probably), the underlying with clause becomes ill-typed.
Diff-⟦⟧ : ∀ {xs} {{ys zs}} {t₀ : DList xs} (e : ES xs (ys ++ zs)) ->
              let ds₁ , ds₂ = dsplit ⟦ e ⟧ in Diff t₀ ⟦ e ⟧ e -> Diff t₀ (ds₁ +++ ds₂) e
Diff-⟦⟧ e d 
  rewrite dsplit-lemma ⟦ e ⟧ = d

Diff-⟪⟫ : ∀ {{xs ys}} {zs} {t₁ : DList zs} (e : ES (xs ++ ys) zs) ->
              let ds₁ , ds₂ = dsplit ⟪ e ⟫ in Diff ⟪ e ⟫ t₁ e -> Diff (ds₁ +++ ds₂) t₁ e
Diff-⟪⟫ e d 
  rewrite dsplit-lemma ⟪ e ⟫ = d

-- Relation between Diff, ⟦_⟧ and ⟪_⟫
mkDiff : ∀ {xs ys} (e : ES xs ys) -> Diff ⟪ e ⟫ ⟦ e ⟧ e
mkDiff (Ins x e) with dsplit ⟦ e ⟧
... | ds₁ , ds₂ = Ins x (Diff-⟦⟧ e (mkDiff e))
mkDiff (Del x e) with dsplit ⟪ e ⟫
... | ds₁ , ds₂ = Del x (Diff-⟪⟫ e (mkDiff e))
mkDiff (Cpy x e) with dsplit ⟪ e ⟫ 
... | r = Cpy x (Diff-⟦⟧ e (Diff-⟪⟫ e (mkDiff e)))
mkDiff (Upd x y e) with dsplit ⟪ e ⟫
... | r = Upd x y (Diff-⟦⟧ e (Diff-⟪⟫ e (mkDiff e)))
mkDiff End = End

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
Diff-suf' (Node x xs₂ ∷ a₂) (Node y ys ∷ b) (s≤s p₁) | yes refl with x =?= y
Diff-suf' (Node x xs ∷ ts₁) (Node .x ys ∷ ts₂) (s≤s p) | yes refl | yes refl 
  with     Del x (sdiff (xs +++ ts₁) (Node x ys ∷ ts₂) (del-size xs ts₁ x ys ts₂ p)) 
         ⨅ Ins x (sdiff (Node x xs ∷ ts₁) (ys +++ ts₂) (ins-size xs ts₁ x ys ts₂ p))
         ⨅ Cpy x (sdiff (xs +++ ts₁) (ys +++ ts₂) (upd-size xs ts₁ x ys ts₂ p))
       | lemma-⨅₃ (Del x (sdiff (xs +++ ts₁) (Node x ys ∷ ts₂) (del-size xs ts₁ x ys ts₂ p))) 
                (Ins x (sdiff (Node x xs ∷ ts₁) (ys +++ ts₂) (ins-size xs ts₁ x ys ts₂ p)))
                (Cpy x (sdiff (xs +++ ts₁) (ys +++ ts₂) (upd-size xs ts₁ x ys ts₂ p)))
Diff-suf' (Node x xs ∷ ts₁) (Node .x ys ∷ ts₂) (s≤s p) | yes refl | yes refl | .(Del x _) | inj₁ refl 
  = Del x (Diff-suf' (xs +++ ts₁) (Node x ys ∷ ts₂) (del-size xs ts₁ x ys ts₂ p))
Diff-suf' (Node x xs₂ ∷ ts₁) (Node .x ys ∷ ts₂) (s≤s p) | yes refl | yes refl | .(Ins x _) | inj₂ (inj₁ refl) 
  = Ins x (Diff-suf' (Node x xs₂ ∷ ts₁) (ys +++ ts₂) (ins-size xs₂ ts₁ x ys ts₂ p))
Diff-suf' (Node x xs₂ ∷ ts₁) (Node .x ys ∷ ts₂) (s≤s p) | yes refl | yes refl | .(Cpy x _) | inj₂ (inj₂ refl) 
  = Cpy x (Diff-suf' (xs₂ +++ ts₁) (ys +++ ts₂) (upd-size xs₂ ts₁ x ys ts₂ p))
Diff-suf' (Node x xs ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | yes refl | no ¬p 
  with     Del x (sdiff (xs +++ ts₁) (Node y ys ∷ ts₂) (del-size xs ts₁ y ys ts₂ p)) 
         ⨅ Ins y (sdiff (Node x xs ∷ ts₁) (ys +++ ts₂) (ins-size xs ts₁ y ys ts₂ p))
         ⨅ Upd x y (sdiff (xs +++ ts₁) (ys +++ ts₂) (upd-size xs ts₁ y ys ts₂ p))
       | lemma-⨅₃ (Del x (sdiff (xs +++ ts₁) (Node y ys ∷ ts₂) (del-size xs ts₁ y ys ts₂ p)))
                  (Ins y (sdiff (Node x xs ∷ ts₁) (ys +++ ts₂) (ins-size xs ts₁ y ys ts₂ p)))
                  (Upd x y (sdiff (xs +++ ts₁) (ys +++ ts₂) (upd-size xs ts₁ y ys ts₂ p)))
Diff-suf' (Node x xs ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | yes refl | no ¬p | .(Del x _) | inj₁ refl 
  = Del x (Diff-suf' (xs +++ ts₁) (Node y ys ∷ ts₂) (del-size xs ts₁ y ys ts₂ p))
Diff-suf' (Node x xs₃ ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | yes refl | no ¬p | .(Ins y _) | inj₂ (inj₁ refl) 
  = Ins y (Diff-suf' (Node x xs₃ ∷ ts₁) (ys +++ ts₂) (ins-size xs₃ ts₁ y ys ts₂ p))
Diff-suf' (Node x xs₃ ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | yes refl | no ¬p | .(Upd x y _) | inj₂ (inj₂ refl) 
  = Upd x y (Diff-suf' (xs₃ +++ ts₁) (ys +++ ts₂) (upd-size xs₃ ts₁ y ys ts₂ p))
Diff-suf' (Node x xs ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | no ¬p with
        Del x (sdiff (xs +++ ts₁) (Node y ys ∷ ts₂) (del-size xs ts₁ y ys ts₂ p)) 
      ⨅ Ins y (sdiff (Node x xs ∷ ts₁) (ys +++ ts₂) (ins-size xs ts₁ y ys ts₂ p))
    | lemma-⨅ (Del x (sdiff (xs +++ ts₁) (Node y ys ∷ ts₂) (del-size xs ts₁ y ys ts₂ p)))
              (Ins y (sdiff (Node x xs ∷ ts₁) (ys +++ ts₂) (ins-size xs ts₁ y ys ts₂ p)))
Diff-suf' (Node x xs₂ ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | no ¬p | .(Del x _) | inj₁ refl 
  = Del x (Diff-suf' (xs₂ +++ ts₁) (Node y ys ∷ ts₂) (del-size xs₂ ts₁ y ys ts₂ p))
Diff-suf' (Node x xs₂ ∷ ts₁) (Node y ys ∷ ts₂) (s≤s p) | no ¬p | .(Ins y _) | inj₂ refl 
  = Ins y (Diff-suf' (Node x xs₂ ∷ ts₁) (ys +++ ts₂) (ins-size xs₂ ts₁ y ys ts₂ p))

-- Note that the opposite does not hold in general.
-- The reason is that diff finds the edit script which minimizes cost.
-- Therefore given Diff x y e, e ≠ diff x y as e might be one of the non-optimal scripts.
-- Diff could be adapted to include additional proofs object that thake these issues into account,
-- but this is not really important for the properties I am going to prove.
-- In other words, the proofs about Diff are valid regardless of the fact that the edit-script is optimal.

Diff-suf : ∀ {xs ys} (x : DList xs) (y : DList ys) -> Diff x y (diff x y)
Diff-suf x y = Diff-suf' x y (≤-refl (size x + size y))

-- Now that we have Diff-suf we can use Diff x y e as an approximation of diff x y 

Diff~ : ∀ {xs ys zs} {x : DList xs} {y : DList ys} {z : DList zs} {e₁ : ES xs ys} {e₂ : ES xs zs} 
        -> Diff x y e₁ -> Diff x z e₂ -> e₁ ~ e₂
Diff~ End End = End
Diff~ End (Ins y q) = Ins₂ {{i = tt}} y (Diff~ End q)
Diff~ (Del x p) (Del .x q) = DelDel x (Diff~ p q)
Diff~ (Del x p) (Upd .x y q) = DelUpd x y (Diff~ p q)
Diff~ (Del x p) (Cpy .x q) = DelCpy x (Diff~ p q)
Diff~ (Del x p) (Ins y q) = Ins₂ {{i = tt}} y (Diff~ (Del x p) q)
Diff~ (Upd x y p) (Del .x q) = UpdDel x y (Diff~ p q)
Diff~ (Upd x y p) (Upd .x z q) = UpdUpd x y z (Diff~ p q)
Diff~ (Upd x y p) (Cpy .x q) = UpdCpy x y (Diff~ p q)
Diff~ (Upd {ts₃ = ts₃} {ts₄ = ts₄} x y p) (Ins z q) = Ins₂ {{i = tt}} z (Diff~ (Upd {ts₃ = ts₃} {ts₄ = ts₄} x y p) q)
Diff~ (Cpy x p) (Del .x q) = CpyDel x (Diff~ p q)
Diff~ (Cpy x p) (Upd .x y q) = CpyUpd x y (Diff~ p q)
Diff~ (Cpy x p) (Cpy .x q) = CpyCpy x (Diff~ p q)
Diff~ (Cpy {ts₃ = ts₃} {ts₄ = ts₄} x p) (Ins y q) = Ins₂ {{i = tt}} y (Diff~ (Cpy {ts₃ = ts₃} {ts₄ = ts₄} x p) q)
Diff~ (Ins y p) End = Ins₁ {{i = tt}} y (Diff~ p End)
Diff~ (Ins y p) (Del x q) = Ins₁ {{i = tt}} y (Diff~ p (Del x q))
Diff~ (Ins y p) (Upd {ts₃ = ts₃} {ts₄ = ts₄} x z q) = Ins₁ {{i = tt}} y (Diff~ p (Upd {ts₃ = ts₃} {ts₄ = ts₄} x z q))
Diff~ (Ins y p) (Cpy {ts₃ = ts₃} {ts₄ = ts₄} x q) = Ins₁ {{i = tt}} y (Diff~ p (Cpy {ts₃ = ts₃} {ts₄ = ts₄} x q))
Diff~ (Ins y p) (Ins z q) = InsIns y z (Diff~ p q)
