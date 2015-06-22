module EditScript.Core where

open import Data.DTree hiding ([_])
open Data.DTree public hiding ([_])
open import Data.List
open import Data.Product
open import Relation.Nullary

data ES : (xs : List Set) (ys : List Set) -> Set₁ where
  Ins : ∀ {xs ys zs a} -> View xs a -> ES ys (xs ++ zs) -> ES ys (a ∷ zs)
  Del : ∀ {xs ys zs a} -> View xs a -> ES (xs ++ ys) zs -> ES (a ∷ ys) zs
  Upd : ∀ {xs ys ws zs a} -> (x : View xs a) -> (y : View ys a) -> ES (xs ++ zs) (ys ++ ws) -> ES (a ∷ zs) (a ∷ ws)
  End : ES [] []

-- Patch
⟦_⟧ : ∀ {xs ys} -> ES xs ys -> DList ys
⟦ Ins {xs} {zs = zs} x e ⟧ with dsplit ⟦ e ⟧
... | ds₁ , ds₂ = (Node x ds₁) ∷ ds₂
⟦ Del x e ⟧ = ⟦ e ⟧
⟦ Upd {ys = ys} {ws = ws} x y e ⟧ with dsplit ⟦ e ⟧
... | ds₁ , ds₂ = (Node y ds₁) ∷ ds₂
⟦ End ⟧ = []

-- Retrieves the source from the edit script
⟪_⟫ : ∀ {xs ys} -> ES xs ys -> DList xs
⟪ Ins x e ⟫ = ⟪ e ⟫
⟪ Del x e ⟫ with dsplit ⟪ e ⟫
... | ds₁ , ds₂ = (Node x ds₁) ∷ ds₂
⟪ Upd x y e ⟫ with dsplit ⟪ e ⟫
... | ds₁ , ds₂ = Node x ds₁ ∷ ds₂
⟪ End ⟫ = []

--------------------------------------------------------------------------------
-- Edit abstracts over the concret edit operation

-- TODO consider removing the End from edits: it is not an acutal edit operation
-- and probably complicates unification with ∻
data Edit : List Set -> List Set -> List Set -> List Set -> Set₁ where
  Ins : ∀ {as a} -> View as a -> Edit [] as [] [ a ]
  Del : ∀ {as a} -> View as a -> Edit as [] [ a ] []
  Upd : ∀ {xs ys a} -> (x : View xs a) -> (y : View ys a) -> Edit xs ys [ a ] [ a ]

-- Adds an edit in a well-typed script.
-- Well-typedness of ES is preserved 

_∻_ : ∀ {as bs cs ds xs ys} -> Edit as bs cs ds -> ES (as ++ xs) (bs ++ ys) -> ES (cs ++ xs) (ds ++ ys) 
(Ins x) ∻ es = Ins x es
(Del x) ∻ es = Del x es
(Upd x y) ∻ es = Upd x y es

infixr 7 _∻_

--------------------------------------------------------------------------------
-- Classification of edits using types

open import Data.Empty
open import Data.Unit hiding (_≤_ ; _≤?_)

output : ∀ {as bs cs ds} -> Edit as bs cs ds -> Set
output (Ins x) = ⊤
output (Del x) = ⊥
output (Upd x x₁) = ⊤

outputArgs : ∀ {as bs cs ds} -> (e : Edit as bs cs ds) -> {{p : output e}} -> List Set
outputArgs {bs = bs} (Ins x) = bs
outputArgs (Del x) {{()}}
outputArgs {bs = bs} (Upd x y) = bs

outputTy : ∀ {as bs cs ds} -> (e : Edit as bs cs ds) -> {{o : output e}} -> Set
outputTy (Ins {a = a} x) = a
outputTy (Del x) {{()}}
outputTy (Upd {a = a} x y) = a

-- Returns the output View object
⌜_⌝ : ∀ {as bs cs ds} (e : Edit as bs cs ds) -> {{p : output e}} -> View (outputArgs e) (outputTy e)
⌜ Ins x ⌝ = x
⌜_⌝ (Del x) {{()}}
⌜ Upd x y ⌝ = y

--------------------------------------------------------------------------------

input : ∀ {as bs cs ds} -> Edit as bs cs ds -> Set
input (Ins x) = ⊥
input (Del x) = ⊤
input (Upd x y) = ⊤

inputTy : ∀ {as bs cs ds} -> (e : Edit as bs cs ds) -> {{p : input e}} -> Set
inputTy (Ins x) {{()}}
inputTy (Del {a = a} x) = a
inputTy (Upd {a = a} x y) = a

inputArgs : ∀ {as bs cs ds} -> (e : Edit as bs cs ds) -> {{p : input e}} -> List Set
inputArgs (Ins x) {{()}}
inputArgs (Del {as = as} x) = as
inputArgs (Upd {xs = xs} x y) = xs

⌞_⌟ : ∀ {as bs cs ds} -> (e : Edit as bs cs ds) -> {{p : input e}} -> View (inputArgs e) (inputTy e)
⌞_⌟ (Ins x) {{()}}
⌞ Del x ⌟ = x
⌞ Upd x y ⌟ = x

--------------------------------------------------------------------------------

-- The edit performs a change?
change : ∀ {as bs cs ds} -> Edit as bs cs ds -> Set
change (Ins x) = ⊤
change (Del x) = ⊤
change (Upd x y) with x =?= y
change (Upd x .x) | yes refl = ⊥
change (Upd x y) | no ¬p = ⊤

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

⊏ₑ-∈₁ : ∀ {xs ys as bs cs ds es fs gs hs} {e : ES xs ys} {c : Edit as bs cs ds} {d : Edit es fs gs hs} 
          -> e ⊢ₑ c ⊏ d -> c ∈ₑ e
⊏ₑ-∈₁ (here c o) = here c
⊏ₑ-∈₁ (there e p) = there e (⊏ₑ-∈₁ p)

⊏ₑ-∈₂ : ∀ {xs ys as bs cs ds es fs gs hs} {e : ES xs ys} {c : Edit as bs cs ds} {d : Edit es fs gs hs} 
          -> e ⊢ₑ c ⊏ d -> d ∈ₑ e
⊏ₑ-∈₂ (here c o) = there c o
⊏ₑ-∈₂ (there e p) = there e (⊏ₑ-∈₂ p)

--------------------------------------------------------------------------------

∈-here-⟪⟫ : ∀ {as bs cs ds xs ys} {e : ES (as ++ xs) (bs ++ ys)} (c : Edit as bs cs ds) {{i : input c}} -> ⌞ c ⌟ ∈ ⟪ c ∻ e ⟫
∈-here-⟪⟫ (Ins x) {{()}}
∈-here-⟪⟫ (Del x) = ∈-here x
∈-here-⟪⟫ (Upd x y) = ∈-here x

∈-there-⟪⟫ : ∀ {as bs cs ds ms m xs ys} {e : ES (as ++ xs) (bs ++ ys)} {α : View ms m} -> 
               (d : Edit as bs cs ds) -> α ∈ ⟪ e ⟫ -> α ∈ ⟪ d ∻ e ⟫
∈-there-⟪⟫ (Ins x) p = p
∈-there-⟪⟫ (Del x) p = ∈-there (∈-dsplit _ p)
∈-there-⟪⟫ (Upd x y) p = ∈-there (∈-dsplit _ p)

--------------------------------------------------------------------------------

∈-there-⟦⟧ :  ∀ {as bs cs ds ms m xs ys} {e : ES (as ++ xs) (bs ++ ys)} {α : View ms m} -> 
               (d : Edit as bs cs ds) -> α ∈ ⟦ e ⟧ -> α ∈ ⟦ d ∻ e ⟧
∈-there-⟦⟧ (Ins x) p = ∈-there (∈-dsplit _ p)
∈-there-⟦⟧ (Del x) p = p
∈-there-⟦⟧ (Upd x y) p = ∈-there (∈-dsplit _ p)

∈-here-⟦⟧ : ∀ {as bs cs ds xs ys} {e : ES (as ++ xs) (bs ++ ys)} (c : Edit as bs cs ds) {{o : output c}} -> ⌜ c ⌝ ∈ ⟦ c ∻ e ⟧
∈-here-⟦⟧ (Ins x) = ∈-here x
∈-here-⟦⟧ (Del x) {{()}}
∈-here-⟦⟧ (Upd x y) = ∈-here y

--------------------------------------------------------------------------------