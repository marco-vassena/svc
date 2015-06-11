module EditScript.Core where

open import Data.DTree hiding ([_])
open Data.DTree public hiding ([_])
open import Data.List
open import Data.Product


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

⊏ₑ-∈₁ : ∀ {xs ys as bs cs ds es fs gs hs} {e : ES xs ys} {c : Edit as bs cs ds} {d : Edit es fs gs hs} 
          -> e ⊢ₑ c ⊏ d -> c ∈ₑ e
⊏ₑ-∈₁ (here c o) = here c
⊏ₑ-∈₁ (there e p) = there e (⊏ₑ-∈₁ p)

⊏ₑ-∈₂ : ∀ {xs ys as bs cs ds es fs gs hs} {e : ES xs ys} {c : Edit as bs cs ds} {d : Edit es fs gs hs} 
          -> e ⊢ₑ c ⊏ d -> d ∈ₑ e
⊏ₑ-∈₂ (here c o) = there c o
⊏ₑ-∈₂ (there e p) = there e (⊏ₑ-∈₂ p)

--------------------------------------------------------------------------------
