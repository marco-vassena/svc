module Safety where

open import Diff
open import View
open import Diff3
open import DTree
open import Lemmas

open import Function
open import Data.Empty
open import Data.Product
open import Data.List
open import Relation.Binary
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality hiding ([_])

--------------------------------------------------------------------------------
-- Safety properties
--------------------------------------------------------------------------------

data _∈₃_ : ∀ {xs a} -> View xs a -> ES₃ -> Set where
  hereIns : ∀ {e xs a} (x : View xs a) -> x ∈₃ Ins x e
  hereDel : ∀ {e xs a} (x : View xs a) -> x ∈₃ Del x e
  hereUpd₁ : ∀ {e xs ys a} (x : View xs a) (y : View ys a) -> x ∈₃ Upd x y e
  hereUpd₂ : ∀ {e xs ys a} (x : View xs a) (y : View ys a) -> y ∈₃ Upd x y e
  hereCpy : ∀ {e xs a} (x : View xs a) -> x ∈₃ Cpy x e
  thereIns : ∀ {e xs ys b a}{y : View ys b} (x : View xs a) -> y ∈₃ e -> y ∈₃ Ins x e
  thereDel : ∀ {e xs ys a b} {y : View ys b} (x : View xs a) -> y ∈₃ e -> y ∈₃ Del x e
  thereUpd : ∀ {e xs ys zs a b} {z : View zs b} (x : View xs a) (y : View ys a) -> z ∈₃ e -> z ∈₃ Upd x y e
  thereCpy : ∀ {e xs ys b a} {y : View ys b} (x : View xs a) -> y ∈₃ e -> y ∈₃ Cpy x e


data _∈₂_ : ∀ {xs ys as a} -> View as a -> ES xs ys -> Set where
  hereIns : ∀ {as xs ys a} {e : ES xs (as ++ ys)} -> (x : View as a) -> x ∈₂ Ins x e
  hereCpy : ∀ {as xs ys a} {e : ES (as ++ xs) (as ++ ys)} -> (x : View as a) -> x ∈₂ Cpy x e
  hereUpd₁ : ∀ {as bs xs ys a} {e : ES (as ++ xs) (bs ++ ys)} -> (x : View as a) (y : View bs a) -> x ∈₂ Upd x y e
  hereUpd₂ : ∀ {as bs xs ys a} {e : ES (as ++ xs) (bs ++ ys)} -> (x : View as a) (y : View bs a) -> y ∈₂ Upd x y e
  hereDel : ∀ {as xs ys a} {e : ES (as ++ xs) ys} -> (x : View as a) -> x ∈₂ Del x e
  thereDel : ∀ {xs ys as bs a b} {e : ES (as ++ xs) ys} {x : View as a} {y : View bs b}
             -> y ∈₂ e -> y ∈₂ Del x e 
  thereIns : ∀ {xs ys as bs a b} {e : ES xs (as ++ ys)} {x : View as a} {y : View bs b}
             -> y ∈₂ e -> y ∈₂ Ins x e 
  thereCpy : ∀ {xs ys as bs a b} {e : ES (as ++ xs) (as ++ ys)} {x : View as a} {y : View bs b}
             -> y ∈₂ e -> y ∈₂ Cpy x e 
  thereUpd : ∀ {xs ys as bs cs a c} {e : ES (as ++ xs) (bs ++ ys)} {x : View as a} {y : View bs a} {z : View cs c}
             -> z ∈₂ e -> z ∈₂ Upd x y e

open import Data.Sum
import Data.Sum as S

-- Data is not made up

dataNotMadeUp : ∀ {xs ys zs ws a} {e₁ : ES xs ys} {e₂ : ES xs zs} {x : View ws a} (p : e₁ ~ e₂) ->
                      let e₁₂ = diff3 e₁ e₂ p in x ∈₃ e₁₂ -> x ∈₂ e₁ ⊎ x ∈₂ e₂
dataNotMadeUp End ()
dataNotMadeUp (DelDel x p) (hereDel .x) = inj₁ (hereDel x)
dataNotMadeUp (DelDel x p) (thereDel .x q) = S.map thereDel thereDel (dataNotMadeUp p q)
dataNotMadeUp (UpdUpd x y z p) q with y =?= z
dataNotMadeUp (UpdUpd x y .y p) (hereUpd₁ .x .y) | yes refl = inj₁ (hereUpd₁ x y)
dataNotMadeUp (UpdUpd x y .y p) (hereUpd₂ .x .y) | yes refl = inj₁ (hereUpd₂ x y)
dataNotMadeUp (UpdUpd x y .y p) (thereUpd .x .y q) | yes refl = S.map thereUpd thereUpd (dataNotMadeUp p q)
dataNotMadeUp (UpdUpd x y z p) () | no ¬p
dataNotMadeUp (CpyCpy x p) (hereCpy .x) = inj₁ (hereCpy x)
dataNotMadeUp (CpyCpy x p) (thereCpy .x q) = S.map thereCpy thereCpy (dataNotMadeUp p q)
dataNotMadeUp (CpyDel x p) (hereDel .x) = inj₂ (hereDel x)
dataNotMadeUp (CpyDel x p) (thereDel .x q) = S.map thereCpy thereDel (dataNotMadeUp p q)
dataNotMadeUp (DelCpy x p) (hereDel .x) = inj₁ (hereDel x)
dataNotMadeUp (DelCpy x p) (thereDel .x q) = S.map thereDel thereCpy (dataNotMadeUp p q)
dataNotMadeUp (CpyUpd x y p) (hereUpd₁ .x .y) = inj₂ (hereUpd₁ x y)
dataNotMadeUp (CpyUpd x y p) (hereUpd₂ .x .y) = inj₂ (hereUpd₂ x y)
dataNotMadeUp (CpyUpd x y p) (thereUpd .x .y q) = S.map thereCpy thereUpd (dataNotMadeUp p q)
dataNotMadeUp (UpdCpy x y p) (hereUpd₁ .x .y) = inj₁ (hereUpd₁ x y)
dataNotMadeUp (UpdCpy x y p) (hereUpd₂ .x .y) = inj₁ (hereUpd₂ x y)
dataNotMadeUp (UpdCpy x y p) (thereUpd .x .y q) = S.map thereUpd thereCpy (dataNotMadeUp p q)
dataNotMadeUp (DelUpd x₁ y p) ()
dataNotMadeUp (UpdDel x₁ y p) ()
dataNotMadeUp (InsIns {a = a} {b = b} x y p) q with eq? a b
dataNotMadeUp (InsIns x y p) q | yes refl with x =?= y
dataNotMadeUp (InsIns x .x p) (hereIns .x) | yes refl | yes refl = inj₁ (hereIns x)
dataNotMadeUp (InsIns x .x p) (thereIns .x q) | yes refl | yes refl = S.map thereIns thereIns (dataNotMadeUp p q)
dataNotMadeUp (InsIns x y p) () | yes refl | no ¬p
dataNotMadeUp (InsIns x y p) () | no ¬pope
dataNotMadeUp (Ins₁ x p) (hereIns .x) = inj₁ (hereIns x)
dataNotMadeUp (Ins₁ x p) (thereIns .x q) = S.map thereIns id (dataNotMadeUp p q)
dataNotMadeUp (Ins₂ x p) (hereIns .x) = inj₂ (hereIns x)
dataNotMadeUp (Ins₂ x₁ p) (thereIns .x₁ q) = S.map id thereIns (dataNotMadeUp p q)

-- Change does not include Cpy.
-- Since this edit does not actually introduce any change, it might be backed out with an Upd or Del
data Change : ∀ {xs ys zs a} -> View xs a -> ES ys zs -> Set where
  hereIns : ∀ {as xs ys a} {e : ES xs (as ++ ys)} -> (x : View as a) -> Change x (Ins x e)
  hereUpd : ∀ {as bs xs ys a} {e : ES (as ++ xs) (bs ++ ys)} -> (x : View as a) (y : View bs a) -> Change y (Upd x y e)
  hereDel :  ∀ {as xs ys a} {e : ES (as ++ xs) ys} -> (x : View as a) -> Change x (Del x e)
  thereDel : ∀ {xs ys as bs a b} {e : ES (as ++ xs) ys} {x : View as a} {y : View bs b}
             -> Change y e -> Change y (Del x e) 
  thereIns : ∀ {xs ys as bs a b} {e : ES xs (as ++ ys)} {x : View as a} {y : View bs b}
             -> Change y e -> Change y (Ins x e) 
  thereCpy : ∀ {xs ys as bs a b} {e : ES (as ++ xs) (as ++ ys)} {x : View as a} {y : View bs b}
             -> Change y e -> Change y (Cpy x e) 
  thereUpd : ∀ {xs ys as bs cs a c} {e : ES (as ++ xs) (bs ++ ys)} {x : View as a} {y : View bs a} {z : View cs c}
             -> Change z e -> Change z (Upd x y e)

-- TODO prove a stronger statement: the exact same change is performed
-- with this formulation Del x can be transformed in Cpy x

-- If a change is present in one of the two scripts and no conflicts are detected,
-- than that change is present in the merged version.
noBackOutChanges₁ : ∀ {a as xs ys zs} {x : View as a} {e₁ : ES xs ys} {e₂ : ES xs zs}
                   -> (p : e₁ ~ e₂) -> let e₁₂ = diff3 e₁ e₂ p in 
                      NoCnf e₁₂ -> Change x e₁ -> x ∈₃ e₁₂
noBackOutChanges₁ End q ()
noBackOutChanges₁ (DelDel x p) (Del .x q) (hereDel .x) = hereDel x
noBackOutChanges₁ (DelDel x p) (Del .x q) (thereDel r) = thereDel x (noBackOutChanges₁ p q r)
noBackOutChanges₁ (UpdUpd x y z p) q (hereUpd .x .y) with y =?= z
noBackOutChanges₁ (UpdUpd x y .y p) (Upd .x .y q) (hereUpd .x .y) | yes refl = hereUpd₂ x y
noBackOutChanges₁ (UpdUpd x y z p) () (hereUpd .x .y) | no ¬p
noBackOutChanges₁ (UpdUpd x y z p) q (thereUpd r) with y =?= z
noBackOutChanges₁ (UpdUpd x y .y p) (Upd .x .y q) (thereUpd r) | yes refl = thereUpd x y (noBackOutChanges₁ p q r)
noBackOutChanges₁ (UpdUpd x y z p) () (thereUpd r) | no ¬p
noBackOutChanges₁ (CpyCpy x p) (Cpy .x q) (thereCpy r) = thereCpy x (noBackOutChanges₁ p q r)
noBackOutChanges₁ (CpyDel x p) (Del .x q) (thereCpy r) = thereDel x (noBackOutChanges₁ p q r)
noBackOutChanges₁ (DelCpy x p) (Del .x q) (hereDel .x) = hereDel x
noBackOutChanges₁ (DelCpy x p) (Del .x q) (thereDel r) = thereDel x (noBackOutChanges₁ p q r)
noBackOutChanges₁ (CpyUpd x y p) (Upd .x .y q) (thereCpy r) = thereUpd x y (noBackOutChanges₁ p q r)
noBackOutChanges₁ (UpdCpy x y p) (Upd .x .y q) (hereUpd .x .y) = hereUpd₂ x y
noBackOutChanges₁ (UpdCpy x y p) (Upd .x .y q) (thereUpd r) = thereUpd x y (noBackOutChanges₁ p q r)
noBackOutChanges₁ (DelUpd x y p) () r
noBackOutChanges₁ (UpdDel x y p) () r
noBackOutChanges₁ (InsIns {a = a} {b = b} x y p) q r with eq? a b
noBackOutChanges₁ (InsIns x y p) q r | yes refl with x =?= y
noBackOutChanges₁ (InsIns x .x p) (Ins .x q) (hereIns .x) | yes refl | yes refl = hereIns x
noBackOutChanges₁ (InsIns x .x p) (Ins .x q) (thereIns r) | yes refl | yes refl = thereIns x (noBackOutChanges₁ p q r)
noBackOutChanges₁ (InsIns x y p) () r | yes refl | no ¬p
noBackOutChanges₁ (InsIns x₁ y p) () r | no ¬p
noBackOutChanges₁ (Ins₁ x p) (Ins .x q) (hereIns .x) = hereIns x
noBackOutChanges₁ (Ins₁ x p) (Ins .x q) (thereIns r) = thereIns x (noBackOutChanges₁ p q r)
noBackOutChanges₁ (Ins₂ x p) (Ins .x q) r = thereIns x (noBackOutChanges₁ p q r)

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

noConf-sym : ∀ {xs ys zs} {e₁ : ES xs ys} {e₂ : ES xs zs} -> (p : e₁ ~ e₂) -> NoCnf (diff3 _ _ p) 
             -> NoCnf (diff3 _ _ (~-sym p))
noConf-sym p q with diff3 _ _ (~-sym p) | diff3-sym p q
noConf-sym p q | ._ | refl = q

noBackOutChanges₂ : ∀ {a as xs ys zs} {x : View as a} {e₁ : ES xs ys} {e₂ : ES xs zs}
                   -> (p : e₁ ~ e₂) -> let e₁₂ = diff3 e₁ e₂ p in 
                      NoCnf e₁₂ -> Change x e₂ -> x ∈₃ e₁₂
noBackOutChanges₂ p q r with noBackOutChanges₁ (~-sym p) (noConf-sym p q) r
noBackOutChanges₂ p q r | a rewrite diff3-sym p q = a

--------------------------------------------------------------------------------

-- well-typedness is symmetric
diff3-wt-sym : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} -> (p : e₁ ~ e₂) -> diff3 e₁ e₂ p ↓ ws -> diff3 e₂ e₁ (~-sym p) ↓ ws
diff3-wt-sym p q rewrite sym (diff3-sym p (diff3-wt p q)) = q


--------------------------------------------------------------------------------

-- What is the actual relation _~_,_  ?
-- We need to think more carefully about it: how are ys and zs related to the result ws ?
-- Problems:
--  - Not simple MixOf because of DelCpy
--  - Disalignment

-- xs ~ ys , zs is the proof that xs is a list composed from elements of ys and zs
data _⊑_,_ : List Set -> List Set -> List Set -> Set where
  [] : [] ⊑ [] , []
  cons₁ : ∀ {y xs ys zs} -> xs ⊑ ys , zs -> y ∷ xs ⊑ y ∷ ys , zs
  cons₂ : ∀ {z xs ys zs} -> xs ⊑ ys , zs -> z ∷ xs ⊑ ys , z ∷ zs
  cons₁₂ : ∀ {x xs ys zs} -> xs ⊑ ys , zs -> x ∷ xs ⊑ x ∷ ys , x ∷ zs
  drop₁ : ∀ {y xs ys zs} -> xs ⊑ ys , zs -> xs ⊑ y ∷ ys , zs
  drop₂ : ∀ {z xs ys zs} -> xs ⊑ ys , zs -> xs ⊑ ys , z ∷ zs

infix 3 _⊑_,_ 

typesOf : ∀ {xs} -> DList xs -> List Set
typesOf [] = []
typesOf (Node {a = a} x xs ∷ d) = a ∷ typesOf xs ++ typesOf d

typesOf++ : ∀ {as bs} (a : DList as) (b : DList bs) -> typesOf a ++ typesOf b ≡ typesOf (a +++ b)
typesOf++ [] b = refl
typesOf++ (Node {a = ty} x xs ∷ a) b rewrite 
   sym (typesOf++ a b)  
  | ++-assoc (typesOf xs) (typesOf a) (typesOf b) = cong (_∷_ ty) refl

typesOf-dsplit : ∀ {{ws us}} {xs ys zs as bs} {e₀₁ : ES xs ys} {e₀₂ : ES xs zs} -> (p : e₀₁ ~ e₀₂) -> 
        let e₀₁₂ = diff3 e₀₁ e₀₂ p in (q : e₀₁₂ ↓ (ws ++ us)) ->        
        let ds = ⟦ toES p q ⟧ in typesOf ds ⊑ as , bs -> 
        let ds₁ , ds₂ = dsplit ds in typesOf ds₁ ++ typesOf ds₂ ⊑ as , bs 
typesOf-dsplit p q r rewrite  
    typesOf++ (proj₁ (dsplit ⟦ toES p q ⟧)) (proj₂ (dsplit ⟦ toES p q ⟧)) 
  | dsplit-lemma ⟦ toES p q ⟧ = r

-- This is not true in general because upon Del/Cpy delete is chosen,
-- so one element does not get into the list
mixOf : ∀ {xs ys zs ws} {t₀ : DList xs} {t₁ : DList ys} {t₂ : DList zs} {e₀₁ : ES xs ys} {e₀₂ : ES xs zs} 
        -> (p : e₀₁ ~ e₀₂) ->
        let e₀₁₂ = diff3 e₀₁ e₀₂ p in (q : e₀₁₂ ↓ ws) ->        
        let t₁₂ = ⟦ toES p q ⟧ in Diff t₀ t₁ e₀₁ -> Diff t₀ t₂ e₀₂ -> typesOf t₁₂ ⊑ typesOf t₁ , typesOf t₂
mixOf End End End End = []
mixOf (DelDel x p) (Del .x q) (Del .x c) (Del .x d) = mixOf p q c d
mixOf (UpdUpd x y z p) q (Upd .x .y c) (Upd .x .z d) with y =?= z
mixOf (UpdUpd {bs = bs} x y .y p) (Upd {zs = zs} .x .y q) (Upd {ts₃ = ts₃} {ts₄ = ts₄} .x .y c) (Upd {ts₃ = ts₃'} {ts₄ = ts₄'} .x .y d)
  | yes refl rewrite
    typesOf++ ts₃ ts₄ 
  | typesOf++ ts₃' ts₄' = cons₁₂ (typesOf-dsplit p q (mixOf p q c d))

mixOf (UpdUpd x y z p) () (Upd .x .y c) (Upd .x .z d) | no ¬p

mixOf (CpyCpy {as = as} x p) (Cpy {ys = ys} .x q) (Cpy {ts₃ = ts₃} {ts₄ = ts₄} .x c) (Cpy {ts₃ = ts₃'} {ts₄ = ts₄'} .x d) rewrite 
  typesOf++ ts₃ ts₄ | typesOf++ ts₃' ts₄' = cons₁₂ (typesOf-dsplit p q (mixOf p q c d))

mixOf (CpyDel x p) (Del .x q) (Cpy {ts₃ = ts₃} {ts₄ = ts₄} .x c) (Del .x d) 
  rewrite typesOf++ ts₃ ts₄ = drop₁ (mixOf p q c d)
mixOf (DelCpy x p) (Del .x q) (Del .x c) (Cpy {ts₃ = ts₃} {ts₄ = ts₄} .x d) 
  rewrite typesOf++ ts₃ ts₄ = drop₂ (mixOf p q c d)

mixOf (CpyUpd {bs = bs} x y p) (Upd {zs = zs} .x .y q) (Cpy {ts₃ = ts₃} {ts₄ = ts₄} .x c) (Upd {ts₃ = ts₃'} {ts₄ = ts₄'} .x .y d)   
  rewrite  typesOf++ ts₃ ts₄ 
         | typesOf++ ts₃' ts₄' = cons₁₂ (typesOf-dsplit p q (mixOf p q c d))

mixOf (UpdCpy {bs = bs} x y p) (Upd {zs = zs} .x .y q) (Upd {ts₃ = ts₃} {ts₄ = ts₄} .x .y c) (Cpy {ts₃ = ts₃'} {ts₄ = ts₄'} .x d) 
  rewrite  typesOf++ ts₃ ts₄ 
         | typesOf++ ts₃' ts₄' = cons₁₂ (typesOf-dsplit p q (mixOf p q c d))

mixOf (DelUpd x y p) () c d
mixOf (UpdDel x y p) () c d
mixOf (InsIns {a = a} {b = b} x y p) q (Ins .x c) (Ins .y d) with eq? a b
mixOf (InsIns x y p) q (Ins .x c) (Ins .y d) | yes refl with x =?= y
mixOf (InsIns {as = as} x .x p) (Ins {ys = ys} .x q) (Ins {ts₂ = ts₂} {ts₃ = ts₃} .x c) (Ins {ts₂ = ts₂'} {ts₃ = ts₃'} .x d) 
  | yes refl | yes refl rewrite
    typesOf++ ts₂ ts₃ | typesOf++ ts₂' ts₃' = cons₁₂ (typesOf-dsplit p q (mixOf p q c d))

mixOf (InsIns x y p) () (Ins .x c) (Ins .y d) | yes refl | no ¬p
mixOf (InsIns x y p) () (Ins .x c) (Ins .y d) | no ¬p
mixOf (Ins₁ {as = as} x p) (Ins {ys = ys} .x q) (Ins {ts₂ = ts₂} {ts₃ = ts₃} .x c) d 
  rewrite typesOf++ ts₂ ts₃ = cons₁ (typesOf-dsplit p q (mixOf p q c d))
mixOf (Ins₂ {as = as} x p) (Ins {ys = ys} .x q) c (Ins {ts₂ = ts₂} {ts₃ = ts₃} .x d) 
  rewrite typesOf++ ts₂ ts₃ = cons₂ (typesOf-dsplit p q (mixOf p q c d))
