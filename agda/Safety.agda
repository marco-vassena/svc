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

-- Source View present in edit script
data _∈ˢ_ : ∀ {xs ys as a} -> View as a -> ES xs ys -> Set₁ where
  source-∈ : ∀ {as bs cs ds xs ys} {c : Edit as bs cs ds} {i : input c} {e : ES xs ys}
           -> c ∈ₑ e -> ⌜ c ⌝ ∈ˢ e 
-- Every term in the input tree is found as source in the edit script
noEraseˢ : ∀ {xs ys as a} {α : View as a} {x : DList xs} {y : DList ys} {e : ES xs ys}
            -> Diff x y e -> α ∈ x -> α ∈ˢ e
noEraseˢ (Del α p) (∈-here .α) = source-∈ (here (Del α))
noEraseˢ (Upd α y p) (∈-here .α) = source-∈ (here (Upd α y))
noEraseˢ (Cpy α p) (∈-here .α) = source-∈ (here (Cpy α))
noEraseˢ (Ins y p) (∈-here α) with noEraseˢ p (∈-here α)
noEraseˢ (Ins y p₁) (∈-here ._) | source-∈ {i = i} x = source-∈ {i = i} (there (Ins y) x)
noEraseˢ (Del y p) (∈-there q) with noEraseˢ p q
noEraseˢ (Del y p) (∈-there q) | source-∈ {i = i} x = source-∈ {i = i} (there (Del y) x)
noEraseˢ (Upd y z p) (∈-there q) with noEraseˢ p q
noEraseˢ (Upd y z p) (∈-there q) | source-∈ {i = i} x = source-∈ {i = i} (there (Upd y z) x)
noEraseˢ (Cpy y p) (∈-there q) with noEraseˢ p q
noEraseˢ (Cpy y p) (∈-there q) | source-∈ {i = i} x = source-∈ {i = i} (there (Cpy y) x)
noEraseˢ (Ins y p) (∈-there q) with noEraseˢ p (∈-there q)
noEraseˢ (Ins y p) (∈-there q) | source-∈ {i = i} x = source-∈ {i = i} (there (Ins y) x)

open import Data.Unit

noMadeUpAuxˢ : ∀ {xs ys bs cs ds es} {t₀ : DList xs} {t₁ : DList ys} {e : ES xs ys} {c : Edit bs cs ds es}
              {{i : input c}} {α : View (inputArgs c) (inputTy c)} -> ⌜ c ⌝ ≡ α -> c ∈ₑ e -> Diff t₀ t₁ e -> α ∈ t₀
noMadeUpAuxˢ {{i = ()}} eq (here (Ins x)) q
noMadeUpAuxˢ {{i = tt}} refl (here (Del x)) (Del .x q) = ∈-here x
noMadeUpAuxˢ {{i = tt}} refl (here (Cpy x)) (Cpy .x q) = ∈-here x
noMadeUpAuxˢ {{i = tt}} refl (here (Upd x y)) (Upd .x .y q) = ∈-here x
noMadeUpAuxˢ {{i = ()}} eq (here End) q
noMadeUpAuxˢ eq (there (Ins x) p) (Ins .x q) = noMadeUpAuxˢ eq p q
noMadeUpAuxˢ eq (there (Del x) p) (Del .x q) = ∈-there (noMadeUpAuxˢ eq p q)
noMadeUpAuxˢ eq (there (Cpy x) p) (Cpy .x q) = ∈-there (noMadeUpAuxˢ eq p q)
noMadeUpAuxˢ eq (there (Upd x y) p) (Upd .x .y q) = ∈-there (noMadeUpAuxˢ eq p q)
noMadeUpAuxˢ eq (there End p) q = noMadeUpAuxˢ eq p q

-- Inverse of noErase
-- This lemma cannot be proved directly because of the abstraction introduced by ∈ˢ,
-- therefore the auxiliary lemma noMadeUpAuxˢ, which requires explicit equality proofs,
-- is used.
noMadeUpˢ : ∀ {xs ys as a bs cs ds es} {t₀ : DList xs} {t₁ : DList ys} {e : ES xs ys} {c : Edit bs cs ds es}
              {α : View as a} -> α ∈ˢ e -> Diff t₀ t₁ e -> α ∈ t₀
noMadeUpˢ (source-∈ x) q = noMadeUpAuxˢ refl x q

--------------------------------------------------------------------------------
-- Target view present in edit script

data _∈ₒ_ : ∀ {xs ys as a} -> View as a -> ES xs ys -> Set₁ where
  target-∈ : ∀ {as bs cs ds xs ys} {c : Edit as bs cs ds} {o : output c} {e : ES xs ys}
           -> c ∈ₑ e -> ⌞ c ⌟ ∈ₒ e 

noEraseₒ : ∀ {xs ys as a} {α : View as a} {x : DList xs} {y : DList ys} {e : ES xs ys}
            -> Diff x y e -> α ∈ y -> α ∈ₒ e
noEraseₒ End ()
noEraseₒ (Del x p) q with noEraseₒ p q
noEraseₒ (Del x p) q | target-∈ {o = o} r = target-∈ {o = o} (there (Del x) r)
noEraseₒ (Upd x α p) (∈-here .α) = target-∈ (here (Upd x α))
noEraseₒ (Upd x y p) (∈-there q) with noEraseₒ p q
noEraseₒ (Upd x y p) (∈-there q) | target-∈ {o = o} r = target-∈ {o = o} (there (Upd x y) r)
noEraseₒ (Cpy α p) (∈-here .α) = target-∈ (here (Cpy α))
noEraseₒ (Cpy x p) (∈-there q) with noEraseₒ p q
noEraseₒ (Cpy x p) (∈-there q) | target-∈ {o = o} r = target-∈ {o = o} (there (Cpy x) r)
noEraseₒ (Ins α p) (∈-here .α) = target-∈ (here (Ins α))
noEraseₒ (Ins y p) (∈-there q) with noEraseₒ p q 
noEraseₒ (Ins y p) (∈-there q) | target-∈ {o = o} r = target-∈ {o = o} (there (Ins y) r)

noMadeUpAuxₒ : ∀ {xs ys bs cs ds es} {t₀ : DList xs} {t₁ : DList ys} {e : ES xs ys} {c : Edit bs cs ds es}
               {{o : output c}} {α : View (outputArgs c) (outputTy c)} -> ⌞ c ⌟ ≡ α -> c ∈ₑ e -> Diff t₀ t₁ e -> α ∈ t₁
noMadeUpAuxₒ refl (here (Ins x)) (Ins .x q) = ∈-here x
noMadeUpAuxₒ {{()}} eq (here (Del x)) q
noMadeUpAuxₒ refl (here (Cpy x)) (Cpy .x q) = ∈-here x
noMadeUpAuxₒ refl (here (Upd x y)) (Upd .x .y q) = ∈-here y
noMadeUpAuxₒ {{()}} eq (here End) q
noMadeUpAuxₒ eq (there (Ins x) p) (Ins .x q) = ∈-there (noMadeUpAuxₒ eq p q)
noMadeUpAuxₒ eq (there (Del x) p) (Del .x q) = noMadeUpAuxₒ eq p q
noMadeUpAuxₒ eq (there (Cpy x) p) (Cpy .x q) = ∈-there (noMadeUpAuxₒ eq p q)
noMadeUpAuxₒ eq (there (Upd x y) p) (Upd .x .y q) = ∈-there (noMadeUpAuxₒ eq p q)
noMadeUpAuxₒ eq (there End p) q = noMadeUpAuxₒ eq p q

noMadeUpₒ : ∀ {xs ys as a} {α : View as a} {x : DList xs} {y : DList ys} {e : ES xs ys}
            -> α ∈ₒ e -> Diff x y e -> α ∈ y 
noMadeUpₒ (target-∈ x) q = noMadeUpAuxₒ refl x q

--------------------------------------------------------------------------------

-- Similar statements are made on edits operation for diff3.
-- This is a stronger statement than noMadeUp.

noBackOutChanges₁ : ∀ {xs ys zs ws as bs cs ds} {e₁ : ES xs ys} {e₂ : ES xs zs} {d : Edit as bs cs ds} 
                     {{c : change d}} -> d ∈ₑ e₁ -> (p : e₁ ~ e₂) ->
                     let e₁₂ = diff3 e₁ e₂ p in (q : e₁₂ ↓ ws) -> d ∈ₑ (toES p q)
noBackOutChanges₁ (here (Ins x)) (InsIns {a = a} {b = b} .x y p) q with eq? a b
noBackOutChanges₁ (here (Ins x)) (InsIns .x y p) q | yes refl with x =?= y
noBackOutChanges₁ (here (Ins x)) (InsIns .x .x p) (Ins .x q) | yes refl | yes refl = here (Ins x)
noBackOutChanges₁ (here (Ins x)) (InsIns .x y p) () | yes refl | no ¬p
noBackOutChanges₁ (here (Ins x)) (InsIns .x y p) () | no ¬p
noBackOutChanges₁ (here (Ins x)) (Ins₁ .x p) (Ins .x q) = here (Ins x)
noBackOutChanges₁ (here (Ins x)) (Ins₂ y p) (Ins .y q) = there (Ins y) (noBackOutChanges₁ (here (Ins x)) p q)
noBackOutChanges₁ (here (Del x)) (DelDel .x p) (Del .x q) = here (Del x)
noBackOutChanges₁ (here (Del x)) (DelCpy .x p) (Del .x q) = here (Del x)
noBackOutChanges₁ (here (Del x)) (DelUpd .x y p) ()
noBackOutChanges₁ (here (Del x)) (Ins₂ y p) (Ins .y q) = there (Ins y) (noBackOutChanges₁ (here (Del x)) p q)
noBackOutChanges₁ {{()}} (here (Cpy x)) p q
noBackOutChanges₁ (here (Upd x y)) (UpdUpd .x .y z p) q with y =?= z
noBackOutChanges₁ (here (Upd x y)) (UpdUpd .x .y .y p) (Upd .x .y q) | yes refl = here (Upd x y)
noBackOutChanges₁ (here (Upd x y)) (UpdUpd .x .y z p) () | no ¬p
noBackOutChanges₁ (here (Upd x y)) (UpdCpy .x .y p) (Upd .x .y q) = here (Upd x y)
noBackOutChanges₁ (here (Upd x y)) (UpdDel .x .y p) ()
noBackOutChanges₁ (here (Upd x y)) (Ins₂ z p) (Ins .z q) = there (Ins z) (noBackOutChanges₁ (here (Upd x y)) p q)
noBackOutChanges₁ {{()}} (here End) p q
noBackOutChanges₁ (there (Ins x) r) (InsIns {a = a} {b = b} .x y p) q with eq? a b
noBackOutChanges₁ (there (Ins x) r) (InsIns .x y p) q | yes refl with x =?= y
noBackOutChanges₁ (there (Ins x) r) (InsIns .x .x p) (Ins .x q) | yes refl | yes refl = there (Ins x) (noBackOutChanges₁ r p q)
noBackOutChanges₁ (there (Ins x) r) (InsIns .x y p₁) () | yes refl | no ¬p
noBackOutChanges₁ (there (Ins x) r) (InsIns .x y p) () | no ¬p
noBackOutChanges₁ (there (Ins x) r) (Ins₁ .x p) (Ins .x q) = there (Ins x) (noBackOutChanges₁ r p q)
noBackOutChanges₁ (there (Ins x) r) (Ins₂ y p) (Ins .y q) = there (Ins y) (noBackOutChanges₁ (there (Ins x) r) p q)
noBackOutChanges₁ (there (Del x) r) (DelDel .x p) (Del .x q) = there (Del x) (noBackOutChanges₁ r p q)
noBackOutChanges₁ (there (Del x) r) (DelCpy .x p) (Del .x q) = there (Del x) (noBackOutChanges₁ r p q)
noBackOutChanges₁ (there (Del x) r) (DelUpd .x y p) ()
noBackOutChanges₁ (there (Del x) r) (Ins₂ y p) (Ins .y q) = there (Ins y) (noBackOutChanges₁ (there (Del x) r) p q)
noBackOutChanges₁ (there (Cpy x) r) (CpyCpy .x p) (Cpy .x q) = there (Cpy x) (noBackOutChanges₁ r p q)
noBackOutChanges₁ (there (Cpy x) r) (CpyDel .x p) (Del .x q) = there (Del x) (noBackOutChanges₁ r p q)
noBackOutChanges₁ (there (Cpy x) r) (CpyUpd .x y p) (Upd .x .y q) = there (Upd x y) (noBackOutChanges₁ r p q)
noBackOutChanges₁ (there (Cpy x) r) (Ins₂ y p) (Ins .y q) = there (Ins y) (noBackOutChanges₁ (there (Cpy x) r) p q)
noBackOutChanges₁ (there (Upd x y) r) (UpdUpd .x .y z p) q with y =?= z
noBackOutChanges₁ (there (Upd x y) r) (UpdUpd .x .y .y p) (Upd .x .y q) | yes refl = there (Upd x y) (noBackOutChanges₁ r p q)
noBackOutChanges₁ (there (Upd x y) r) (UpdUpd .x .y z p) () | no ¬p
noBackOutChanges₁ (there (Upd x y) r) (UpdCpy .x .y p) (Upd .x .y q) = there (Upd x y) (noBackOutChanges₁ r p q)
noBackOutChanges₁ (there (Upd x y) r) (UpdDel .x .y p) ()
noBackOutChanges₁ (there (Upd x y) r) (Ins₂ z p) (Ins .z q) = there (Ins z) (noBackOutChanges₁ (there (Upd x y) r) p q)
noBackOutChanges₁ (there End r) p q = noBackOutChanges₁ r p q

-- Troubles to define this. The issue is that the with
-- clause produces an ill-typed function ... but how do I fix it?
postulate toES-sym : ∀ {xs ys zs ws} {e₀₁ : ES xs ys} {e₀₂ : ES xs zs} (p : e₀₁ ~ e₀₂) -> 
           let e₀₁₂ = diff3 e₀₁ e₀₂ p in (q : e₀₁₂ ↓ ws) -> toES p q ≡ toES (~-sym p) (↓-sym p q)
-- toES-sym p q 
--  rewrite sym (diff3-sym p (diff3-wt p q)) = {!!}

--  with diff3 _ _ p | diff3-sym p (diff3-wt p q)
-- ... | e | a = {!!}

noBackOutChanges₂ : ∀ {xs ys zs ws as bs cs ds} {e₁ : ES xs ys} {e₂ : ES xs zs} {d : Edit as bs cs ds} 
                     {{c : change d}} -> d ∈ₑ e₂ -> (p : e₁ ~ e₂) ->
                     let e₁₂ = diff3 e₁ e₂ p in (q : e₁₂ ↓ ws) -> d ∈ₑ (toES p q)
noBackOutChanges₂ r p q 
  rewrite toES-sym p q = noBackOutChanges₁ r (~-sym p) (↓-sym p q)

open import Data.Sum
import Data.Sum as S


-- The sum type ⊎ corresponds to disjunction in logic (∨).
-- An edit can belong to both the script and in those cases I default to inj₁.
-- Note that this does not affect the generality of the theorem. 
noEditMadeUp : ∀ {xs ys zs ws as bs cs ds} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₁₂ : ES xs ws} {c : Edit as bs cs ds} 
                 -> c ∈ₑ e₁₂ -> Diff₃ e₁ e₂ e₁₂ -> c ∈ₑ e₁ ⊎ c ∈ₑ e₂
noEditMadeUp (here (Ins x)) (InsIns .x d₁) = inj₁ (here (Ins x))
noEditMadeUp (here (Ins x)) (Ins₁ .x d₁) = inj₁ (here (Ins x))
noEditMadeUp (here (Ins x)) (Ins₂ .x d₁) = inj₂ (here (Ins x))
noEditMadeUp (here (Del x)) (DelDel .x d) = inj₁ (here (Del x))
noEditMadeUp (here (Del x)) (DelCpy .x d) = inj₁ (here (Del x))
noEditMadeUp (here (Del x)) (CpyDel .x d) = inj₂ (here (Del x))
noEditMadeUp (here (Cpy x)) (CpyCpy .x d) = inj₁ (here (Cpy x))
noEditMadeUp (here (Upd x y)) (CpyUpd .x .y d) = inj₂ (here (Upd x y))
noEditMadeUp (here (Upd x y)) (UpdCpy .x .y d) = inj₁ (here (Upd x y))
noEditMadeUp (here (Upd x y)) (UpdUpd .x .y d) = inj₁ (here (Upd x y))
noEditMadeUp (here End) d = inj₁ (here End)
noEditMadeUp (there (Ins x) p) (InsIns .x d) = S.map (there (Ins x)) (there (Ins x)) (noEditMadeUp p d)
noEditMadeUp (there (Ins x) p) (Ins₁ .x d) = S.map (there (Ins x)) id (noEditMadeUp p d)
noEditMadeUp (there (Ins x) p) (Ins₂ .x d) = S.map id (there (Ins x)) (noEditMadeUp p d)
noEditMadeUp (there (Del x) p) (DelDel .x d) = S.map (there (Del x)) (there (Del x)) (noEditMadeUp p d)
noEditMadeUp (there (Del x) p) (DelCpy .x d) = S.map (there (Del x)) (there (Cpy x)) (noEditMadeUp p d)
noEditMadeUp (there (Del x) p) (CpyDel .x d) = S.map (there (Cpy x)) (there (Del x)) (noEditMadeUp p d)
noEditMadeUp (there (Cpy x) p) (CpyCpy .x d) = S.map (there (Cpy x)) (there (Cpy x)) (noEditMadeUp p d)
noEditMadeUp (there (Upd x y) p) (CpyUpd .x .y d) = S.map (there (Cpy x)) (there (Upd x y)) (noEditMadeUp p d)
noEditMadeUp (there (Upd x y) p) (UpdCpy .x .y d) = S.map (there (Upd x y)) (there (Cpy x)) (noEditMadeUp p d)
noEditMadeUp (there (Upd x y) p) (UpdUpd .x .y d) = S.map (there (Upd x y)) (there (Upd x y)) (noEditMadeUp p d)
noEditMadeUp (there End p) d = noEditMadeUp p d

--------------------------------------------------------------------------------

-- How should I formulate maximality ?
-- It means that diff3 must propagate all the changes from e1 and e2
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------

-- xs ⊆ ys , zs is the proof that xs is a list composed from elements of ys and zs
data _⊆_,_ : List Set -> List Set -> List Set -> Set where
  [] : [] ⊆ [] , []
  cons₁ : ∀ {y xs ys zs} -> xs ⊆ ys , zs -> y ∷ xs ⊆ y ∷ ys , zs
  cons₂ : ∀ {z xs ys zs} -> xs ⊆ ys , zs -> z ∷ xs ⊆ ys , z ∷ zs
  cons₁₂ : ∀ {x xs ys zs} -> xs ⊆ ys , zs -> x ∷ xs ⊆ x ∷ ys , x ∷ zs
  drop₁ : ∀ {y xs ys zs} -> xs ⊆ ys , zs -> xs ⊆ y ∷ ys , zs
  drop₂ : ∀ {z xs ys zs} -> xs ⊆ ys , zs -> xs ⊆ ys , z ∷ zs

infix 3 _⊆_,_ 

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
        let ds = ⟦ toES p q ⟧ in typesOf ds ⊆ as , bs -> 
        let ds₁ , ds₂ = dsplit ds in typesOf ds₁ ++ typesOf ds₂ ⊆ as , bs 
typesOf-dsplit p q r rewrite  
    typesOf++ (proj₁ (dsplit ⟦ toES p q ⟧)) (proj₂ (dsplit ⟦ toES p q ⟧)) 
  | dsplit-lemma ⟦ toES p q ⟧ = r

mixOf : ∀ {xs ys zs ws} {t₀ : DList xs} {t₁ : DList ys} {t₂ : DList zs} {e₀₁ : ES xs ys} {e₀₂ : ES xs zs} 
        -> (p : e₀₁ ~ e₀₂) ->
        let e₀₁₂ = diff3 e₀₁ e₀₂ p in (q : e₀₁₂ ↓ ws) ->        
        let t₁₂ = ⟦ toES p q ⟧ in Diff t₀ t₁ e₀₁ -> Diff t₀ t₂ e₀₂ -> typesOf t₁₂ ⊆ typesOf t₁ , typesOf t₂
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
