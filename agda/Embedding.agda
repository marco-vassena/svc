module Embedding where

open import DTree hiding ([_])
open import View
open import Diff
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])

data Edit : List Set -> List Set -> List Set -> List Set -> Set₁ where
  Ins : ∀ {as a} -> View as a -> Edit [] as [] [ a ]
  Del : ∀ {as a} -> View as a -> Edit as [] [ a ] []
  Cpy : ∀ {as a} -> View as a -> Edit as as [ a ] [ a ]
  Upd : ∀ {xs ys a} -> View xs a -> View ys a -> Edit xs ys [ a ] [ a ]
  End : Edit [] [] [] []

-- Adds an edit in a well-typed script.
-- Well-typedness of ES is preserved
add : ∀ {as bs cs ds xs ys} -> Edit as bs cs ds -> ES (as ++ xs) (bs ++ ys) -> ES (cs ++ xs) (ds ++ ys) 
add (Ins x) es = Ins x es
add (Del x) es = Del x es
add (Cpy x) es = Cpy x es
add (Upd x y) es = Upd x y es
add End es = es

data _∈ₑ_ : ∀ {as bs cs ds xs ys} -> Edit as bs cs ds -> ES xs ys -> Set₁ where
  here : ∀ {as bs cs ds xs ys} {e : ES (as ++ xs) (bs ++ ys)} -> (c : Edit as bs cs ds) -> c ∈ₑ add c e
  there : ∀ {as bs cs ds es fs gs hs xs ys} {c : Edit as bs cs ds} {e : ES (es ++ xs) (fs ++ ys)} (d : Edit es fs gs hs)
          -> c ∈ₑ e -> c ∈ₑ add d e

data _⊢ₑ_⊏_ : ∀ {xs ys as bs cs ds es fs gs hs} -> ES xs ys -> Edit as bs cs ds -> Edit es fs gs hs -> Set₁ where
  here : ∀ {as bs cs ds es fs gs hs xs ys} {d : Edit es fs gs hs} {e : ES (as ++ xs) (bs ++ ys)} 
         -> (c : Edit as bs cs ds) -> (o : d ∈ₑ e) -> add c e ⊢ₑ c ⊏ d 
  there : ∀ {as bs cs ds es fs gs hs is ls ms ns xs ys} {d : Edit es fs gs hs} {c : Edit as bs cs ds} {e : ES (is ++ xs) (ls ++ ys)}
          (a : Edit is ls ms ns) -> (o : e ⊢ₑ c ⊏ d) -> add a e ⊢ₑ c ⊏ d 

open import Data.Empty
open import Data.Unit

-- output : ∀ {as bs cs ds} -> Edit as bs cs ds -> Set
-- output (Ins x) = ⊤
-- output (Del x) = ⊥
-- output (Cpy x) = ⊤
-- output (Upd x x₁) = ⊤
-- output End = ⊥

-- outputArgs : ∀ {as bs cs ds} -> (e : Edit as bs cs ds) -> output e -> List Set
-- outputArgs {bs = bs} (Ins x) tt = bs
-- outputArgs (Del x) ()
-- outputArgs {as = as} (Cpy x) tt = as
-- outputArgs {bs = bs} (Upd x y) tt = bs
-- outputArgs End ()

-- outputTy : ∀ {as bs cs ds} -> (e : Edit as bs cs ds) -> output e -> Set
-- outputTy (Ins {a = a} x) tt = a
-- outputTy (Del x) ()
-- outputTy (Cpy {a = a} x) tt = a
-- outputTy (Upd {a = a} x y) tt = a
-- outputTy End ()

-- -- Returns the output View object
-- ⌞_⌟ : ∀ {as bs cs ds} (e : Edit as bs cs ds) -> {{p : output e}} -> View (outputArgs e p) (outputTy e p)
-- ⌞ Ins x ⌟ = x
-- ⌞_⌟ (Del x) {{()}}
-- ⌞ Cpy x ⌟ = x
-- ⌞ Upd x y ⌟ = y
-- ⌞_⌟ End {{()}}

-- ∈-dsplit : ∀ {as bs cs ds'} {{ys zs}} {ds : DList (ys ++ zs)} (d : Edit as bs cs ds') {{ p : output d }} ->  
--            let ds₁ , ds₂ = dsplit ds in ⌞ d ⌟ ∈ ds -> ⌞ d ⌟ ∈ ds₁ +++ ds₂
-- ∈-dsplit {ds = ds} _ q
--   rewrite dsplit-lemma ds = q

-- ∈ₑ-∈  : ∀ {as bs cs ds xs ys} {d : Edit as bs cs ds} {{ p : output d }} {e : ES xs ys} -> d ∈ₑ e -> ⌞ d ⌟ ∈ ⟦ e ⟧
-- ∈ₑ-∈ (here {e = e} (Ins x)) = ∈-here x 
-- ∈ₑ-∈ {{p = ()}} (here (Del x))
-- ∈ₑ-∈ (here {e = e} (Cpy x)) = ∈-here x
-- ∈ₑ-∈ (here {e = e} (Upd x y)) = ∈-here y
-- ∈ₑ-∈ {{p = ()}} (here End)
-- ∈ₑ-∈ {d = d} (there {e = e} (Ins x) q) = ∈-there (∈-dsplit d (∈ₑ-∈ q))
-- ∈ₑ-∈ (there (Del x) q) = ∈ₑ-∈ q
-- ∈ₑ-∈ {d = d} {{p = p}} (there {e = e} (Cpy x) q) = ∈-there (∈-dsplit d (∈ₑ-∈ q))
-- ∈ₑ-∈ {d = d} (there (Upd x x₁) q) = ∈-there (∈-dsplit d (∈ₑ-∈ q))
-- ∈ₑ-∈ (there End q) = ∈ₑ-∈ q

-- ⟦⟧-lemma : ∀ {{ys}} {{zs}} {as bs cs ds es fs gs hs xs} (c : Edit as bs cs ds) (d : Edit es fs gs hs) (e : ES xs (ys ++ zs))
--              {{p : output c}} {{q : output d}} -> ⟦ e ⟧ ⊢ ⌞ c ⌟ ⊏ ⌞ d ⌟ ->
--               let ds₁ , ds₂ = dsplit ⟦ e ⟧ in ds₁ +++ ds₂ ⊢ ⌞ c ⌟ ⊏ ⌞ d ⌟
-- ⟦⟧-lemma c d e q rewrite dsplit-lemma ⟦ e ⟧ = q

-- preserves-⊏ : ∀ {as bs cs ds es fs gs hs xs ys} {e : ES xs ys} {d : Edit es fs gs hs}
--               (c : Edit as bs cs ds) -> {{p : output c}} {{q : output d}} 
--               -> e ⊢ₑ c ⊏ d -> ⟦ e ⟧ ⊢ ⌞ c ⌟ ⊏ ⌞ d ⌟
-- preserves-⊏ {d = d} (Ins x) (here .(Ins x) p) = here x (∈-dsplit d (∈ₑ-∈ p))
-- preserves-⊏ (Del x) {{()}} (here .(Del x) p)
-- preserves-⊏ {d = d} (Cpy x) (here {e = e} .(Cpy x) p) = here x (∈-dsplit d (∈ₑ-∈ p))
-- preserves-⊏ {d = d} (Upd x y) (here .(Upd x y) p) = here y (∈-dsplit d (∈ₑ-∈ p))
-- preserves-⊏ End {{()}} (here .End x)
-- preserves-⊏ {d = d} c (there {e = e} (Ins x) p) = there (⟦⟧-lemma c d e (preserves-⊏ c p))
-- preserves-⊏ c (there (Del x) p) = preserves-⊏ c p
-- preserves-⊏ {d = d} c (there {e = e} (Cpy x) p) = there (⟦⟧-lemma c d e (preserves-⊏ c p))
-- preserves-⊏ {d = d} c (there {e = e} (Upd x y) p) = there (⟦⟧-lemma c d e (preserves-⊏ c p))
-- preserves-⊏ c (there End p) = preserves-⊏ c p

-- The edit performs a change?
change : ∀ {as bs cs ds} -> Edit as bs cs ds -> Set
change (Ins x) = ⊤
change (Del x) = ⊤
change (Cpy x) = ⊥
change (Upd x y) = ⊤
change End = ⊥

open import Relation.Nullary
open import Diff3

toES∈ₑ : ∀ {as bs cs ds xs ys zs ws} {d : Edit as bs cs ds} {{w : change d}} {e₁ : ES xs ys} {e₂ : ES xs zs} 
           -> d ∈ₑ e₁ -> (p : e₁ ~ e₂) ->
           let e₁₂ = diff3 e₁ e₂ p in (q : e₁₂ ↓ ws) -> d ∈ₑ toES p q
toES∈ₑ (here (Ins x)) (InsIns {a = a} {b = b} .x y p) q with eq? a b
toES∈ₑ (here (Ins x)) (InsIns .x y p) q | yes refl with x =?= y
toES∈ₑ (here (Ins x)) (InsIns .x .x p) (Ins .x q) | yes refl | yes refl = here (Ins x)
toES∈ₑ (here (Ins x)) (InsIns .x y p) () | yes refl | no ¬p
toES∈ₑ (here (Ins x)) (InsIns .x y p) () | no ¬p
toES∈ₑ (here (Ins x)) (Ins₁ .x p) (Ins .x q) = here (Ins x)
toES∈ₑ (here (Ins x)) (Ins₂ y p) (Ins .y q) = there (Ins y) (toES∈ₑ (here (Ins x)) p q)
toES∈ₑ (here (Del x)) (DelDel .x p) (Del .x q) = here (Del x)
toES∈ₑ (here (Del x)) (DelCpy .x p) (Del .x q) = here (Del x)
toES∈ₑ (here (Del x)) (DelUpd .x y p) ()
toES∈ₑ (here (Del x)) (Ins₂ y p) (Ins .y q) = there (Ins y) (toES∈ₑ (here (Del x)) p q)
toES∈ₑ {{w = ()}} (here (Cpy x)) p q
toES∈ₑ (here (Upd x y)) (UpdUpd .x .y z p) q with y =?= z
toES∈ₑ (here (Upd x y)) (UpdUpd .x .y .y p) (Upd .x .y q) | yes refl = here (Upd x y)
toES∈ₑ (here (Upd x y)) (UpdUpd .x .y z p) () | no ¬p
toES∈ₑ (here (Upd x y)) (UpdCpy .x .y p) (Upd .x .y q) = here (Upd x y)
toES∈ₑ (here (Upd x y)) (UpdDel .x .y p) ()
toES∈ₑ (here (Upd x y)) (Ins₂ z p) (Ins .z q) = there (Ins z) (toES∈ₑ (here (Upd x y)) p q)
toES∈ₑ {{w = ()}} (here End) p q
toES∈ₑ (there (Ins x) r) (InsIns {a = a} {b = b} .x y p) q with eq? a b
toES∈ₑ (there (Ins x) r) (InsIns .x y p) q | yes refl with x =?= y
toES∈ₑ (there (Ins x) r) (InsIns .x .x p) (Ins .x q) | yes refl | yes refl = there (Ins x) (toES∈ₑ r p q)
toES∈ₑ (there (Ins x) r) (InsIns .x y p) () | yes refl | no ¬p
toES∈ₑ (there (Ins x) r) (InsIns .x y p) () | no ¬p
toES∈ₑ (there (Ins x) r) (Ins₁ .x p) (Ins .x q) = there (Ins x) (toES∈ₑ r p q)
toES∈ₑ (there (Ins x) r) (Ins₂ y p) (Ins .y q) = there (Ins y) (toES∈ₑ (there (Ins x) r) p q)
toES∈ₑ (there (Del x) r) (DelDel .x p) (Del .x q) = there (Del x) (toES∈ₑ r p q)
toES∈ₑ (there (Del x) r) (DelCpy .x p) (Del .x q) = there (Del x) (toES∈ₑ r p q)
toES∈ₑ (there (Del x) r) (DelUpd .x y p) ()
toES∈ₑ (there (Del x) r) (Ins₂ y p) (Ins .y q) = there (Ins y) (toES∈ₑ (there (Del x) r) p q)
toES∈ₑ (there (Cpy x) r) (CpyCpy .x p) (Cpy .x q) = there (Cpy x) (toES∈ₑ r p q)
toES∈ₑ (there (Cpy x) r) (CpyDel .x p) (Del .x q) = there (Del x) (toES∈ₑ r p q)
toES∈ₑ (there (Cpy x) r) (CpyUpd .x y p) (Upd .x .y q) = there (Upd x y) (toES∈ₑ r p q)
toES∈ₑ (there (Cpy x) r) (Ins₂ y p) (Ins .y q) = there (Ins y ) (toES∈ₑ (there (Cpy x) r) p q)
toES∈ₑ (there (Upd x y) r) (UpdUpd .x .y z p) q with y =?= z
toES∈ₑ (there (Upd x y) r) (UpdUpd .x .y .y p) (Upd .x .y q) | yes refl = there (Upd x y) (toES∈ₑ r p q)
toES∈ₑ (there (Upd x y) r) (UpdUpd .x .y z p) () | no ¬p
toES∈ₑ (there (Upd x y) r) (UpdCpy .x .y p) (Upd .x .y q) = there (Upd x y) (toES∈ₑ r p q)
toES∈ₑ (there (Upd x y) r) (UpdDel .x .y p) ()
toES∈ₑ (there (Upd x y) r) (Ins₂ z p) (Ins .z q) = there (Ins z) (toES∈ₑ (there (Upd x y) r) p q)
toES∈ₑ (there End r) p q = toES∈ₑ r p q

-- diff3-⊏ : ∀ {as bs cs ds es fs gs hs xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs}
--               (c : Edit as bs cs ds) (d : Edit es fs gs hs) -> {{w : change c}} {{z : change d}} 
--               -> e₁ ⊢ₑ c ⊏ d -> (p : e₁ ~ e₂) ->
--               let e₁₂ = diff3 e₁ e₂ p in (q : e₁₂ ↓ ws) -> toES p q ⊢ₑ c ⊏ d
-- diff3-⊏ (Ins x) d (here .(Ins x) o) (InsIns {a = a} {b = b} .x y p) q with eq? a b
-- diff3-⊏ (Ins x) d (here .(Ins x) o) (InsIns .x y p) q | yes refl with x =?= y
-- diff3-⊏ (Ins x) d (here .(Ins x) o) (InsIns .x .x p) (Ins .x q) | yes refl | yes refl = here (Ins x) (toES∈ₑ o p q)
-- diff3-⊏ (Ins x) d (here .(Ins x) o) (InsIns .x y p) () | yes refl | no ¬p
-- diff3-⊏ (Ins x) d (here .(Ins x) o) (InsIns .x y p) () | no ¬p
-- diff3-⊏ (Ins x) d (here .(Ins x) o) (Ins₁ .x p) (Ins .x q) = here (Ins x) (toES∈ₑ o p q)
-- diff3-⊏ (Ins x) d (here .(Ins x) o) (Ins₂ y p) (Ins .y q) = there (Ins y) (diff3-⊏ (Ins x) d (here (Ins x) o) p q)
-- diff3-⊏ (Del x) d (here .(Del x) o) (DelDel .x p) (Del .x q) = here (Del x) (toES∈ₑ o p q)
-- diff3-⊏ (Del x) d (here .(Del x) o) (DelCpy .x p) (Del .x q) = here (Del x) (toES∈ₑ o p q)
-- diff3-⊏ (Del x) d (here .(Del x) o) (DelUpd .x y p) ()
-- diff3-⊏ (Del x) d (here .(Del x) o) (Ins₂ y p) (Ins .y q) = there (Ins y) (diff3-⊏ (Del x) d (here (Del x) o) p q)
-- diff3-⊏ (Cpy x) d (here .(Cpy x) o) (CpyCpy .x p) (Cpy .x q) = here (Cpy x) (toES∈ₑ o p q)
-- diff3-⊏ (Cpy x) d {{()}} (here .(Cpy x) o) (CpyDel .x p) q
-- diff3-⊏ (Cpy x) d {{()}} (here .(Cpy x) o) (CpyUpd .x y p) (Upd .x .y q)
-- diff3-⊏ (Cpy x) d (here .(Cpy x) o) (Ins₂ y p) (Ins .y q) = there (Ins y) (diff3-⊏ (Cpy x) d (here (Cpy x) o) p q)
-- diff3-⊏ (Upd x y) d (here .(Upd x y) o) (UpdUpd .x .y z p) q with y =?= z
-- diff3-⊏ (Upd x y) d (here .(Upd x y) o) (UpdUpd .x .y .y p) (Upd .x .y q) | yes refl = here (Upd x y) (toES∈ₑ o p q)
-- diff3-⊏ (Upd x y) d (here .(Upd x y) o) (UpdUpd .x .y z p) () | no ¬p
-- diff3-⊏ (Upd x y) d (here .(Upd x y) o) (UpdCpy .x .y p) (Upd .x .y q) = here (Upd x y) (toES∈ₑ o p q)
-- diff3-⊏ (Upd x y) d (here .(Upd x y) o) (UpdDel .x .y p) ()
-- diff3-⊏ (Upd x y) d (here .(Upd x y) o) (Ins₂ z p) (Ins .z q) = there (Ins z) (diff3-⊏ (Upd x y) d (here (Upd x y) o) p q)
-- diff3-⊏ End d {{()}} (here .End x) p q
-- diff3-⊏ c d (there (Ins x) r) (InsIns {a = a} {b = b} .x y p) q with eq? a b
-- diff3-⊏ c d (there (Ins x) r) (InsIns .x y p) q | yes refl with x =?= y
-- diff3-⊏ c d (there (Ins x) r) (InsIns .x .x p) (Ins .x q) | yes refl | yes refl = there (Ins x) (diff3-⊏ c d r p q)
-- diff3-⊏ c d (there (Ins x) r) (InsIns .x y p) () | yes refl | no ¬p
-- diff3-⊏ c d (there (Ins x) r) (InsIns .x y p) () | no ¬p
-- diff3-⊏ c d (there (Ins x) r) (Ins₁ .x p) (Ins .x q) = there (Ins x) (diff3-⊏ c d r p q)
-- diff3-⊏ c d (there (Ins x) r) (Ins₂ y p) (Ins .y q) = there (Ins y) (diff3-⊏ c d (there (Ins x) r) p q)
-- diff3-⊏ c d (there (Del x) r) (DelDel .x p) (Del .x q) = there (Del x) (diff3-⊏ c d r p q)
-- diff3-⊏ c d (there (Del x) r) (DelCpy .x p) (Del .x q) = there (Del x) (diff3-⊏ c d r p q)
-- diff3-⊏ c d (there (Del x) r) (DelUpd .x y p) ()
-- diff3-⊏ c d (there (Del x) r) (Ins₂ y p) (Ins .y q) = there (Ins y) (diff3-⊏ c d (there (Del x) r) p q)
-- diff3-⊏ c d (there (Cpy x) r) (CpyCpy .x p) (Cpy .x q) = there (Cpy x) (diff3-⊏ c d r p q)
-- diff3-⊏ c d (there (Cpy x) r) (CpyDel .x p) (Del .x q) = there (Del x) (diff3-⊏ c d r p q)
-- diff3-⊏ c d (there (Cpy x) r) (CpyUpd .x y p) (Upd .x .y q) = there (Upd x y) (diff3-⊏ c d r p q)
-- diff3-⊏ c d (there (Cpy x) r) (Ins₂ y p) (Ins .y q) = there (Ins y) (diff3-⊏ c d (there (Cpy x) r) p q)
-- diff3-⊏ c d (there (Upd x y) r) (UpdUpd .x .y z p) q with y =?= z
-- diff3-⊏ c d (there (Upd x y) r) (UpdUpd .x .y .y p) (Upd .x .y q) | yes refl = there (Upd x y) (diff3-⊏ c d r p q)
-- diff3-⊏ c d (there (Upd x y) r) (UpdUpd .x .y z p) () | no ¬p
-- diff3-⊏ c d (there (Upd x y) r) (UpdCpy .x .y p) (Upd .x .y q) = there (Upd x y) (diff3-⊏ c d r p q)
-- diff3-⊏ c d (there (Upd x y) r) (UpdDel .x .y p) ()
-- diff3-⊏ c d (there (Upd x y) r) (Ins₂ z p) (Ins .z q) = there (Ins z) (diff3-⊏ c d (there (Upd x y) r) p q)
-- diff3-⊏ c d (there End r) p q = diff3-⊏ c d r p q

--------------------------------------------------------------------------------
-- diff3 preserves ordering

-- Diff a b e links the edit script e and the source and target objects a b.
-- It is used instead of diff a b because the diff algorithm requires several unimportant steps
-- that makes the proof overly complicated.

-- diff3⊏ : ∀ {xs ys zs ws as bs a b} {α : View as a} {β : View bs b} {t₀ : DList xs} {t₁ : DList ys} {t₂ : DList zs}
--            {e₀₁ : ES xs ys} {e₀₂ : ES xs zs} -> (p : e₀₁ ~ e₀₂) -> Diff t₀ t₁ e₀₁ -> Diff t₀ t₂ e₀₂ ->
--            let e₀₁₂ = diff3 e₀₁ e₀₂ p in (q : e₀₁₂ ↓ ws) ->
--            let t₀₁₂ = ⟦ e₀₁₂ ⟧ q in t₀ ⊢ α ⊏ β -> α ∈ t₀₁₂ -> β ∈ t₀₁₂ -> t₀₁₂ ⊢ α ⊏ β
-- diff3⊏ End c d q () n m

-- -- Here I should have only there, n and m are not () because it's possible that another α is present in t₀₁₂
-- -- -> relate t₀ ⊢ α ⊏ β -> α ∈ t₀₁₂ -> β ∈ t₀₁₂ via their edit scripts
-- diff3⊏ (DelDel α p) (Del .α c) (Del .α d) (Del .α q) (here .α x) n m = {!!}
-- diff3⊏ (DelDel x p) (Del {ts₁ = ts₁} .x c) (Del .x d) (Del .x q) (there r) n m = diff3⊏ p c d q (there⊏+++ ts₁ r) n m
-- diff3⊏ (UpdUpd x y z p) c d q r n m = {!!}
-- diff3⊏ (CpyCpy {as = as} x p) (Cpy .x c) (Cpy .x d) (Cpy {ys = ys} .x q) r n m with dsplit {as} {ys} (⟦ diff3 _ _ p ⟧ q)
-- diff3⊏ (CpyCpy β p) (Cpy .β c) (Cpy .β d) (Cpy .β q) (here .β t) (∈-here .β) (∈-here .β) | ds₁ , ds₂ = {!!} -- n ≠ m
-- diff3⊏ (CpyCpy x p) (Cpy .x c) (Cpy .x d) (Cpy .x q) (here .x t) (∈-here .x) (∈-there m) | ds₁ , ds₂ = here x m
-- diff3⊏ (CpyCpy x p) (Cpy .x c) (Cpy .x d) (Cpy .x q) (here .x t) (∈-there n) (∈-here .x) | ds₁ , ds₂ = here x n
-- diff3⊏ (CpyCpy x p) (Cpy .x c) (Cpy .x d) (Cpy .x q) (here .x t) (∈-there n) (∈-there m) | ds₁ , ds₂ = here x m
-- diff3⊏ (CpyCpy β p) (Cpy .β c) (Cpy .β d) (Cpy .β q) (there r) (∈-here .β) (∈-here .β) | ds₁ , ds₂ = {!!} -- n ≠ m
-- diff3⊏ (CpyCpy x p) (Cpy .x c) (Cpy .x d) (Cpy .x q) (there r) (∈-here .x) (∈-there m) | ds₁ , ds₂ = here x m
-- diff3⊏ (CpyCpy x p) (Cpy {ts₁ = ts₁} .x c) (Cpy .x d) (Cpy .x q) (there r) (∈-there n) (∈-here .x) | ds₁ , ds₂ 
--   = {!!} -- there (diff3⊏ p c d {!q!} (there⊏+++ ts₁ r) {!n!} {!m!})
-- diff3⊏ (CpyCpy x p) (Cpy {ts₁ = ts₁} .x c) (Cpy .x d) (Cpy .x q) (there r) (∈-there n) (∈-there m) | ds₁ , ds₂ 
--   = there (diff3⊏ p c d {!q!} (there⊏+++ ts₁ r) {!n!} {!m!})
-- diff3⊏ (CpyDel x p) c d q r n m = {!!}
-- diff3⊏ (DelCpy x p) c d q r n m = {!!}
-- diff3⊏ (CpyUpd x y p) c d q r n m = {!!}
-- diff3⊏ (UpdCpy x y p) c d q r n m = {!!}
-- diff3⊏ (DelUpd x y p) c d q r n m = {!!}
-- diff3⊏ (UpdDel x y p) c d q r n m = {!!}
-- diff3⊏ (InsIns x y p) c d q r n m = {!!}
-- diff3⊏ (Ins₁ {as = as} x p) (Ins .x c) d (Ins {ys = ys} .x q) r n m with dsplit {as} {ys} (⟦ diff3 _ _ p ⟧ q)
-- diff3⊏ (Ins₁ x p) (Ins .x c) d (Ins .x q) (here α t) n m | ds₁ , ds₂ = {!!}
-- diff3⊏ (Ins₁ x p) (Ins .x c₁) d (Ins .x q) (there r) n m | ds₁ , ds₂ = {!!}
-- diff3⊏ (Ins₂ x p) c d q r n m = {!!}

-- -- diff3⊏ End End End End () n m
-- -- -- Here I have to relate "same" nodes
-- -- -- For instance here α meant by t₀ is deleted but still another α is present in t₀₁₂ (produced later in the edit script) 
-- -- diff3⊏ (DelDel α p) (Del .α c) (Del .α d) (Del .α q) (here₁ .α x) n m = {!!}
-- -- diff3⊏ (DelDel α p) (Del {ts₁ = ts₁} .α c) (Del .α d) (Del .α q) (here₂ .α x) n m = {!!}
-- -- diff3⊏ (DelDel x p) (Del {ts₁ = ts₁} .x c) (Del .x d) (Del .x q) (there r) n m = diff3⊏ p c d q (there⊏+++ ts₁ r) n m
-- -- diff3⊏ (UpdUpd x y z p) c d q r n m = {!!}
-- -- diff3⊏ (CpyCpy {as = as} α p) (Cpy .α c) (Cpy .α d) (Cpy {ys = ys} .α q) (here₁ .α x) n m with dsplit {as} {ys} (⟦ diff3 _ _ p ⟧ q)
-- -- diff3⊏ (CpyCpy α p) (Cpy .α c) (Cpy .α d) (Cpy .α q) (here₁ .α x) (∈-here .α) (∈-here .α) | ds₁ , ds₂ = {!here₁!}
-- -- diff3⊏ (CpyCpy α p) (Cpy .α c) (Cpy .α d) (Cpy .α q) (here₁ .α x) (∈-this n) (∈-here .α) | ds₁ , ds₂ = here₁ α n
-- -- diff3⊏ (CpyCpy α p) (Cpy .α c) (Cpy .α d) (Cpy .α q) (here₁ .α x) (∈-there n) (∈-here .α) | ds₁ , ds₂ = here₂ α n -- n ‌≠ m
-- -- diff3⊏ (CpyCpy α p) (Cpy .α c) (Cpy .α d) (Cpy .α q) (here₁ .α x) n (∈-this m) | ds₁ , ds₂ = here₁ α m
-- -- diff3⊏ (CpyCpy α p) (Cpy .α c) (Cpy .α d) (Cpy .α q) (here₁ .α x) n (∈-there m) | ds₁ , ds₂ = here₂ α m
-- -- diff3⊏ (CpyCpy {as = as} α p) (Cpy .α c) (Cpy .α d) (Cpy {ys = ys} .α q) (here₂ .α x) n m with dsplit {as} {ys} (⟦ diff3 _ _ p ⟧ q)
-- -- diff3⊏ (CpyCpy β p) (Cpy .β c) (Cpy .β d) (Cpy .β q) (here₂ .β x) (∈-here .β) (∈-here .β) | ds₁ , ds₂ = {!!} -- n ‌≠ m
-- -- diff3⊏ (CpyCpy α p) (Cpy .α c) (Cpy .α d) (Cpy .α q) (here₂ .α x) (∈-here .α) (∈-this m) | ds₁ , ds₂ = here₁ α m
-- -- diff3⊏ (CpyCpy α p) (Cpy .α c) (Cpy .α d) (Cpy .α q) (here₂ .α x) (∈-here .α) (∈-there m) | ds₁ , ds₂ = here₂ α m
-- -- diff3⊏ (CpyCpy α p) (Cpy .α c) (Cpy .α d) (Cpy .α q) (here₂ .α x) (∈-this n) (∈-here .α) | ds₁ , ds₂ = here₁ α n
-- -- diff3⊏ (CpyCpy α p) (Cpy .α c) (Cpy .α d) (Cpy .α q) (here₂ .α x) (∈-this n) (∈-this m) | ds₁ , ds₂ = here₁ α m
-- -- diff3⊏ (CpyCpy α p) (Cpy .α c) (Cpy .α d) (Cpy .α q) (here₂ .α x) (∈-this n) (∈-there m) | ds₁ , ds₂ = here₂ α m
-- -- diff3⊏ (CpyCpy α p) (Cpy .α c) (Cpy .α d) (Cpy .α q) (here₂ .α x) (∈-there n) (∈-here .α) | ds₁ , ds₂ = here₂ α n
-- -- diff3⊏ (CpyCpy α p) (Cpy .α c) (Cpy .α d) (Cpy .α q) (here₂ .α x) (∈-there n) (∈-this m) | ds₁ , ds₂ = here₁ α m
-- -- diff3⊏ (CpyCpy α p) (Cpy .α c) (Cpy .α d) (Cpy .α q) (here₂ .α x) (∈-there n) (∈-there m) | ds₁ , ds₂ = here₂ α m
-- -- diff3⊏ (CpyCpy {as = as} x p) (Cpy .x c) (Cpy .x d) (Cpy {ys = ys} .x q) (there r) n m with dsplit {as} {ys} (⟦ diff3 _ _ p ⟧ q)
-- -- diff3⊏ (CpyCpy β p) (Cpy .β c) (Cpy .β d) (Cpy .β q) (there r) (∈-here .β) (∈-here .β) | ds₁ , ds₂ = {!!} -- n ≠ m
-- -- diff3⊏ (CpyCpy x p) (Cpy .x c) (Cpy .x d) (Cpy .x q) (there r) (∈-here .x) (∈-this m) | ds₁ , ds₂ = here₁ x m
-- -- diff3⊏ (CpyCpy x p) (Cpy .x c) (Cpy .x d) (Cpy .x q) (there r) (∈-here .x) (∈-there m) | ds₁ , ds₂ = here₂ x m
-- -- diff3⊏ (CpyCpy x p) (Cpy .x c) (Cpy .x d) (Cpy .x q) (there r) (∈-this n) (∈-here .x) | ds₁ , ds₂ = {!!} -- ???
-- -- diff3⊏ (CpyCpy x p) (Cpy .x c) (Cpy .x d) (Cpy .x q) (there r) (∈-this n) (∈-this m) | ds₁ , ds₂ = {!!}
-- -- diff3⊏ (CpyCpy x p) (Cpy .x c) (Cpy .x d) (Cpy .x q) (there r) (∈-this n) (∈-there m) | ds₁ , ds₂ = {!!}
-- -- diff3⊏ (CpyCpy x p) (Cpy .x c) (Cpy .x d) (Cpy .x q) (there r) (∈-there n) m | ds₁ , ds₂ = {!!}
-- -- -- with diff3⊏ p c d q {!r!} {!n!} {!m!} 
-- -- -- ... | a = {!!}
-- -- diff3⊏ (CpyDel x p) c d q r n m = {!!}
-- -- diff3⊏ (DelCpy x p) c d q r n m = {!!}
-- -- diff3⊏ (CpyUpd x y p) c d q r n m = {!!}
-- -- diff3⊏ (UpdCpy x y p) c d q r n m = {!!}
-- -- diff3⊏ (DelUpd x y p) c d q r n m = {!!}
-- -- diff3⊏ (UpdDel x y p) c d q r n m = {!!}
-- -- diff3⊏ (InsIns x y p) c d q r n m = {!!}
-- -- diff3⊏ (Ins₁ x p) c d q r n m = {!!}
-- -- diff3⊏ (Ins₂ x p) c d q r n m = {!!}

-- --------------------------------------------------------------------------------

-- lemma⊏' : ∀ {as a bs b cs c ys} {α : View as a} {β : View bs b} {x : View cs c} {ts₁ : DList cs} {ts₂ : DList ys} 
--           -> Node x ts₁ ⊢ᵗ α ⊏' β -> ts₁ +++ ts₂ ⊢ α ⊏ β
-- lemma⊏' (here α x) = {!x!}
-- lemma⊏' (Node p) = {!there←!}

-- -- diff3⊏' : ∀ {xs ys zs ws as bs a b} {α : View as a} {β : View bs b} {t₀ : DList xs} {t₁ : DList ys} {t₂ : DList zs}
-- --            {e₀₁ : ES xs ys} {e₀₂ : ES xs zs} -> (p : e₀₁ ~ e₀₂) -> Diff t₀ t₁ e₀₁ -> Diff t₀ t₂ e₀₂ ->
-- --            let e₀₁₂ = diff3 e₀₁ e₀₂ p in (q : e₀₁₂ ↓ ws) ->
-- --            let t₀₁₂ = ⟦ e₀₁₂ ⟧ q in t₀ ⊢ α ⊏' β -> α ∈ t₀₁₂ -> β ∈ t₀₁₂ -> t₀₁₂ ⊢ α ⊏' β
-- -- diff3⊏' End End End End () n m
-- -- diff3⊏' (DelDel x p) (Del .x c) (Del .x d) (Del .x q) (this α t) n m = diff3⊏' p c d q {!t!} n m
-- -- diff3⊏' (DelDel x p) (Del {ts₁ = ts₁} .x c) (Del .x d) (Del .x q) (there r) n m = diff3⊏' p c d q (there⊏'+++ ts₁ r) n m
-- -- diff3⊏' (UpdUpd x y z p) c d q r n m = {!!}
-- -- diff3⊏' (CpyCpy {as = as} x p) (Cpy .x c) (Cpy .x d) (Cpy {ys = ys} .x q) r n m with dsplit {as} {ys} (⟦ diff3 _ _ p ⟧ q)
-- -- diff3⊏' (CpyCpy β p) (Cpy .β c) (Cpy .β d) (Cpy .β q) (this .β t) (∈-here .β) (∈-here .β) | ds₁ , ds₂ = {!!} -- n ≠ m
-- -- diff3⊏' (CpyCpy x p) (Cpy .x c) (Cpy .x d) (Cpy .x q) (this .x t) (∈-here .x) (∈-this m) | ds₁ , ds₂ = this x (here x m)
-- -- diff3⊏' (CpyCpy x p) (Cpy .x c) (Cpy .x d) (Cpy .x q) (this .x t) (∈-here .x) (∈-there m) | ds₁ , ds₂ = there {!!}
-- -- diff3⊏' (CpyCpy x p) (Cpy .x c) (Cpy .x d) (Cpy .x q) (this α t) (∈-this n) m | ds₁ , ds₂ = {!!}
-- -- diff3⊏' (CpyCpy x p) (Cpy .x c) (Cpy .x d) (Cpy .x q) (this α t) (∈-there n) m | ds₁ , ds₂ = {!!}
-- -- diff3⊏' (CpyCpy x p) (Cpy .x c) (Cpy .x d) (Cpy .x q) (there r) n m | ds₁ , ds₂ = {!!}
-- -- diff3⊏' (CpyDel x p) c d q r n m = {!!}
-- -- diff3⊏' (DelCpy x p) c d q r n m = {!!}
-- -- diff3⊏' (CpyUpd x y p) c d q r n m = {!!}
-- -- diff3⊏' (UpdCpy x y p) c d q r n m = {!!}
-- -- diff3⊏' (DelUpd x y p) c d q r n m = {!!}
-- -- diff3⊏' (UpdDel x y p) c d q r n m = {!!}
-- -- diff3⊏' (InsIns x y p) c d q r n m = {!!}
-- -- diff3⊏' (Ins₁ x p) c d q r n m = {!!}
-- -- diff3⊏' (Ins₂ x p) c d q r n m = {!!}

-- --------------------------------------------------------------------------------

-- -- What is produced by an edit script
-- data Output : ∀ {xs a} -> View xs a -> ES₃ -> Set where
--   hereIns : ∀ {as e a} (x : View as a) -> Output x (Ins x e)
--   hereCpy : ∀ {as e a} (x : View as a) -> Output x (Cpy x e)
--   hereUpd : ∀ {as e a bs} (x : View as a) (y : View bs a) -> Output x (Upd x y e)
--   Ins : ∀ {as e bs b a} {y : View bs b} (x : View as a) -> Output y e -> Output y (Ins x e)
--   Del : ∀ {as e bs b a} {y : View bs b} (x : View as a) -> Output y e -> Output y (Del x e)
--   Cpy : ∀ {as e bs b a} {y : View bs b} (x : View as a) -> Output y e -> Output y (Cpy x e)
--   Upd : ∀ {as e a bs cs c} {z : View cs c} (x : View as a) (y : View bs a) -> Output z e -> Output z (Upd x y e)

-- -- This is in general not true -> counterexample.
-- -- A child might end up being a sibling of his parent in the merged version
-- -- diff3≺ : ∀ {xs ys zs ws as bs a b} {α : View as a} {β : View bs b} {t₀ : DList xs} {t₁ : DList ys} {t₂ : DList zs}
-- --            {e₀₁ : ES xs ys} {e₀₂ : ES xs zs} -> (p : e₀₁ ~ e₀₂) -> Diff t₀ t₁ e₀₁ -> Diff t₀ t₂ e₀₂ ->
-- --            let e₀₁₂ = diff3 e₀₁ e₀₂ p in (q : e₀₁₂ ↓ ws) ->
-- --            let t₀₁₂ = ⟦ e₀₁₂ ⟧ q in t₀ ⊢ α ≺ β -> α ∈ t₀₁₂ -> β ∈ t₀₁₂ -> t₀₁₂ ⊢ α ≺ β
-- -- diff3≺ End c d q () m n
-- -- -- I need to relate t₀ and t₀₁₂ somehow, in particular I need to rule out this case in which
-- -- -- α ∈ t₀₁₂ is here : since α is deleted why should we find it in t₀₁₂ ? -> Maybe we should invert
-- -- -- the order of the arguments: first pattern match on ∈ and then on ⊢.
-- -- diff3≺ (DelDel α p) (Del .α c) (Del .α d) (Del .α q) (here .α x) m n = diff3≺ p c d q {!!} m n
-- -- diff3≺ (DelDel α p) (Del {ts₁ = ts₁} .α c) (Del .α d) (Del .α q) (there r) m n = diff3≺ p c d q (there+++ ts₁ r) m n
-- -- diff3≺ (UpdUpd x y z p) c d q r m n = {!!}
-- -- diff3≺ (CpyCpy {as = as} α p) (Cpy .α c) (Cpy .α d) (Cpy {ys = ys} .α q) (here .α x) m n 
-- --   with dsplit {as} {ys} (⟦ diff3 _ _ p ⟧ q)
-- -- -- X can be discharged assuming α ≠ β
-- -- diff3≺ (CpyCpy β p) (Cpy .β c) (Cpy .β d) (Cpy .β q) (here .β x) (∈-here .β) (∈-here .β) | ds₁ , ds₂ = {!!} -- X
-- -- diff3≺ (CpyCpy α p) (Cpy .α c) (Cpy .α d) (Cpy .α q) (here .α x) (∈-here .α) (∈-this n) | ds₁ , ds₂ = here α n
-- -- diff3≺ (CpyCpy α p) (Cpy .α c) (Cpy .α d) (Cpy .α q) (here .α x) (∈-here .α) (∈-there n) | ds₁ , ds₂ = {!there!} -- ???
-- -- diff3≺ (CpyCpy α p) (Cpy .α c) (Cpy .α d) (Cpy .α q) (here .α x) (∈-this m) (∈-here .α) | ds₁ , ds₂ = {!!} -- X
-- -- diff3≺ (CpyCpy α p) (Cpy .α c) (Cpy .α d) (Cpy .α q) (here .α x) (∈-this m) (∈-this n) | ds₁ , ds₂ = here α n 
-- -- diff3≺ (CpyCpy α p) (Cpy .α c) (Cpy .α d) (Cpy .α q) (here .α x) (∈-this m) (∈-there n) | ds₁ , ds₂ = {!!} -- ???
-- -- diff3≺ (CpyCpy α p) (Cpy .α c) (Cpy .α d) (Cpy .α q) (here .α x) (∈-there m) (∈-here .α) | ds₁ , ds₂ = {!!} -- X
-- -- diff3≺ (CpyCpy α p) (Cpy .α c) (Cpy .α d) (Cpy .α q) (here .α x) (∈-there m) (∈-this n) | ds₁ , ds₂ = here α n
-- -- diff3≺ (CpyCpy α p) (Cpy .α c) (Cpy .α d) (Cpy .α q) (here .α x) (∈-there m) (∈-there n) | ds₁ , ds₂ = here α {!!} -- ???
-- -- diff3≺ (CpyCpy {as = as} x p) (Cpy .x c) (Cpy .x d) (Cpy {ys = ys} .x q) (there r) m n with dsplit {as} {ys} (⟦ diff3 _ _ p ⟧ q )
-- -- -- Something is wrong with my definition: m should be only there or this, so that a recursive call can be made
-- -- -- -> relation between t₀ and t₀₁₂ missing ? 
-- -- diff3≺ (CpyCpy x p) (Cpy .x c) (Cpy .x d) (Cpy .x q) (there r) (∈-here .x) n | ds₁ , ds₂ = {!!} 
-- -- diff3≺ (CpyCpy x p) (Cpy .x c) (Cpy .x d) (Cpy .x q) (there r) (∈-this m) n | ds₁ , ds₂ = {!!}
-- -- diff3≺ (CpyCpy x p) (Cpy .x c) (Cpy .x d) (Cpy .x q) (there r) (∈-there m) (∈-here .x) | ds₁ , ds₂ = {!!}
-- -- diff3≺ (CpyCpy x p) (Cpy .x c) (Cpy .x d) (Cpy .x q) (there r) (∈-there m) (∈-this n) | ds₁ , ds₂ = {!!}
-- -- diff3≺ (CpyCpy x p) (Cpy .x c) (Cpy .x d) (Cpy .x q) (there r) (∈-there m) (∈-there n) | ds₁ , ds₂ = there {!!} -- (diff3≺ p c d {!q!} {!r!} m n)
-- -- diff3≺ (CpyDel x p) c d q r m n = {!!}
-- -- diff3≺ (DelCpy x p) c d q r m n = {!!}
-- -- diff3≺ (CpyUpd x y p) c d q r m n = {!!}
-- -- diff3≺ (UpdCpy x y p) c d q r m n = {!!}
-- -- diff3≺ (DelUpd x y p) c d q r m n = {!!}
-- -- diff3≺ (UpdDel x y p) c d q r m n = {!!}
-- -- diff3≺ (InsIns x y p) c d q r m n = {!!}
-- -- diff3≺ (Ins₁ x p) c d q r m n = {!!}
-- -- diff3≺ (Ins₂ x p) c d q r m n = {!!}
