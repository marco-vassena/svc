module Diff3.Algo where

open import Lemmas
open import Diff3.Core

open import Data.Sum
open import Data.List
open import Data.Empty
open import Data.Maybe
open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality hiding ([_])

--------------------------------------------------------------------------------

-- The diff₃ algorithm
_⨆_ : ∀ {xs ys zs} (e₁ : ES xs ys) (e₂ : ES xs zs) -> {{ p : e₁ ⋎ e₂ }} -> ES₃ xs
_⨆_ .[] .[] {{nil}} = []
_⨆_ ._ ._ {{cons x y p}} with mergeOrConflict x y
_⨆_ ._ ._ {{cons x y p}} | inj₁ (c , _) = c ∷ᶜ _⨆_ _ _ {{p}}
_⨆_ ._ ._ {{cons x y p}} | inj₂ (z , _) = z ∷ _⨆_ _ _ {{p}}

--------------------------------------------------------------------------------
-- When ES₃ is well typed ?
--------------------------------------------------------------------------------

open import Data.Empty

data _⇒_ : ∀ {xs} -> ES₃ xs -> List Set -> Set₁ where
  [] : [] ⇒ []
  _∷_ : ∀ {as bs cs ds xs ys} {v : Val as bs} {w : Val cs ds} {e : ES₃ (as ++ xs)} -> 
          (f : v ~> w) -> e ⇒ cs ++ ys -> f ∷ e ⇒ ds ++ ys

infixr 3 _⇒_

∥_∥  : ∀ {xs ys} (e : ES₃ xs) -> {{q : e ⇒ ys }}-> ES xs ys
∥_∥ .[] {{[]}} = []
∥_∥ (.f ∷ e) {{f ∷ q}} = f ∷ ∥ e ∥

data _↦_ : ∀ {xs ys zs} {e₁ : ES xs ys} {e₂ : ES xs zs} -> e₁ ⋎ e₂ -> List Set -> Set₁ where
  nil : nil ↦ []
  cons : ∀ {as bs cs ds es fs gs hs xs ys zs ws} ->
           {u : Val as bs} {v : Val cs ds} {w : Val es fs} {z : Val gs hs} ->
           {e₁ : ES (as ++ xs) (cs ++ ys)} {e₂ : ES (as ++ xs) (es ++ zs)} {p : e₁ ⋎ e₂} ->
           (f : u ~> v) (g : u ~> w) (h : u ~> z) (m : f ⊔ g ↧ h) -> p ↦ (gs ++ ws) -> cons f g p ↦ (hs ++ ws)

_,_↣_ : ∀ {xs ys zs} (e₁ : ES xs ys) (e₂ : ES xs zs) {{p : e₁ ⋎ e₂}} -> List Set -> Set₁
_,_↣_ e₁ e₂ {{p}} ws = p ↦ ws

-- Sufficient
↣-⇒ : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES₃ xs} {{p : e₁ ⋎ e₂}} -> 
         Diff₃ e₁ e₂ e₃ -> e₁ , e₂ ↣ ws -> e₃ ⇒ ws
↣-⇒ nil nil = []
↣-⇒ (merge m d) (cons f g h m' q) with mergeDeterministic m m'
↣-⇒ (merge m d) (cons f g h m' q) | refl = h ∷ ↣-⇒ d q
↣-⇒ (conflict u d) (cons f g h m q) = ⊥-elim (mergeConflictExclusive m u)

-- Necessary conditions
⇒-↣ : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES₃ xs} {{p : e₁ ⋎ e₂}} -> 
         Diff₃ e₁ e₂ e₃ -> e₃ ⇒ ws -> e₁ , e₂ ↣ ws
⇒-↣ nil [] = nil
⇒-↣ (merge {f = f} {g = g} m d) (h ∷ q) = cons f g h m (⇒-↣ d q)

lemma : ∀ {xs} (e : ES₃ xs) -> Maybe (∃ λ ws -> e ⇒ ws)
lemma [] = just ([] , [])
lemma (x ∷ e) with lemma e
lemma (_∷_ {cs = cs} x e) | just (ws , p) with isPrefixOf {_≟_ = eq?} cs  ws
lemma (_∷_ {ds = ds} x e) | just (._ , p) | just (ws , refl) = just ((ds ++ ws) , (x ∷ p))
lemma (x ∷ e) | just (ws , proj₂) | nothing = nothing
lemma (x ∷ e) | nothing = nothing
lemma (c ∷ᶜ e) = nothing

--------------------------------------------------------------------------------

-- Well-typed implies no conflicts
-- diff3-wt : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} -> (p : e₁ ~ e₂) -> diff3 e₁ e₂ p ↓ ws -> NoCnf (diff3 e₁ e₂ p)
-- diff3-wt End End = End
-- diff3-wt (DelDel x p) (Del .x q) = Del x (diff3-wt p q)
-- diff3-wt (UpdUpd x y z p) q with y =?= z
-- diff3-wt (UpdUpd x y .y p) (Upd .x .y q) | yes refl = Upd x y (diff3-wt p q)
-- diff3-wt (UpdUpd x y z p) () | no ¬p
-- diff3-wt (DelUpd x y p) q with x =?= y
-- diff3-wt (DelUpd x .x p) (Del .x q) | yes refl = Del x (diff3-wt p q)
-- diff3-wt (DelUpd x y p) () | no ¬p
-- diff3-wt (UpdDel x y p) q with x =?= y
-- diff3-wt (UpdDel x .x p) (Del .x q) | yes refl = Del x (diff3-wt p q)
-- diff3-wt (UpdDel x y p) () | no ¬p
-- diff3-wt (InsIns {a = a} {b = b} x y p) q with eq? a b
-- diff3-wt (InsIns x y p) q | yes refl with x =?= y
-- diff3-wt (InsIns x .x p) (Ins .x q) | yes refl | yes refl = Ins x (diff3-wt p q)
-- diff3-wt (InsIns x y p) () | yes refl | no ¬p
-- diff3-wt (InsIns x y p) () | no ¬p
-- diff3-wt (Ins₁ x p) (Ins .x q) = Ins x (diff3-wt p q)
-- diff3-wt (Ins₂ x p) (Ins .x q) = Ins x (diff3-wt p q)

--------------------------------------------------------------------------------

-- diff3 is reflexive. Any edit script run against itself succeeds

Diff₃-refl : ∀ {xs ys} {e : ES xs ys} {e₃ : ES₃ xs} -> (⋎-refl e) ⇓ e₃ -> e₃ ⇒ ys
Diff₃-refl nil = []
Diff₃-refl (merge (Id₁ f .f v≠w) d) = ⊥-elim (v≠w refl)
Diff₃-refl (merge (Id₂ f .f v≠w) d) = ⊥-elim (v≠w refl)
Diff₃-refl (merge (Idem f) d) = f ∷ (Diff₃-refl d)
Diff₃-refl (conflict (InsIns f .f α≠β) d) = ⊥-elim (α≠β refl)
Diff₃-refl (conflict (UpdUpd f .f α≠β α≠γ β≠γ) d) = ⊥-elim (β≠γ refl)

--------------------------------------------------------------------------------

-- well-typedness is symmetric
↦-sym : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {p : e₁ ⋎ e₂} -> p ↦ ws -> (⋎-sym p) ↦ ws
↦-sym nil = nil
↦-sym (cons f g h m q) = cons g f h (↧-sym m) (↦-sym q)

--------------------------------------------------------------------------------
-- Relation between Diff₃ and ⨆

-- Sufficient condition: ⨆ => Diff₃
-- It shows that Diff₃ can safely represent the outcome of ⨆. 
Diff₃-suf : ∀ {xs ys zs} {e₁ : ES xs ys} {e₂ : ES xs zs} -> (p : e₁ ⋎ e₂) -> Diff₃ e₁ e₂ (e₁ ⨆ e₂)
Diff₃-suf (cons x y p) with mergeOrConflict x y
Diff₃-suf (cons x y p) | inj₁ (c , u) = conflict u (Diff₃-suf p)
Diff₃-suf (cons x y p) | inj₂ (z , m) = merge m (Diff₃-suf p)
Diff₃-suf nil = nil 

-- Necessary conditions : Diff₃ => ⨆ 
-- Given Diff₃ e₁ e₂ e₃, e₃ is the result of e₁ ⨆ e₂
Diff₃-nec : ∀ {xs ys zs} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES₃ xs} {p : e₁ ⋎ e₂} -> 
              Diff₃ e₁ e₂ e₃ -> e₃ ≡ e₁ ⨆ e₂
Diff₃-nec nil = refl
Diff₃-nec (merge {f = f} {g = g} m q) with mergeOrConflict f g
Diff₃-nec (merge m q) | inj₁ (c , u) = ⊥-elim (mergeConflictExclusive m u)
Diff₃-nec (merge m q) | inj₂ (h , m') with mergeDeterministic m m'
Diff₃-nec (merge m q) | inj₂ (h , m') | refl = cong (_∷_ h) (Diff₃-nec q)
Diff₃-nec (conflict {f = f} {g = g} u q) with mergeOrConflict f g
Diff₃-nec (conflict u q) | inj₁ (c , u') with conflictDeterministic u u'
Diff₃-nec (conflict u q) | inj₁ (c , u') | refl = cong (_∷ᶜ_ c) (Diff₃-nec q)
Diff₃-nec (conflict u q) | inj₂ (h , m) = ⊥-elim (mergeConflictExclusive m u)

-- Diff₃ <=> ⨆ , therefore all the properties that hold for Diff₃ hold also for ⨆.

--------------------------------------------------------------------------------
-- Relation between well-typedness and Merged₃

Merged₃-suf : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {p : e₁ ⋎ e₂} {e₃ : ES₃ xs} ->
                Diff₃ e₁ e₂ e₃ -> (q : e₃ ⇒ ws) -> Merged₃ {ws = ws} e₁ e₂ ∥ e₃ ∥
Merged₃-suf nil [] = nil
Merged₃-suf (merge m d) (f ∷ q) = cons m (Merged₃-suf d q)

-- Here we need to explicitly pattern match on h to avoid unification issues ultimately 
-- due to _++_ in the _∷_ constructor for ⇒. 
Merged₃-nec : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {p : e₁ ⋎ e₂} {e₃ : ES xs ws} {e₃' : ES₃ xs} ->
                 Merged₃ e₁ e₂ e₃ -> Diff₃ e₁ e₂ e₃' -> (q : e₃' ⇒ ws) -> e₃ ≡ ∥ e₃' ∥
Merged₃-nec nil nil [] = refl
Merged₃-nec (cons m p) (merge m' d) q with mergeDeterministic m m'
Merged₃-nec (cons m p) (merge {h = Ins α} m' d) (.(Ins α) ∷ q) | refl = cong (_∷_ (Ins α)) (Merged₃-nec p d q)
Merged₃-nec (cons m p) (merge {h = Del α} m' d) (.(Del α) ∷ q) | refl = cong (_∷_ (Del α)) (Merged₃-nec p d q)
Merged₃-nec (cons m p) (merge {h = Upd α β} m' d) (.(Upd α β) ∷ q) | refl = cong (_∷_ (Upd α β)) (Merged₃-nec p d q)
Merged₃-nec (cons m p) (merge {h = Nop} m' d) (.Nop ∷ q) | refl = cong (_∷_ Nop) (Merged₃-nec p d q)
Merged₃-nec (cons m p) (conflict u d) ()

-- Merged₃ and Diff₃ are in a one-to-one relationship given the well-typedness of e₃.
-- Therefore we can use Merged₃ to reason about well-typed conflictless Diff₃.

--------------------------------------------------------------------------------
-- Relate Diff and Diff₃ and diff3

-- Define data type for well-typed WT-Diff3.
-- Show that Diff3 e1 e2 e3 + WT e3 <=> WT-Diff3

-- diff₃-Diff-suf : ∀ {xs ys zs ws} {x : DList xs} {y : DList ys} {z : DList zs}
--                  {e₁ : ES xs ys} {e₂ : ES xs zs} (d₁ : Diff x y e₁) (d₂ : Diff x z e₂) ->
--                  let p = Diff~ d₁ d₂ in
--                  let e₃ = diff3 e₁ e₂ p in (q : e₃ ↓ ws) -> Diff₃ e₁ e₂ (toES p q)
-- diff₃-Diff-suf d₁ d₂ q = diff₃-suf (Diff~ d₁ d₂) q

-- diff₃-Diff-nec : ∀ {xs ys zs ws} {x : DList xs} {y : DList ys} {z : DList zs}
--                  {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} (d₁ : Diff x y e₁) (d₂ : Diff x z e₂) ->
--                  let p = Diff~ d₁ d₂ in
--                  let e₁₂ = diff3 e₁ e₂ p in (q : e₁₂ ↓ ws) -> Diff₃ e₁ e₂ e₃ -> e₃ ≡ toES p q
-- diff₃-Diff-nec d₁ d₂ q = diff₃-nec (Diff~ d₁ d₂) q
