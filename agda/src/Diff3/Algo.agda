module Diff3.Algo where

open import Diff3.Core

open import Data.List
open import Data.Empty
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality hiding ([_])

--------------------------------------------------------------------------------
-- When ES₃ is well typed ?
--------------------------------------------------------------------------------

open import Data.Empty

data _⇒_ : ∀ {xs} -> ES₃ xs -> List Set -> Set₁ where
  [] : [] ⇒ []
  _∷_ : ∀ {as bs cs ds xs ys} {v : Val as bs} {w : Val cs ds} {e : ES₃ (as ++ xs)} -> 
          (f : v ~> w) -> e ⇒ cs ++ ys -> f ∷ e ⇒ ds ++ ys

infixr 3 _⇒_

∥_∥  : ∀ {xs ys} {e : ES₃ xs} -> e ⇒ ys -> ES xs ys
∥ [] ∥ = []
∥ f ∷ p ∥ = f ∷ ∥ p ∥

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

open import Data.Product

⊥ᶜ-⇒ : ∀ {as bs cs ds es fs xs ws} {e : ES₃ (as ++ xs)} 
               {u : Val as bs} {v : Val cs ds} {w : Val es fs} {c : Conflict u v w} -> 
               ¬ (c ∷ᶜ e ⇒ ws)
⊥ᶜ-⇒ ()

_isPrefixOf_ : ∀ (as bs : List Set) -> Dec (∃ λ cs -> bs ≡ as ++ cs)   
[] isPrefixOf [] = yes ([] , refl)
(x ∷ as) isPrefixOf [] = no {!!}
[] isPrefixOf (x ∷ bs) = no {!!}
(a ∷ as) isPrefixOf (b ∷ bs) with eq? a b 
(a ∷ as) isPrefixOf (.a ∷ bs) | yes refl with as isPrefixOf bs
(a ∷ as) isPrefixOf (.a ∷ bs) | yes refl | yes (proj₁ , proj₂) = {!!}
(a ∷ as) isPrefixOf (.a ∷ bs) | yes refl | no ¬p = no {!!}
(a ∷ as) isPrefixOf (b ∷ bs) | no ¬p = {!!}

aux : ∀ {xs as bs cs ds} {e : ES₃ (as ++ xs)} {v : Val as bs} {w : Val cs ds} {x : v ~> w} -> 
         ¬ (∃ λ ws -> e ⇒ ws) -> ¬ (∃ λ ws -> x ∷ e ⇒ ws)
aux ¬p (._ , (x ∷ p)) = ¬p (_ , p)

-- aux₂ : ∀ {xs as bs cs ds} {v : Val as bs} {w : Val cs ds} {x : v ~> w} {e : ES₃ (as ++ xs)} ->
--          (∃ λ ws -> e ⇒ ws) -> (∀ ws -> ¬ ∃ λ ys -> ws ≡ cs ++ ys) -> ¬ (∃ λ ws -> x ∷ e ⇒ ws)
-- aux₂ (ws , p) ¬p (._ , (_∷_ {cs = cs} {ds = ds} {ys = ys} x e)) = ¬p (cs ++ ys) (ys , refl)

aux₃ : ∀ {xs as bs cs ds ws} {v : Val as bs} {w : Val cs ds} {x : v ~> w} {e : ES₃ (as ++ xs)} ->
         x ∷ e ⇒ ws -> ∃ λ ys -> ws ≡ ds ++ ys × e ⇒ (cs ++ ys)
aux₃ (_∷_ {ys = ys} x p) = ys , (refl , p) 

aux₂ : ∀ {xs as bs cs ds ws} {v : Val as bs} {w : Val cs ds} {x : v ~> w} {e : ES₃ (as ++ xs)} ->
         ¬ (∃ λ ys -> ws ≡ cs ++ ys) -> ¬ (∃ λ us -> x ∷ e ⇒ us)
aux₂ ¬p (_ , p) with aux₃ p
aux₂ {x = x} ¬p (._ , p) | ys , (refl , p') = {!!}

lemma : ∀ {xs} (e : ES₃ xs) -> Dec (∃ λ ws -> e ⇒ ws)
lemma [] = yes ([] , [])
lemma (x ∷ e) with lemma e
lemma (_∷_ {cs = cs} x e) | yes (ws , p) with cs isPrefixOf ws
lemma (_∷_ {ds = ds} x e) | yes (._ , p) | yes (ys , refl) = yes ((ds ++ ys) , (x ∷ p))
lemma (x ∷ e) | yes (ws , p) | no ¬p = no {!!} -- (aux₂ (ws , p) {!!}) -- (aux₂ ? {!¬p!}) 
lemma (x ∷ e) | no ¬p = no (aux ¬p)
lemma (c ∷ᶜ e) = no (λ p → ⊥ᶜ-⇒ (proj₂ p))


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

-- Well-typed ES₃ can be converted to well-typed ES
-- toES : ∀ {xs ys zs ws} {e₀₁ : ES xs ys} {e₀₂ : ES xs zs} (p : e₀₁ ~ e₀₂) -> 
--        let e₀₁₂ = diff3 e₀₁ e₀₂ p in (q : e₀₁₂ ↓ ws) -> ES xs ws
-- toES End End = End
-- toES (DelDel x p) (Del .x q) = Del x (toES p q)
-- toES (UpdUpd x y z p) q with y =?= z
-- toES (UpdUpd x y .y p) (Upd .x .y q) | yes refl = Upd x y (toES p q)
-- toES (UpdUpd x y z p) () | no ¬p
-- toES (DelUpd x y p) q with x =?= y
-- toES (DelUpd x .x p) (Del .x q) | yes refl = Del x (toES p q)
-- toES (DelUpd x y p) () | no ¬p
-- toES (UpdDel x y p) q with x =?= y
-- toES (UpdDel x .x p) (Del .x q) | yes refl = Del x (toES p q)
-- toES (UpdDel x y p) () | no ¬p
-- toES (InsIns {a = a} {b = b} x y p) q with eq? a b
-- toES (InsIns x y p) q | yes refl with x =?= y
-- toES (InsIns x .x p) (Ins .x q) | yes refl | yes refl = Ins x (toES p q)
-- toES (InsIns x y p) () | yes refl | no ¬p
-- toES (InsIns x y p) () | no ¬p
-- toES (Ins₁ x p) (Ins .x q) = Ins x (toES p q)
-- toES (Ins₂ x p) (Ins .x q) = Ins x (toES p q)

--------------------------------------------------------------------------------

-- diff3 is reflexive. Any edit script run against itself succeeds
-- diff3-refl : ∀ {xs ys} (e : ES xs ys) -> diff3 e e (~-refl e) ↓ ys
-- diff3-refl (Ins {a = a} x e) with eq? a a
-- diff3-refl (Ins x e) | yes refl with x =?= x
-- diff3-refl (Ins x e) | yes refl | yes refl = Ins x (diff3-refl e)
-- diff3-refl (Ins x e) | yes refl | no ¬p = ⊥-elim (¬p refl)
-- diff3-refl (Ins x e) | no ¬p = ⊥-elim (¬p refl)
-- diff3-refl (Del x e) = Del x (diff3-refl e)
-- diff3-refl (Upd x y e) with y =?= y
-- diff3-refl (Upd x y e) | yes refl = Upd x y (diff3-refl e)
-- diff3-refl (Upd x y e) | no ¬p = ⊥-elim (¬p refl)
-- diff3-refl End = End

-- diff3-sym : ∀ {xs ys zs} {e₁ : ES xs ys} {e₂ : ES xs zs} -> (p : e₁ ~ e₂) -> 
--              let e₁₂ = diff3 e₁ e₂ p in NoCnf e₁₂ -> e₁₂ ≡ diff3 e₂ e₁ (~-sym p)
-- diff3-sym End End = refl
-- diff3-sym (DelDel x p) (Del .x q) = cong (Del x) (diff3-sym p q)
-- diff3-sym (UpdUpd x y z p) q with y =?= z
-- diff3-sym (UpdUpd x y .y p) q | yes refl with y =?= y
-- diff3-sym (UpdUpd x y .y p) (Upd .x .y q) | yes refl | yes refl = cong (Upd x y) (diff3-sym p q)
-- diff3-sym (UpdUpd x y .y p) q | yes refl | no ¬p = ⊥-elim (¬p refl)
-- diff3-sym (UpdUpd x y z p) () | no ¬p
-- diff3-sym (DelUpd x y p) q with x =?= y
-- diff3-sym (DelUpd x .x p) (Del .x q) | yes refl = cong (Del x) (diff3-sym p q)
-- diff3-sym (DelUpd x y p) () | no ¬p
-- diff3-sym (UpdDel x y p) q with x =?= y
-- diff3-sym (UpdDel x .x p) (Del .x q) | yes refl = cong (Del x) (diff3-sym p q)
-- diff3-sym (UpdDel x y p) () | no ¬p
-- diff3-sym (InsIns {a = a} {b = b} x y p) q with eq? a b
-- diff3-sym (InsIns x y p) q | yes refl with x =?= y
-- diff3-sym (InsIns {a = a} x .x p) q | yes refl | yes refl with eq? a a
-- diff3-sym (InsIns x .x p) q | yes refl | yes refl | yes refl with x =?= x
-- diff3-sym (InsIns x .x p) (Ins .x q) | yes refl | yes refl | yes refl | yes refl = cong (Ins x) (diff3-sym p q)
-- diff3-sym (InsIns x .x p) q | yes refl | yes refl | yes refl | no ¬p = ⊥-elim (¬p refl)
-- diff3-sym (InsIns x .x p) q | yes refl | yes refl | no ¬p = ⊥-elim (¬p refl)
-- diff3-sym (InsIns x y p) () | yes refl | no ¬p
-- diff3-sym (InsIns x y p) () | no ¬p
-- diff3-sym (Ins₁ x p) (Ins .x q) = cong (Ins x) (diff3-sym p q)
-- diff3-sym (Ins₂ x p) (Ins .x q) = cong (Ins x) (diff3-sym p q)

--------------------------------------------------------------------------------

-- -- well-typedness is symmetric
-- ↓-sym : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} -> (p : e₁ ~ e₂) -> diff3 e₁ e₂ p ↓ ws -> diff3 e₂ e₁ (~-sym p) ↓ ws
-- ↓-sym p q rewrite sym (diff3-sym p (diff3-wt p q)) = q

--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Relates Diff and Diff₃ and diff3

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
