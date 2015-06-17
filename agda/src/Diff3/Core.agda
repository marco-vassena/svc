module Diff3.Core where

open import Diff.Core public
open import EditScript.Core public
open import EditScript.Aligned public
open import EditScript.Mapping

open import Relation.Nullary
open import Data.Product
open import Data.Sum
open import Data.List
open import Relation.Binary

--------------------------------------------------------------------------------

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

-- Reifies the outcome of diff₃
data RawDiff₃ : ∀ {xs ys zs} (e₁ : ES xs ys) (e₂ : ES xs zs) ->  ES₃ -> Set₁ where
  EndEnd : RawDiff₃ End End End
  InsIns : ∀ {as a xs ys zs e₃} {e₁ : ES xs (as ++ ys)} {e₂ : ES xs (as ++ zs)} (α : View as a) -> 
           RawDiff₃ e₁ e₂ e₃ -> RawDiff₃ (Ins α e₁) (Ins α e₂) (Ins α e₃)
  Ins₁ : ∀ {as a xs ys zs e₃} {e₁ : ES xs (as ++ ys)} {e₂ : ES xs zs} {{i : ¬Ins e₂}} (α : View as a) -> 
           RawDiff₃ e₁ e₂ e₃ -> RawDiff₃ (Ins α e₁) e₂ (Ins α e₃)
  Ins₂ : ∀ {as a xs ys zs e₃} {e₁ : ES xs ys} {e₂ : ES xs (as ++ zs)} {{i : ¬Ins e₁}} (α : View as a) -> 
           RawDiff₃ e₁ e₂ e₃ -> RawDiff₃ e₁ (Ins α e₂) (Ins α e₃)
  DelDel : ∀ {as a xs ys zs e₃} {e₁ : ES (as ++ xs) ys} {e₂ : ES (as ++ xs) zs} (α : View as a) -> 
             RawDiff₃ e₁ e₂ e₃ -> RawDiff₃ (Del α e₁) (Del α e₂) (Del α e₃)
  CpyCpy : ∀ {as a xs ys zs e₃} {e₁ : ES (as ++ xs) (as ++ ys)} {e₂ : ES (as ++ xs) (as ++ zs)} (α : View as a) -> 
             RawDiff₃ e₁ e₂ e₃ -> RawDiff₃ (Cpy α e₁) (Cpy α e₂) (Cpy α e₃)
  UpdUpd : ∀ {as bs a xs ys zs e₃} {e₁ : ES (as ++ xs) (bs ++ ys)} {e₂ : ES (as ++ xs) (bs ++ zs)} 
             (α : View as a) (β : View bs a) -> RawDiff₃ e₁ e₂ e₃ -> RawDiff₃ (Upd α β e₁) (Upd α β e₂) (Upd α β e₃)
  CpyDel : ∀ {as a xs ys zs e₃} {e₁ : ES (as ++ xs) (as ++ ys)} {e₂ : ES (as ++ xs) zs} (α : View as a) ->
              RawDiff₃ e₁ e₂ e₃ -> RawDiff₃ (Cpy α e₁) (Del α e₂) (Del α e₃)
  DelCpy : ∀ {as a xs ys zs e₃} {e₁ : ES (as ++ xs) ys} {e₂ : ES (as ++ xs) (as ++ zs)} (α : View as a) ->
              RawDiff₃ e₁ e₂ e₃ -> RawDiff₃ (Del α e₁) (Cpy α e₂) (Del α e₃)
  CpyUpd : ∀ {as bs a xs ys zs e₃} {e₁ : ES (as ++ xs) (as ++ ys)} {e₂ : ES (as ++ xs) (bs ++ zs)} (α : View as a) (β : View bs a) ->
              RawDiff₃ e₁ e₂ e₃ -> RawDiff₃ (Cpy α e₁) (Upd α β e₂) (Upd α β e₃)
  UpdCpy : ∀ {as bs a xs ys zs e₃} {e₁ : ES (as ++ xs) (bs ++ ys)} {e₂ : ES (as ++ xs) (as ++ zs)} (α : View as a) (β : View bs a) ->
              RawDiff₃ e₁ e₂ e₃ -> RawDiff₃ (Upd α β e₁) (Cpy α e₂) (Upd α β e₃)
  DelUpdC : ∀ {as bs a xs ys zs e₃} {e₁ : ES (as ++ xs) ys} {e₂ : ES (as ++ xs) (bs ++ zs)} (α : View as a) (β : View bs a) ->
              RawDiff₃ e₁ e₂ e₃ -> RawDiff₃ (Del α e₁) (Upd α β e₂) (Cnf (DelUpd α β) e₃)
  UpdDelC : ∀ {as bs a xs ys zs e₃} {e₁ : ES (as ++ xs) (bs ++ ys)} {e₂ : ES (as ++ xs) zs} (α : View as a) (β : View bs a) ->
              RawDiff₃ e₁ e₂ e₃ -> RawDiff₃ (Upd α β e₁) (Del α e₂) (Cnf (UpdDel α β) e₃)
  InsInsC : ∀ {as bs a b xs ys zs e₃} {e₁ : ES xs (as ++ ys)} {e₂ : ES xs (bs ++ zs)} (α : View as a) (β : View bs b) ->
              {¬eq : ¬ (α ⋍ β)} -> RawDiff₃ e₁ e₂ e₃ -> RawDiff₃ (Ins α e₁) (Ins β e₂) (Cnf (InsIns α β) e₃)
  UpdUpdC : ∀ {as bs cs a xs ys zs e₃} {e₁ : ES (as ++ xs) (bs ++ ys)} {e₂ : ES (as ++ xs) (cs ++ zs)} 
              (α : View as a) (β : View bs a) (γ : View cs a) -> {¬eq : ¬ (β ⋍ γ)} -> RawDiff₃ e₁ e₂ e₃ 
              -> RawDiff₃ (Upd α β e₁) (Upd α γ e₂) (Cnf (UpdUpd β γ) e₃)

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

--------------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality

Diff₃⟪_⟫ : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} ->
            Diff₃ e₁ e₂ e₃ -> ⟪ e₃ ⟫ ≡ ⟪ e₁ ⟫
Diff₃⟪ End ⟫ = refl
Diff₃⟪ InsIns x d ⟫ = Diff₃⟪ d ⟫
Diff₃⟪ Ins₁ x d ⟫ = Diff₃⟪ d ⟫
Diff₃⟪ Ins₂ x d ⟫ = Diff₃⟪ d ⟫
Diff₃⟪ DelDel x d ⟫ rewrite Diff₃⟪ d ⟫ = refl
Diff₃⟪ DelCpy x d ⟫ rewrite Diff₃⟪ d ⟫ = refl
Diff₃⟪ CpyDel x d ⟫ rewrite Diff₃⟪ d ⟫ = refl
Diff₃⟪ CpyCpy x d ⟫ rewrite Diff₃⟪ d ⟫ = refl
Diff₃⟪ CpyUpd x y d ⟫ rewrite Diff₃⟪ d ⟫ = refl
Diff₃⟪ UpdCpy x y d ⟫ rewrite Diff₃⟪ d ⟫ = refl
Diff₃⟪ UpdUpd x y d ⟫ rewrite Diff₃⟪ d ⟫ = refl 

Diff₃~ : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} 
           -> Diff₃ e₁ e₂ e₃ -> e₁ ~ e₂
Diff₃~ End = End
Diff₃~ (InsIns x d) = InsIns x x (Diff₃~ d)
Diff₃~ (Ins₁ x d) = Ins₁ x (Diff₃~ d)
Diff₃~ (Ins₂ x d) = Ins₂ x (Diff₃~ d)
Diff₃~ (DelDel x d) = DelDel x (Diff₃~ d)
Diff₃~ (DelCpy x d) = DelCpy x (Diff₃~ d)
Diff₃~ (CpyDel x d) = CpyDel x (Diff₃~ d)
Diff₃~ (CpyCpy x d) = CpyCpy x (Diff₃~ d)
Diff₃~ (CpyUpd x y d) = CpyUpd x y (Diff₃~ d)
Diff₃~ (UpdCpy x y d) = UpdCpy x y (Diff₃~ d)
Diff₃~ (UpdUpd x y d) = UpdUpd x y y (Diff₃~ d)

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

--------------------------------------------------------------------------------

-- Relation between Diff and Diff₃
-- Note that implicitly says that the edit scripts all originated from the 
-- same source object
getDiff : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} ->
            Diff₃ e₁ e₂ e₃ -> Diff ⟪ e₃ ⟫ ⟦ e₁ ⟧ e₁ × Diff ⟪ e₃ ⟫ ⟦ e₂ ⟧ e₂
getDiff {e₁ = e₁} {e₂ = e₂} {e₃ = e₃} d₃
  rewrite Diff₃⟪ d₃ ⟫ with mkDiff e₁ | mkDiff e₂ | (Diff₃~ d₃)
... | d₁ | d₂ | p = d₁ , aux d₂ (Diff~nec d₁ d₂ p)
  where aux : Diff ⟪ e₂ ⟫ ⟦ e₂ ⟧ e₂ -> ⟪ e₁ ⟫ ≡ ⟪ e₂ ⟫ -> Diff ⟪ e₁ ⟫ ⟦ e₂ ⟧ e₂
        aux d p rewrite p = d

--------------------------------------------------------------------------------

-- Represents how changes can be merged
data _≔_⊔_ : ∀ {a b c d e f} -> a ~> b -> c ~> d -> e ~> f -> Set where
  Same : ∀ {v w} -> (g : v ~> w) -> g ≔ g ⊔ g
  Change₁ : ∀ {v w} -> (f : v ~> w) (g : v ~> v) -> f ≔ f ⊔ g
  Change₂ : ∀ {v w} -> (f : v ~> v) (g : v ~> w) -> g ≔ f ⊔ g
