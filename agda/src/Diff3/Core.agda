module Diff3.Core where

open import Diff
open import EditScript

open import Data.Product
open import Data.Sum
open import Data.List
open import Relation.Binary

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

--------------------------------------------------------------------------------

diff3~ : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} 
           -> Diff₃ e₁ e₂ e₃ -> e₁ ~ e₂
diff3~ End = End
diff3~ (InsIns x d) = InsIns x x (diff3~ d)
diff3~ (Ins₁ x d) = Ins₁ x (diff3~ d)
diff3~ (Ins₂ x d) = Ins₂ x (diff3~ d)
diff3~ (DelDel x d) = DelDel x (diff3~ d)
diff3~ (DelCpy x d) = DelCpy x (diff3~ d)
diff3~ (CpyDel x d) = CpyDel x (diff3~ d)
diff3~ (CpyCpy x d) = CpyCpy x (diff3~ d)
diff3~ (CpyUpd x y d) = CpyUpd x y (diff3~ d)
diff3~ (UpdCpy x y d) = UpdCpy x y (diff3~ d)
diff3~ (UpdUpd x y d) = UpdUpd x y y (diff3~ d)

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
