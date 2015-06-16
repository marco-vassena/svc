module Diff3.Maximal where

--------------------------------------------------------------------------------
-- It means that diff3 must propagate all the changes from e1 and e2

open import Diff3.Core
open import EditScript.Mapping

open import Data.List

-- Convenient way to deal with Edits
data _~>_ : Val -> Val -> Set where
  Ins : ∀ {as a} -> (α : View as a) -> ⊥ ~> ⟨ α ⟩
  Del : ∀ {as a} -> (α : View as a) -> ⟨ α ⟩ ~> ⊥
  Cpy : ∀ {as a} -> (α : View as a) -> ⟨ α ⟩ ~> ⟨ α ⟩
  Upd : ∀ {as a bs} -> (α : View as a) (β : View bs a) -> ⟨ α ⟩ ~> ⟨ β ⟩
  End : ⊥ ~> ⊥

source : ∀ {as bs cs ds} -> Edit as bs cs ds -> Val
source (Ins x) = ⊥
source (Del x) = ⟨ x ⟩
source (Cpy x) = ⟨ x ⟩
source (Upd x y) = ⟨ x ⟩
source End = ⊥

target : ∀ {as bs cs ds} -> Edit as bs cs ds -> Val
target (Ins x) = ⟨ x ⟩
target (Del x) = ⊥
target (Cpy x) = ⟨ x ⟩
target (Upd x y) = ⟨ y ⟩
target End = ⊥

toMap : ∀ {as bs cs ds} -> (c : Edit as bs cs ds) -> source c ~> target c
toMap (Ins x) = Ins x
toMap (Del x) = Del x
toMap (Cpy x) = Cpy x
toMap (Upd x y) = Upd x y
toMap End = End

sourceMap : (v : Val) -> List Set
sourceMap ⊥ = []
sourceMap (⟨_⟩ {as = as} x) = as

targetMap : (v : Val) -> List Set
targetMap ⊥ = []
targetMap (⟨_⟩ {a = a} x ) = a ∷ []

fromMap : ∀ {v w} -> v ~> w -> Edit (sourceMap v) (sourceMap w) (targetMap v) (targetMap w)
fromMap (Ins α) = Ins α
fromMap (Del α) = Del α
fromMap (Cpy α) = Cpy α
fromMap (Upd α β) = Upd α β
fromMap End = End

-- TODO Is it possible to make the merged mapping a parameter instead of an index? Is it better?
-- TODO use misfix operator e.g. _≔_⊔_ 
data Merge : ∀ {a b c d e f} -> a ~> b -> c ~> d -> e ~> f -> Set where
  Same : ∀ {v w} -> (g : v ~> w) -> Merge g g g
  Change₁ : ∀ {v w} -> (f : v ~> w) (g : v ~> v) -> Merge f g f
  Change₂ : ∀ {v w} -> (f : v ~> v) (g : v ~> w) -> Merge f g g

-- TODO maybe I should use a variant of ES to allow pattern matching on Maximal ...
-- at the moment I don't need it though.
-- Pattern match fails even using explicit equality proofs.
data Maximal : ∀ {xs₁ xs₂ xs₃ ys zs ws} (e₁ : ES xs₁ ys) (e₂ : ES xs₂ zs) (e₃ : ES xs₃ ws) -> Set₁ where
  inj₁ : ∀ {as bs cs ds xs₁ xs₂ xs₃ ys zs ws} {e₁ : ES (as ++ xs₁) (bs ++ ys)} {e₂ : ES xs₂ zs} {e₃ : ES (as ++ xs₃) (bs ++ ws)} ->
           (c : Edit as bs cs ds) -> Maximal e₁ e₂ e₃ -> Maximal (c ∻ e₁) e₂ (c ∻ e₃)
  inj₂ : ∀ {as bs cs ds xs₁ xs₂ xs₃ ys zs ws} {e₁ : ES xs₁ ys} {e₂ : ES (as ++ xs₂) (bs ++ zs)} {e₃ : ES (as ++ xs₃) (bs ++ ws)} ->
           (c : Edit as bs cs ds) -> Maximal e₁ e₂ e₃ -> Maximal e₁ (c ∻ e₂) (c ∻ e₃)
  inj₁₂ : ∀ {as₁ as₂ as₃ bs₁ bs₂ bs₃ cs₁ cs₂ cs₃ ds₁ ds₂ ds₃ xs₁ xs₂ xs₃ ys zs ws} 
            {e₁ : ES (as₁ ++ xs₁) (bs₁ ++ ys)} {e₂ : ES (as₂ ++ xs₂) (bs₂ ++ zs)} {e₃ : ES (as₃ ++ xs₃) (bs₃ ++ ws)} ->
            {a : Edit as₁ bs₁ cs₁ ds₁} {b : Edit as₂ bs₂ cs₂ ds₂} {c : Edit as₃ bs₃ cs₃ ds₃} 
            -> Merge (toMap a) (toMap b) (toMap c) -> Maximal e₁ e₂ e₃ -> Maximal (a ∻ e₁) (b ∻ e₂) (c ∻ e₃)
  End : Maximal End End End

maximal : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} -> 
            Diff₃ e₁ e₂ e₃ -> Maximal e₁ e₂ e₃
maximal End = End
maximal (InsIns x d) = inj₁₂ (Same (Ins x)) (maximal d)
maximal (Ins₁ x d) = inj₁ (Ins x) (maximal d)
maximal (Ins₂ x d) = inj₂ (Ins x) (maximal d)
maximal (DelDel x d) = inj₁₂ (Same (Del x)) (maximal d)
maximal (DelCpy x d) = inj₁₂ (Change₁ (Del x) (Cpy x)) (maximal d)
maximal (CpyDel x d) = inj₁₂ (Change₂ (Cpy x) (Del x)) (maximal d)
maximal (CpyCpy x d) = inj₁₂ (Same (Cpy x)) (maximal d)
maximal (CpyUpd x y d) = inj₁₂ (Change₂ (Cpy x) (Upd x y)) (maximal d)
maximal (UpdCpy x y d) = inj₁₂ (Change₁ (Upd x y) (Cpy x)) (maximal d)
maximal (UpdUpd x y d) = inj₁₂ (Same (Upd x y)) (maximal d)

data Edits : ∀ {xs ys} -> ES xs ys -> Set₁ where
  [] : Edits End
  _∷_ : ∀ {as bs cs ds xs ys} {e : ES (as ++ xs) (bs ++ ys)} (c : Edit as bs cs ds) -> Edits e -> Edits (c ∻ e)

edits : ∀ {xs ys} -> (e : ES xs ys) -> Edits e
edits (Ins x e) = Ins x ∷ edits e
edits (Del x e) = Del x ∷ edits e
edits (Cpy x e) = Cpy x ∷ edits e
edits (Upd x y e) = Upd x y ∷ edits e
edits End = []

data Maximal' : ∀ {xs₁ xs₂ xs₃ ys zs ws} {e₁ : ES xs₁ ys} {e₂ : ES xs₂ zs} {e₃ : ES xs₃ ws} 
                -> Edits e₁ -> Edits e₂ -> Edits e₃ -> Set₁ where
     [] : Maximal' [] [] []
     inj₁ : ∀ {as bs cs ds xs₁ xs₂ xs₃ ys zs ws} {e₁ : ES (as ++ xs₁) (bs ++ ys)} {e₂ : ES xs₂ zs} {e₃ : ES (as ++ xs₃) (bs ++ ws)} ->
              {x : Edits e₁} {y : Edits e₂} {z : Edits e₃}
              (c : Edit as bs cs ds) -> Maximal' x y z -> Maximal' (c ∷ x) y (c ∷ z)
     inj₂ : ∀ {as bs cs ds xs₁ xs₂ xs₃ ys zs ws} {e₁ : ES xs₁ ys} {e₂ : ES (as ++ xs₂) (bs ++ zs)} {e₃ : ES (as ++ xs₃) (bs ++ ws)} ->
              {x : Edits e₁} {y : Edits e₂} {z : Edits e₃}
              (c : Edit as bs cs ds) -> Maximal' x y z -> Maximal' x (c ∷ y) (c ∷ z)
     inj₁₂ : ∀ {as₁ as₂ as₃ bs₁ bs₂ bs₃ cs₁ cs₂ cs₃ ds₁ ds₂ ds₃ xs₁ xs₂ xs₃ ys zs ws} 
               {e₁ : ES (as₁ ++ xs₁) (bs₁ ++ ys)} {e₂ : ES (as₂ ++ xs₂) (bs₂ ++ zs)} {e₃ : ES (as₃ ++ xs₃) (bs₃ ++ ws)} ->
               {a : Edit as₁ bs₁ cs₁ ds₁} {b : Edit as₂ bs₂ cs₂ ds₂} {c : Edit as₃ bs₃ cs₃ ds₃} 
               {x : Edits e₁} {y : Edits e₂} {z : Edits e₃} ->
               Merge (toMap a) (toMap b) (toMap c) -> Maximal' x y z -> Maximal' (a ∷ x) (b ∷ y) (c ∷ z)
            
     -- inj₁ : ∀ {as bs cs ds xs₁ xs₂ xs₃ ys zs ws} {e₁ : ES (as ++ xs₁) (bs ++ ys)} {e₂ : ES xs₂ zs} {e₃ : ES (as ++ xs₃) (bs ++ ws)} ->
  --          (c : Edit as bs cs ds) -> Maximal e₁ e₂ e₃ -> Maximal (c ∻ e₁) e₂ (c ∻ e₃)
  -- End : Maximal End End End

foo : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} 
        {x : Edits e₁} {y : Edits e₂} {z : Edits e₃} -> Maximal' x y z -> {!!}
foo {e₁ = e₁}  {e₂ = e₂} m = {!!}

--------------------------------------------------------------------------------

data Mapping : Set₁ where
  [] : Mapping
  _∷_ : ∀ {v w} -> v ~> w -> Mapping -> Mapping

infixr 3 _∷_

-- It is possible to pattern match directly on this data type.
-- When edit script are involved, first patter match on the edit script (or some auxilairy datatype such as Diff₃)
-- and then on Maximal₃.
data Maximal₃ : Mapping -> Mapping -> Mapping -> Set where
  stop : Maximal₃ [] [] []
  inj₁ : ∀ {xs ys zs v w} -> (x : v ~> w) -> (p : Maximal₃ xs ys zs) -> Maximal₃ (x ∷ xs) ys (x ∷ zs)
  inj₂ : ∀ {xs ys zs v w} -> (y : v ~> w) (p : Maximal₃ xs ys zs) -> Maximal₃ xs (y ∷ ys) (y ∷ zs)
  inj₁₂ : ∀ {xs ys zs a b c d e f} {x : a ~> b} {y : c ~> d} {z : e ~> f} ->
            (m : Merge x y z) (p : Maximal₃ xs ys zs) -> Maximal₃ (x ∷ xs) (y ∷ ys) (z ∷ zs)
 
mapping : ∀ {xs ys} -> ES xs ys -> Mapping
mapping (Ins x e) = Ins x ∷ mapping e
mapping (Del x e) = Del x ∷ mapping e
mapping (Cpy x e) = Cpy x ∷ mapping e
mapping (Upd x y e) = Upd x y ∷ mapping e
mapping End = []

maximal₃ : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} -> 
           Diff₃ e₁ e₂ e₃ -> Maximal₃ (mapping e₁) (mapping e₂) (mapping e₃)
maximal₃ End = stop
maximal₃ (InsIns x d) = inj₁₂ (Same (Ins x)) (maximal₃ d)
maximal₃ (Ins₁ x d) = inj₁ (Ins x) (maximal₃ d)
maximal₃ (Ins₂ x d) = inj₂ (Ins x) (maximal₃ d)
maximal₃ (DelDel x d) = inj₁₂ (Same (Del x)) (maximal₃ d)
maximal₃ (DelCpy x d) = inj₁₂ (Change₁ (Del x) (Cpy x)) (maximal₃ d)
maximal₃ (CpyDel x d) = inj₁₂ (Change₂ (Cpy x) (Del x)) (maximal₃ d)
maximal₃ (CpyCpy x d) = inj₁₂ (Same (Cpy x)) (maximal₃ d)
maximal₃ (CpyUpd x y d) = inj₁₂ (Change₂ (Cpy x) (Upd x y)) (maximal₃ d)
maximal₃ (UpdCpy x y d) = inj₁₂ (Change₁ (Upd x y) (Cpy x)) (maximal₃ d)
maximal₃ (UpdUpd x y d) = inj₁₂ (Same (Upd x y)) (maximal₃ d)
