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
data _≔_⊔_ {v : Val} : ∀ {a b c} -> v ~> a -> v ~> b -> v ~> c -> Set₁ where
  Id₁ : ∀ {w} -> (f : v ~> v) (g : v ~> w) -> g ≔ f ⊔ g
  Id₂ : ∀ {w} -> (f : v ~> w) (g : v ~> v) -> f ≔ f ⊔ g
  Idem : ∀ {w} -> (f : v ~> w) -> f ≔ f ⊔ f

--------------------------------------------------------------------------------

data RawMapping : Set₁ where
  [] : RawMapping
  _∷_ : ∀ {a b} -> a ~> b -> RawMapping -> RawMapping
  _∷ᶜ_ : Conflict -> RawMapping -> RawMapping

data _,_↥_ : ∀ {v w z} -> (v ~> w) -> (v ~> z) -> Conflict -> Set where
  InsIns : ∀ {as a bs b} {α : View as a} {β : View bs b} 
             (f : ⊥ ~> ⟨ α ⟩) (g : ⊥ ~> ⟨ β ⟩) (α≠β : ¬ (α ⋍ β)) -> f , g ↥ InsIns α β
  UpdUpd : ∀ {as bs cs a} {α : View as a} {β : View bs a} {γ : View cs a}
             (f : ⟨ α ⟩ ~> ⟨ β ⟩) (g : ⟨ α ⟩ ~> ⟨ γ ⟩)
             (α≠β : ¬ (α ⋍ β)) (α≠γ : ¬ (α ⋍ γ)) (β≠γ : ¬ (β ⋍ γ))
             -> f , g ↥ UpdUpd β γ
  UpdDel : ∀ {as bs a} {α : View as a} {β : View bs a} 
             (f : ⟨ α ⟩ ~> ⟨ β ⟩) (g : ⟨ α ⟩ ~> ⊥) (α≠β : ¬ (α ⋍ β)) -> f , g ↥ UpdDel α β
  DelUpd : ∀ {as bs a} {α : View as a} {β : View bs a} 
             (f : ⟨ α ⟩ ~> ⊥) (g : ⟨ α ⟩ ~> ⟨ β ⟩) (α≠β : ¬ (α ⋍ β)) -> f , g ↥ DelUpd α β

infixl 2 _,_↥_

-- data Merge : Mapping -> Mapping -> RawMapping -> Set₁ where
--   [] : Merge [] [] []
--   merge : ∀ {xs ys zs a b c d} {x : a ~> b} {y : a ~> c} {z : a ~> d} -> 
--           z ≔ x ⊔ y -> Merge xs ys zs -> Merge (x ∷ xs) (y ∷ ys) (z ∷ zs)
--   conflict : ∀ {xs ys zs v w z c} {x : v ~> w} {y : v ~> z} -> 
--                x , y ↥ c -> Merge xs ys zs -> Merge (x ∷ xs) (y ∷ ys) (c ∷ᶜ zs)
--   ins₁ : ∀ {xs ys zs as a} {α : View as a} {{i : ¬Insᵐ ys}} (x : ⊥ ~> ⟨ α ⟩) -> Merge xs ys zs -> Merge (x ∷ xs) ys (x ∷ zs)
--   ins₂ : ∀ {xs ys zs as a} {α : View as a} {{i : ¬Insᵐ xs}} (y : ⊥ ~> ⟨ α ⟩) -> Merge xs ys zs -> Merge xs (y ∷ ys) (y ∷ zs)       

-- Reifies the outcome of diff₃
-- Merges two mapping producing
-- data Merge : Mapping -> Mapping -> Mapping -> Set₁ where
--   [] : Merge [] [] []
--   cons : ∀ {xs ys zs a b c d} {x : a ~> b} {y : a ~> c} {z : a ~> d} -> 
--               z ≔ x ⊔ y -> Merge xs ys zs -> Merge (x ∷ xs) (y ∷ ys) (z ∷ zs)
--   ins₁ : ∀ {xs ys zs as a} {α : View as a} (x : ⊥ ~> ⟨ α ⟩) -> Merge xs ys zs -> Merge (x ∷ xs) ys (x ∷ zs)
--   ins₂ : ∀ {xs ys zs as a} {α : View as a} (y : ⊥ ~> ⟨ α ⟩) -> Merge xs ys zs -> Merge xs (y ∷ ys) (y ∷ zs)       

-- Alternative definition with ~ᵐ
-- data Merge : {xs : Mapping} {ys : Mapping} -> xs ~ᵐ ys -> Mapping -> Set₁ where
--   [] : Merge nil []
--   cons : ∀ {xs ys zs a b c d} {p : xs ~ᵐ ys} {x : a ~> b} {y : a ~> c} {z : a ~> d} -> 
--               z ≔ x ⊔ y -> Merge p zs -> Merge (cons x y p) (z ∷ zs)
--   ins₁ : ∀ {xs ys zs as a} {p : xs ~ᵐ ys} {α : View as a} {{i : ¬Insᵐ ys}} 
--            (x : ⊥ ~> ⟨ α ⟩) -> Merge p zs -> Merge (ins₁ x p) (x ∷ zs)
--   ins₂ : ∀ {xs ys zs as a} {p : xs ~ᵐ ys} {α : View as a}  {{i : ¬Insᵐ xs}}
--            (y : ⊥ ~> ⟨ α ⟩) -> Merge p zs -> Merge (ins₂ y p) (y ∷ zs)

-- data MVal : Set₁ where
--   V : ∀ (v : Val) -> MVal
--   [_,_∥_] : ∀ (v w : Val) -> (v≠w : ¬ (v ≡ w)) -> MVal

-- data _=>_ (a : Val) : MVal -> Set₁ where
--   S : ∀ {b : Val} -> a ~> b -> a => V b 
--   F : ∀ (b c : Val) -> (b≠c : ¬ (b ≡ c)) -> a => [ b , c ∥ b≠c ]

-- -- Merge two mapping a ~> b, a ~> c
-- data MergeMap (a : Val) : Val -> Val -> MVal -> Set₁ where
--   Eq₁ : ∀ b -> MergeMap a a b (V b)
--   Eq₂ : ∀ b -> MergeMap a b a (V b)
--   Eq₃ : ∀ b -> MergeMap a b b (V b)
--   Cnf : ∀ {b c} -> (a≠b : ¬ (a ≡ b)) (a≠c : ¬ (a ≡ c)) (b≠c : ¬ (b ≡ c)) -> MergeMap a b c [ b , c ∥ b≠c ]
  
-- import Level as L

-- data Mapping' {l} (a : Set₁) (b : Set₁) (_:~>:_ : a -> b -> Set l) : Set (L.suc l) where
--   [] : Mapping' a b _:~>:_
--   _∷_ : ∀ {v : a} {w : b} -> v :~>: w -> Mapping' a b _:~>:_ -> Mapping' a b _:~>:_
 

-- Map~> : Set₁
-- Map~> = Mapping' Val Val _~>_

-- Map=> : Set₂ 
-- Map=> = Mapping' Val MVal _=>_

-- data Merge : Map~> -> Map~> -> Map=> -> Set₁ where
--   [] : Merge [] [] []
--   cons : ∀ {xs ys zs a b c d} {x : a ~> b} {y : a ~> c} {z : a => d} -> 
--               MergeMap a b c d -> Merge xs ys zs -> Merge (x ∷ xs) (y ∷ ys) (z ∷ zs)
--   ins₁ : ∀ {xs ys zs as a} {α : View as a} (x : ⊥ ~> ⟨ α ⟩) -> Merge xs ys zs -> Merge (x ∷ xs) ys (S x ∷ zs)
--   ins₂ : ∀ {xs ys zs as a} {α : View as a} (y : ⊥ ~> ⟨ α ⟩) -> Merge xs ys zs -> Merge xs (y ∷ ys) (S y ∷ zs)       

-- TODO point out in thesis that we need to use ~ᵐ to keep things aligned in the proofs.
data _⇓_ : ∀ {xs ys} -> xs ~ᵐ ys -> RawMapping -> Set₁ where
  nil : nil ⇓ []
  merge : ∀ {xs ys zs a b c d} {p : xs ~ᵐ ys} {x : a ~> b} {y : a ~> c} {z : a ~> d} -> 
          (m : z ≔ x ⊔ y) -> p ⇓ zs -> cons x y p ⇓ (z ∷ zs)
  conflict : ∀ {xs ys zs v w z c} {x : v ~> w} {y : v ~> z} {p : xs ~ᵐ ys}  -> 
               (u : x , y ↥ c) -> p ⇓ zs -> cons x y p ⇓ (c ∷ᶜ zs)
  ins₁ : ∀ {xs ys zs as a} {p : xs ~ᵐ ys} {α : View as a} {{i : ¬Insᵐ ys}} (x : ⊥ ~> ⟨ α ⟩) -> p ⇓ zs -> ins₁ x p ⇓ (x ∷ zs)
  ins₂ : ∀ {xs ys zs as a} {p : xs ~ᵐ ys} {α : View as a} {{i : ¬Insᵐ xs}} (y : ⊥ ~> ⟨ α ⟩) -> p ⇓ zs -> ins₂ y p ⇓ (y ∷ zs)   
