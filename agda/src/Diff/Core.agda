module Diff.Core where

open import EditScript.Core
open import EditScript.Aligned
open import Lemmas 

open import Data.Unit hiding (_≤?_ ; _≤_)
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality

data Diff : ∀ {xs ys} ->  DList xs -> DList ys -> ES xs ys -> Set₁ where
  End : Diff [] [] End
  Del : ∀ {as a xs ys} {e : ES (as ++ xs) ys} {ts₁ : DList as} {ts₂ : DList xs} {ts : DList ys}
        ->  (x : View as a) -> Diff (ts₁ +++ ts₂) ts e -> Diff (Node x ts₁ ∷ ts₂ ) ts (Del x e)
  Upd : ∀ {as bs a xs ys} {e : ES (as ++ xs) (bs ++ ys)} {ts₁ : DList as} {ts₂ : DList xs} {ts₃ : DList bs} {ts₄ : DList ys}
      -> (x : View as a) (y : View bs a) -> Diff (ts₁ +++ ts₂) (ts₃ +++ ts₄) e 
      -> Diff (Node x ts₁ ∷ ts₂) (Node y ts₃ ∷ ts₄) (Upd x y e)
  Cpy : ∀ {as a xs ys} {e : ES (as ++ xs) (as ++ ys)} {ts₁ : DList as} {ts₂ : DList xs} {ts₃ : DList as} {ts₄ : DList ys}
        -> (x : View as a) -> Diff (ts₁ +++ ts₂) (ts₃ +++ ts₄) e -> Diff (Node x ts₁ ∷ ts₂) (Node x ts₃ ∷ ts₄) (Cpy x e)
  Ins : ∀ {bs b xs ys} {e : ES xs (bs ++ ys)} {ts₁ : DList xs} {ts₂ : DList bs} {ts₃ : DList ys}   
        -> (y : View bs b) -> Diff ts₁ (ts₂ +++ ts₃) e -> Diff ts₁ (Node y ts₂ ∷ ts₃) (Ins y e)

-- Once more we need to have an explicit mapping with dsplit.
-- Simple rewriting fails because (probably), the underlying with clause becomes ill-typed.
Diff-⟦⟧ : ∀ {xs} {{ys zs}} {t₀ : DList xs} (e : ES xs (ys ++ zs)) ->
              let ds₁ , ds₂ = dsplit ⟦ e ⟧ in Diff t₀ ⟦ e ⟧ e -> Diff t₀ (ds₁ +++ ds₂) e
Diff-⟦⟧ e d 
  rewrite dsplit-lemma ⟦ e ⟧ = d

Diff-⟪⟫ : ∀ {{xs ys}} {zs} {t₁ : DList zs} (e : ES (xs ++ ys) zs) ->
              let ds₁ , ds₂ = dsplit ⟪ e ⟫ in Diff ⟪ e ⟫ t₁ e -> Diff (ds₁ +++ ds₂) t₁ e
Diff-⟪⟫ e d 
  rewrite dsplit-lemma ⟪ e ⟫ = d

-- Relation between Diff, ⟦_⟧ and ⟪_⟫
mkDiff : ∀ {xs ys} (e : ES xs ys) -> Diff ⟪ e ⟫ ⟦ e ⟧ e
mkDiff (Ins x e) = Ins x (Diff-⟦⟧ e (mkDiff e))
mkDiff (Del x e) = Del x (Diff-⟪⟫ e (mkDiff e))
mkDiff (Cpy x e) = Cpy x (Diff-⟦⟧ e (Diff-⟪⟫ e (mkDiff e)))
mkDiff (Upd x y e) = Upd x y (Diff-⟦⟧ e (Diff-⟪⟫ e (mkDiff e)))
mkDiff End = End



open import Function

≡-split : ∀ {xs ys} (a : DList xs) (b : DList ys) (c : DList (xs ++ ys)) -> (a +++ b) ≡ c ->
        let ds₁ , ds₂ = dsplit c in a ≡ ds₁ × b ≡ ds₂
≡-split [] b .b refl = refl , refl
≡-split (t ∷ a) b (.t ∷ .(a +++ b)) refl with proj₁ (dsplit (a +++ b)) | proj₂ (dsplit (a +++ b)) | ≡-split a b (a +++ b) refl
≡-split (t ∷ a) b (.t ∷ .(a +++ b)) refl | .a | .b | refl , refl = refl , refl
 
-- Necessary condition of mkDiff for ⟪_⟫
mkDiff⟪_⟫ : ∀ {xs ys} {t₀ : DList xs} {t₁ : DList ys} {e : ES xs ys} -> Diff t₀ t₁ e -> t₀ ≡ ⟪ e ⟫
mkDiff⟪ End ⟫ = refl
mkDiff⟪ Del {e = e} {ts₁ = ts₁} {ts₂ = ts₂} x d ⟫ with ≡-split ts₁ ts₂ ⟪ e ⟫ mkDiff⟪ d ⟫
mkDiff⟪ Del x d ⟫ | refl , refl = refl
mkDiff⟪ Upd {e = e} {ts₁ = ts₁} {ts₂ = ts₂} x y d ⟫ with ≡-split ts₁ ts₂ ⟪ e ⟫ mkDiff⟪ d ⟫
mkDiff⟪ Upd x y d ⟫ | refl , refl = refl
mkDiff⟪ Cpy {e = e} {ts₁ = ts₁} {ts₂ = ts₂} x d ⟫ with ≡-split ts₁ ts₂ ⟪ e ⟫ mkDiff⟪ d ⟫
mkDiff⟪ Cpy x d ⟫ | refl , refl = refl
mkDiff⟪ Ins y d ⟫ = mkDiff⟪ d ⟫

-- Necessary condition of mkDiff for ⟦_⟧
mkDiff⟦_⟧ : ∀ {xs ys} {t₀ : DList xs} {t₁ : DList ys} {e : ES xs ys} -> Diff t₀ t₁ e -> t₁ ≡ ⟦ e ⟧
mkDiff⟦ End ⟧ = refl
mkDiff⟦ Del x d ⟧ = mkDiff⟦ d ⟧
mkDiff⟦ Upd {e = e} {ts₃ = ts₃} {ts₄ = ts₄} x y d ⟧ with ≡-split ts₃ ts₄ ⟦ e ⟧ mkDiff⟦ d ⟧
mkDiff⟦ Upd x y d ⟧ | refl , refl = refl
mkDiff⟦ Cpy {e = e} {ts₃ = ts₃} {ts₄ = ts₄} x d ⟧ with ≡-split ts₃ ts₄ ⟦ e ⟧ mkDiff⟦ d ⟧
mkDiff⟦ Cpy x d ⟧ | refl , refl = refl
mkDiff⟦ Ins {e = e} {ts₂ = ts₂} {ts₃ = ts₃} y d ⟧ with ≡-split ts₂ ts₃ ⟦ e ⟧ mkDiff⟦ d ⟧
mkDiff⟦ Ins x d ⟧ | refl , refl = refl

-- Now that we have Diff-suf we can use Diff x y e as an approximation of diff x y 

Diff~ : ∀ {xs ys zs} {x : DList xs} {y : DList ys} {z : DList zs} {e₁ : ES xs ys} {e₂ : ES xs zs} 
        -> Diff x y e₁ -> Diff x z e₂ -> e₁ ~ e₂
Diff~ End End = End
Diff~ End (Ins y q) = Ins₂ {{i = tt}} y (Diff~ End q)
Diff~ (Del x p) (Del .x q) = DelDel x (Diff~ p q)
Diff~ (Del x p) (Upd .x y q) = DelUpd x y (Diff~ p q)
Diff~ (Del x p) (Cpy .x q) = DelCpy x (Diff~ p q)
Diff~ (Del x p) (Ins y q) = Ins₂ {{i = tt}} y (Diff~ (Del x p) q)
Diff~ (Upd x y p) (Del .x q) = UpdDel x y (Diff~ p q)
Diff~ (Upd x y p) (Upd .x z q) = UpdUpd x y z (Diff~ p q)
Diff~ (Upd x y p) (Cpy .x q) = UpdCpy x y (Diff~ p q)
Diff~ (Upd {ts₃ = ts₃} {ts₄ = ts₄} x y p) (Ins z q) = Ins₂ {{i = tt}} z (Diff~ (Upd {ts₃ = ts₃} {ts₄ = ts₄} x y p) q)
Diff~ (Cpy x p) (Del .x q) = CpyDel x (Diff~ p q)
Diff~ (Cpy x p) (Upd .x y q) = CpyUpd x y (Diff~ p q)
Diff~ (Cpy x p) (Cpy .x q) = CpyCpy x (Diff~ p q)
Diff~ (Cpy {ts₃ = ts₃} {ts₄ = ts₄} x p) (Ins y q) = Ins₂ {{i = tt}} y (Diff~ (Cpy {ts₃ = ts₃} {ts₄ = ts₄} x p) q)
Diff~ (Ins y p) End = Ins₁ {{i = tt}} y (Diff~ p End)
Diff~ (Ins y p) (Del x q) = Ins₁ {{i = tt}} y (Diff~ p (Del x q))
Diff~ (Ins y p) (Upd {ts₃ = ts₃} {ts₄ = ts₄} x z q) = Ins₁ {{i = tt}} y (Diff~ p (Upd {ts₃ = ts₃} {ts₄ = ts₄} x z q))
Diff~ (Ins y p) (Cpy {ts₃ = ts₃} {ts₄ = ts₄} x q) = Ins₁ {{i = tt}} y (Diff~ p (Cpy {ts₃ = ts₃} {ts₄ = ts₄} x q))
Diff~ (Ins y p) (Ins z q) = InsIns y z (Diff~ p q)


Diff~nec : ∀ {xs ys zs} {x₁ x₂ : DList xs} {y : DList ys} {z : DList zs} {e₁ : ES xs ys} {e₂ : ES xs zs} 
        -> Diff x₁ y e₁ -> Diff x₂ z e₂ -> e₁ ~ e₂ -> x₁ ≡ x₂
Diff~nec d₁ d₂ p rewrite
  mkDiff⟪ d₁ ⟫ | mkDiff⟪ d₂ ⟫ = ~-⟪⟫ p
