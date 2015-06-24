module Diff3.Safety where

open import Diff3.Core public
open import Data.DTree
open import Lemmas

open import Function
open import Data.Product
open import Data.List
open import Relation.Binary
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Data.Sum as S
open import Data.Empty 

-- Two aligned functions are present in e₁ and e₂
-- Better name? 
-- Should I keep the functions as index or make them parameter?
-- data Map⋎₂ {as bs cs ds es fs} {u : Val as bs} {v : Val cs ds} {w : Val es fs} 
--             : ∀ {xs ys zs} {e₁ : ES xs ys} {e₂ : ES xs zs} (p : e₁ ⋎ e₂) (f : u ~> v) (g : u ~> w) -> Set₁ where
--      here : ∀ {xs ys zs} {e₁ : ES (as ++ xs) (cs ++ ys)} {e₂ : ES (as ++ xs) (es ++ zs)} {p : e₁ ⋎ e₂} 
--               (f : u ~> v) (g : u ~> w) -> Map⋎₂ (cons f g p) f g
--      there : ∀ {xs ys zs as' bs' cs' ds' es' fs'} {u' : Val as' bs'} {v' : Val cs' ds'} {w' : Val es' fs'}
--                {e₁ : ES (as' ++ xs) (cs' ++ ys)} {e₂ : ES (as' ++ xs) (es' ++ zs)} {p : e₁ ⋎ e₂}
--                {f : u ~> v} {g : u ~> w} {x : u' ~> v'} {y : u' ~> w'} -> Map⋎₂ p f g -> Map⋎₂ (cons x y p) f g
 
-- _,_∈₂_,_ : ∀ {as bs cs ds es fs xs ys zs} {u : Val as bs} {v : Val cs ds} {w : Val es fs} 
--              (f : u ~> v) (g : u ~> w)  (e₁ : ES xs ys) (e₂ : ES xs zs) {{p : e₁ ⋎ e₂}} -> Set₁
-- _,_∈₂_,_ f g e₁ e₂ {{p}} = Map⋎₂ p f g

--------------------------------------------------------------------------------

data Persistent {as bs cs ds xs ys zs} {u : Val as bs} {v : Val cs ds}
                (e₁ : ES xs ys) (e₂ : ES xs zs) (e₃ : ES₃ xs) (f : u ~> v) : Set₁ where
         
     -- Least specific
     -- 1) Here we do not require ⋎, but only that f and g are present in e₁ and e₂
     -- and the corresponding result in e₃

     conflict : ∀ {es fs} {w : Val es fs} {c : Conflict u v w} {g : u ~> w} -> 
                   (f∈₁ : f ∈ₑ e₁) (g∈₂ : g ∈ₑ e₂) (u : f ⊔ g ↥ c) (c∈₃ : c ∈ᶜ e₃) -> Persistent e₁ e₂ e₃ f 
     propagate : ∀ {es fs} {w : Val es fs} {g : u ~> w} -> 
                   (f∈₁ : f ∈ₑ e₁) (g∈₂ : g ∈ₑ e₂) (m : f ⊔ g ↧ f) (f∈₃ : f ∈₃ e₃) -> Persistent e₁ e₂ e₃ f

      -- 2) Here we require that e₁ ⋎ e₂ and thus that the two functions are aligned
      -- Still c need only to be present in e₃
     -- conflict : ∀ {es fs} {w : Val es fs} {c : Conflict u v w} {g : u ~> w} {p : e₁ ⋎ e₂} -> 
     --              f , g ∈₂ e₁ , e₂ -> f ⊔ g ↥ c -> c ∈ᶜ e₃ -> Persistent e₁ e₂ e₃ f 
     -- propagate : ∀ {es fs} {w : Val es fs} {g : u ~> w} {p : e₁ ⋎ e₂} -> 
     --               f , g ∈₂ e₁ , e₂ -> f ⊔ g ↧ f -> f ∈₃ e₃ -> Persistent e₁ e₂ e₃ f 

     -- Most specific
     -- 3) An additional data-type that mimics ⇓ specialized for conflict and functions is used

-- TODO reformulate this as persistance (either is preserved or there is a conflict that involves it)
-- Then we can easily state noBackOutChanges for conflictless ES₃

mapP : ∀ {xs xs' ys ys' zs zs' as bs cs ds} {v : Val as bs} {w : Val cs ds} {f : v ~> w}
         -> {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES₃ xs} {e₁' : ES xs' ys'} {e₂' : ES xs' zs'} {e₃' : ES₃ xs'}
         -> (f ∈ₑ e₁ → f ∈ₑ e₁') -> (∀ {es fs} {u : Val es fs} {g : v ~> u} -> g ∈ₑ e₂ → g ∈ₑ e₂') 
         -> (∀ {as bs cs ds es fs} {u : Val as bs} {v : Val cs ds} {w : Val es fs} {c : Conflict u v w} -> c ∈ᶜ e₃ -> c ∈ᶜ e₃') 
         -> (f ∈₃ e₃ -> f ∈₃ e₃') -> Persistent e₁ e₂ e₃ f -> Persistent e₁' e₂' e₃' f
mapP f g h₁ h₂ (conflict f∈₁ g∈₂ u c∈₃) = conflict (f f∈₁) (g g∈₂) u (h₁ c∈₃)
mapP f g h₁ h₂ (propagate f∈₁ g∈₂ m f∈₃) = propagate (f f∈₁) (g g∈₂) m (h₂ f∈₃)

persistent : ∀ {xs ys zs as bs cs ds} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES₃ xs} {p : e₁ ⋎ e₂}
               {u : Val as bs} {v : Val cs ds} {f : u ~> v} -> 
               Change f -> (d : Diff₃ e₁ e₂ e₃) -> f ∈ₑ e₁ -> Persistent e₁ e₂ e₃ f 
persistent (IsChange v≠w) (merge (Id₁ f g v≠w₁) d) (here .f) = ⊥-elim (v≠w refl)
persistent c (merge (Id₂ h g v≠w) d) (here .h) = propagate (here h) (here g) (Id₂ h g v≠w) (here h)
persistent c (merge (Idem g) d) (here .g) = propagate (here g) (here g) (Idem g) (here g)
persistent _ (conflict {c = c} {g = g} u d) (here f) = conflict (here f) (here g) u (here c)
persistent c (merge m d) (there g p) = mapP (there g) (there _) (there _) (there _) (persistent c d p)
persistent c (conflict u d) (there g p) = mapP (there g) (there _) (thereᶜ _) (thereᶜ _) (persistent c d p)

noBackOutChanges₁ : ∀ {xs ys zs as bs cs ds} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES₃ xs} {p : e₁ ⋎ e₂}
                      {u : Val as bs} {v : Val cs ds} {f : u ~> v} -> 
                      Change f -> Diff₃ e₁ e₂ e₃ -> f ∈ₑ e₁ -> NoCnf e₃ -> f ∈₃ e₃
noBackOutChanges₁ c d p q with persistent c d p
noBackOutChanges₁ c d p q | conflict f∈₁ g∈₂ u₁ c∈₃ = ⊥-elim (⊥-NoCnf q c∈₃)
noBackOutChanges₁ c d p q | propagate f∈₁ g∈₂ m f∈₃ = f∈₃

noBackOutChanges₂ : ∀ {xs ys zs as bs cs ds} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES₃ xs} {p : e₁ ⋎ e₂}
                      {u : Val as bs} {v : Val cs ds} {f : u ~> v} -> 
                      Change f -> Diff₃ e₁ e₂ e₃ -> f ∈ₑ e₂ -> NoCnf e₃ -> f ∈₃ e₃
noBackOutChanges₂ c d p q with persistent c (⇓-sym d) p
noBackOutChanges₂ c d p q | conflict f∈₁ g∈₂ u c∈₃ = ⊥-elim (⊥-NoCnf (NoCnf-sym q) c∈₃)
noBackOutChanges₂ {e₃ = e₃} c d p q | propagate f∈₁ g∈₂ m f∈₃ with sym₃ e₃ | NoCnf-≡ q
noBackOutChanges₂ c d p₁ q | propagate f∈₁ g∈₂ m f∈₃ | e₃ | refl = f∈₃

open import Data.Sum
import Data.Sum as S

-- The sum type ⊎ corresponds to disjunction in logic (∨).
-- An edit can belong to both the script and in those cases I default to inj₁.
-- Note that this does not affect the generality of the theorem. 
-- TODO better name?
noEditMadeUp : ∀ {xs ys zs as bs cs ds} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES₃ xs} {p : e₁ ⋎ e₂}
                 {u : Val as bs} {v : Val cs ds} {f : u ~> v} -> 
                 f ∈₃ e₃ -> Diff₃ e₁ e₂ e₃ -> f ∈ₑ e₁ ⊎ f ∈ₑ e₂
noEditMadeUp (here f) (merge (Id₁ g .f v≠w) d) = inj₂ (here f)
noEditMadeUp (here f) (merge (Id₂ .f g v≠w) d) = inj₁ (here f)
noEditMadeUp (here f) (merge (Idem .f) d) = inj₁ (here f)
noEditMadeUp (there g p) (merge m d) = S.map (there _) (there _) (noEditMadeUp p d)
noEditMadeUp (thereᶜ c p) (conflict u d) = S.map (there _) (there _) (noEditMadeUp p d)

--------------------------------------------------------------------------------

-- xs ⊆ ys , zs is the proof that xs is a list composed from elements of ys and zs
-- data _⊆_,_ : List Set -> List Set -> List Set -> Set where
--   stop : [] ⊆ [] , []
--   cons₁ : ∀ {y xs ys zs} -> xs ⊆ ys , zs -> y ∷ xs ⊆ y ∷ ys , zs
--   cons₂ : ∀ {z xs ys zs} -> xs ⊆ ys , zs -> z ∷ xs ⊆ ys , z ∷ zs
--   cons₁₂ : ∀ {x xs ys zs} -> xs ⊆ ys , zs -> x ∷ xs ⊆ x ∷ ys , x ∷ zs
--   drop₁ : ∀ {y xs ys zs} -> xs ⊆ ys , zs -> xs ⊆ y ∷ ys , zs
--   drop₂ : ∀ {z xs ys zs} -> xs ⊆ ys , zs -> xs ⊆ ys , z ∷ zs

-- infixr 2 _⊆_,_ 

-- typesOf : ∀ {xs} -> DList xs -> List Set
-- typesOf [] = []
-- typesOf (Node {a = a} x xs ∷ d) = a ∷ typesOf xs ++ typesOf d

-- typesOf++ : ∀ {as bs} (a : DList as) (b : DList bs) -> typesOf a ++ typesOf b ≡ typesOf (a +++ b)
-- typesOf++ [] b = refl
-- typesOf++ (Node {a = ty} x xs ∷ a) b rewrite 
--    sym (typesOf++ a b)  
--   | ++-assoc (typesOf xs) (typesOf a) (typesOf b) = cong (_∷_ ty) refl

-- typesOf⟦_⟧ : ∀ {{ys zs}} {xs} (e : ES xs (ys ++ zs)) ->
--               let ds₁ , ds₂ = dsplit ⟦ e ⟧ in typesOf ds₁ ++ typesOf ds₂ ≡ typesOf ⟦ e ⟧
-- typesOf⟦ e ⟧ rewrite
--   typesOf++ (proj₁ (dsplit ⟦ e ⟧)) (proj₂ (dsplit ⟦ e ⟧)) 
--   | dsplit-lemma ⟦ e ⟧ = refl


-- -- TODO this holds only for well-typed Diff₃

-- -- mixOf : ∀ {xs ys zs ws} {e₀₁ : ES xs ys} {e₀₂ : ES xs zs} {e₀₁₂ : ES xs ws}
-- --            -> Diff₃ e₀₁ e₀₂ e₀₁₂ -> typesOf ⟦ e₀₁₂ ⟧ ⊆ typesOf ⟦ e₀₁ ⟧ , typesOf ⟦ e₀₂ ⟧
-- -- mixOf End = stop
-- -- mixOf (InsIns {e₁ = e₁} {e₂ = e₂} {e₃ = e₃} x d) rewrite
-- --   typesOf⟦ e₁ ⟧ | typesOf⟦ e₂ ⟧ | typesOf⟦ e₃ ⟧ = cons₁₂ (mixOf d)
-- -- mixOf (Ins₁ {e₁ = e₁} {e₃ = e₃} x d) rewrite
-- --   typesOf⟦ e₁ ⟧ | typesOf⟦ e₃ ⟧ = cons₁ (mixOf d)
-- -- mixOf (Ins₂ {e₂ = e₂} {e₃ = e₃} x d) rewrite
-- --   typesOf⟦ e₂ ⟧ | typesOf⟦ e₃ ⟧ = cons₂ (mixOf d)
-- -- mixOf (DelDel x d) = mixOf d
-- -- mixOf (DelCpy {e₂ = e₂} x d) rewrite
-- --   typesOf⟦ e₂ ⟧ = drop₂ (mixOf d)
-- -- mixOf (CpyDel {e₁ = e₁} x d) rewrite
-- --   typesOf⟦ e₁ ⟧ = drop₁ (mixOf d)
-- -- mixOf (UpdUpd {e₁ = e₁} {e₂ = e₂} {e₃ = e₃} x y d) rewrite
-- --   typesOf⟦ e₁ ⟧ | typesOf⟦ e₂ ⟧ | typesOf⟦ e₃ ⟧ = cons₁₂ (mixOf d)
