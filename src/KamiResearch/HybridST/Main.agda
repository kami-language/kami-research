
module KamiResearch.HybridST.Main where


open import Data.Product
open import Data.Sum
open import Data.List
open import KamiResearch.Common


-- ∑ λ (X : SSet A) -> isUnique X
-- variable
--   𝑖 𝑗 : Level

-- record Sum {I : Set} (F : I -> Set) : Set where
--   field fst : I
--   field snd : F fst
-- open import Agda.Builtin.Equality using (_≡_)


module _ (R : Set) (L : Set) where

  data Index : Set (lsuc lzero) where
    _,_ : 𝒫 R -> 𝒫 R -> Index

  _≤-Index_ : Index -> Index -> Set _
  _≤-Index_ (S₀ , I₀) (S₁ , I₁) = (S₀ ≤-𝒫 S₁) × (I₀ ≤-𝒫 I₁)


  _∩-Index_ : Index -> Index -> Index
  _∩-Index_ (S₀ , I₀) (S₁ , I₁) = (S₀ ∩-𝒫 S₁) , (I₀ ∩-𝒫 I₁)

  isValid : Index -> R × R -> Set
  isValid (S , I) (p , q) = (S p × S q) × (I p ⊎ I q)

  data HybridType (Ix : Index) : Set where
    end : HybridType Ix
    _⇒_[_]►_ : (p q : R) -> isValid Ix (p , q) -> List (L × HybridType Ix) -> HybridType Ix

  _⊔-HT_ : ∀{Ix} -> (t s : HybridType Ix) -> HybridType Ix
  _⊔-HT_ t s = {!!}

  restrict : {Ix Jx : Index} -> Ix ≤-Index Jx -> HybridType Jx -> HybridType Ix
  restrict {Ix} {Jx} Ix≤Jx end = end
  restrict {Ix} {Jx} Ix≤Jx (p ⇒ q [ x ]► ts) = {!!}




