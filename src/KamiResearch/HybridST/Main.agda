
module KamiResearch.HybridST.Main where

open import Agda.Primitive
open import Data.Product
open import Data.Sum
open import Data.List

variable
  𝑖 : Level

𝒫 : Set 𝑖 -> Set (lsuc 𝑖)
𝒫 X = X -> Set _

module _ (R : Set) (L : Set) where

  data Index : Set (lsuc lzero) where
    _,_ : 𝒫 R -> 𝒫 R -> Index

  isValid : Index -> R × R -> Set
  isValid (S , I) (p , q)= (S p × S q) × (I p ⊎ I q)

  data HybridType (Ix : Index) : Set where
    end : HybridType Ix
    _⇒_[_]►_ : (p q : R) -> isValid Ix (p , q) -> List (L × HybridType Ix) -> HybridType Ix



