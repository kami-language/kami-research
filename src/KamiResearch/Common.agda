
module KamiResearch.Common where

open import Agda.Primitive public
open import Agda.Builtin.Equality public
open import Data.Product renaming (proj₁ to fst ; proj₂ to snd) public
open import Data.Sum using () renaming (_⊎_ to _+_ ; inj₁ to left ; inj₂ to right) public

variable
  𝑖 𝑗 𝑘 : Level

𝒫 : Set 𝑖 -> Set (lsuc 𝑖)
𝒫 X = X -> Set _

singl : {X : Set 𝑖} -> X -> 𝒫 X
singl x = λ y -> x ≡ y

_∩-𝒫_ : ∀{X : Set 𝑖} -> 𝒫 X -> 𝒫 X -> 𝒫 X
_∩-𝒫_ A B x = A x × B x

_∪-𝒫_ : ∀{X : Set 𝑖} -> 𝒫 X -> 𝒫 X -> 𝒫 X
_∪-𝒫_ A B x = A x + B x

_≤-𝒫_ : ∀{X : Set 𝑖} -> 𝒫 X -> 𝒫 X -> Set _
_≤-𝒫_ A B = ∀ x -> A x -> B x

∑_ : ∀ {A : Set 𝑖} → (A → Set 𝑗) → Set (𝑖 ⊔ 𝑗)
∑_ = Σ _

_∘_ : ∀{A : Set 𝑖} {B : Set 𝑗} {C : Set 𝑘} -> (B -> C) -> (A -> B) -> (A -> C)
f ∘ g = λ x -> f (g x)

record Eval (A : Set 𝑖) (B : Set 𝑗) : Set (𝑖 ⊔ 𝑗) where
  field ⟦_⟧ : A -> B

open Eval {{...}} public

module _ {V : Set 𝑖} (E : V -> V -> Set 𝑗) where
  data Path : V -> V -> Set (𝑖 ⊔ 𝑗) where
    [] : ∀{v} -> Path v v
    _∷_ : ∀{a b c} -> E a b -> Path b c -> Path a c



