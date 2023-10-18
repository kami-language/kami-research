
module KamiResearch.Semantics.Trace.Notes-2023-10-18 where

open import Data.Product
open import Data.Sum
open import Data.List

open import KamiResearch.Common

lone = lsuc lzero

record Env : Set lone where
  field P : Set
  field E : P -> Set
  field Op : Set
  -- field op : E -> Op
  field π : Op -> 𝒫 P
  -- field act : ∀ x -> (∀(p : ∑ (π x)) -> E (fst p)) -> 𝒫 (∀(p : ∑ (π x)) -> E (fst p)) -- (∑ (π x) -> E)
  field act : ∀ x -> (∀ p -> π x p -> E p) -> 𝒫 (∀ p -> π x p -> E p)

open Env

module _ (e : Env) where
  State = ∀(p : P e) -> E e p

  -- substate : {X : 𝒫 (P e)} -> (∑ X -> E e) -> (P e -> E e) -> Set
  -- substate {X} u s = ∀ (x : ∑ X) -> u x ≡ s (fst x)

  a : State -> 𝒫 State
  a s₀ s₁ = ∑ λ x -> act e x (λ p _ -> s₀ p) (λ p _ -> s₁ p)


  Trace : (s t : State) -> Set
  Trace = Path a

  -- data Trace : (s t : State) -> Set where
  --   [] : ∀{t} -> Trace t t
  --   _∷[_]_ : ∀{}

------------------------------------------------------------------------
-- example: the SR (send-receive) language

open import Data.Nat renaming (ℕ to Nat ; _+_ to _+-ℕ_)
open import Data.Bool
open import Data.Unit renaming (⊤ to Unit)

data SRType : Set where
  𝔹 ℕ 𝟙 : SRType
  _+-SR_ _×-SR_ : (A B : SRType) -> SRType

eval-SRType : SRType -> Set
eval-SRType 𝔹 = Bool
eval-SRType ℕ = Nat
eval-SRType 𝟙 = Unit
eval-SRType (X +-SR Y) = eval-SRType X + eval-SRType Y
eval-SRType (X ×-SR Y) = eval-SRType X × eval-SRType Y

instance
  _ : Eval SRType Set
  _ = record { ⟦_⟧ = eval-SRType }


module _ {Proc : Set} where

  data SRCommand (p : Proc) : (A B : SRType) -> Set where
    compute : ∀{A B} -> (⟦ A ⟧ -> ⟦ B ⟧) -> SRCommand p A B
    send : ∀{A} -> ∀ X -> (q : Proc) -> SRCommand p (A ×-SR X) A
    recv : ∀{A} -> ∀ X -> (q : Proc) -> SRCommand p A (A ×-SR X)

  SRTerm : (p : Proc) -> (A B : SRType) -> Set
  SRTerm p = Path (SRCommand p)

  E-SR : Proc -> Set
  E-SR = λ p -> ∑ λ A -> ∑ λ B -> SRTerm p A B × ⟦ A ⟧

  data SROp : Set where
    compute : ∀(p : Proc) -> ∀{A B : SRType} -> (f : ⟦ A ⟧ -> ⟦ B ⟧) -> SROp
    move : ∀(p q : Proc) -> ∀(X : SRType) -> SROp

  Op-SR : Set
  Op-SR = SROp

  π-SR-impl : ∀{p A B} -> SRCommand p A B -> 𝒫 Proc
  π-SR-impl {p} (compute x) = singl p
  π-SR-impl {p} (send X q) = singl p ∪-𝒫 singl q
  π-SR-impl {p} (recv X q) = singl p ∪-𝒫 singl q

  π-SR : Op-SR -> 𝒫 Proc
  π-SR (compute p f) = singl p
  π-SR (move p q X) = singl p ∪-𝒫 singl q

  data act-SR : ∀ x -> (∀ p -> π-SR x p -> E-SR p) -> (∀ p -> π-SR x p -> E-SR p) -> Set where
    compute : ∀{A B C : SRType} -> ∀ p -> (f : ⟦ A ⟧ -> ⟦ B ⟧) -> (a : ⟦ A ⟧)
              -> (ts : SRTerm p B C)
              -> act-SR (compute p f)
                        (λ {q refl -> A , C , compute f ∷ ts , a})
                        (λ {q refl -> B , C , ts , f a})
    move : ∀{A B X C : SRType} -> ∀ p q -> (a : ⟦ A ⟧) -> (b : ⟦ B ⟧) -> (x : ⟦ X ⟧)
         -> (ts : SRTerm p A C) -> (us : SRTerm q (B ×-SR X) C)
         -> act-SR (move p q X)
              (λ { _ (left refl) -> A ×-SR X , C , send X q ∷ ts , a , x
                 ; _ (right refl) -> B , C , recv X p ∷ us , b
                 })
              (λ { _ (left refl) -> A , C , ts , a
                 ; _ (right refl) -> B ×-SR X , C , us , b , x
                 })

  EnvSRTerm : Env
  EnvSRTerm = record
    { P = Proc
    ; E = E-SR
    ; Op = Op-SR
    ; π = π-SR
    ; act = act-SR
    }

------------------------------------------------------------------------
-- example with two processes

data Proc2 : Set where
  p q : Proc2

module test1 where
  term-p : SRTerm p ℕ ℕ
  term-p = compute {B = 𝟙 ×-SR ℕ} (λ x → tt , x) ∷ send ℕ q ∷ recv ℕ q ∷ compute snd ∷ []

  term-q : SRTerm q 𝟙 𝟙
  term-q = recv ℕ p ∷ compute (λ (x , n) -> (x , suc n)) ∷ send ℕ p ∷ []

  start : State (EnvSRTerm {Proc2})
  start p = ℕ , ℕ , term-p , 0
  start q = 𝟙 , 𝟙 , term-q , tt

  end : State (EnvSRTerm {Proc2})
  end p = ℕ , ℕ , [] , 1
  end q = 𝟙 , 𝟙 , [] , tt

  trace : Trace EnvSRTerm start end
  trace = {!!} -- ((compute p (λ x → tt , x)) , {!compute ? ? ? ?!}) ∷ {!!}




