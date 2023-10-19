
module KamiResearch.Semantics.Trace.Notes-2023-10-19 where

open import Data.Product
open import Data.Sum
open import Data.List
open import Data.Unit renaming (⊤ to Unit)
open import Data.Fin

-- open import KamiResearch.Common

open import Agora.Conventions
open import Agora.Data.Universe.Power.Definition

------------------------------------------------------------------------
-- prelude


record Eval (A : Set 𝑖) (B : Set 𝑗) : Set (𝑖 ⊔ 𝑗) where
  field ⟦_⟧ : A -> B

open Eval {{...}} public


module _ {V : Set 𝑖} (E : V -> V -> Set 𝑗) where
  data Path : V -> V -> Set (𝑖 ⊔ 𝑗) where
    [] : ∀{v} -> Path v v
    _∷_ : ∀{a b c} -> E a b -> Path b c -> Path a c

-- isDecidable : ∀(A : 𝒰 𝑖) -> 𝒰 _
-- isDecidable A = (¬ A) +-𝒰 A

-- record isDiscrete (A : 𝒰 𝑖) : 𝒰 𝑖 where
--   field _≟_ : (a b : A) -> Decision (a ≡-Str b)
-- open isDiscrete {{...}} public

------------------------------------------------------------------------

record Env : 𝒰₁ where
  field P : 𝒰₀
  field E : P -> 𝒰₀
  field Op : 𝒰₀
  field π : Op -> 𝒫 P
  field act : Op -> (∏ E) -> List (∏ E)
  field op : ∀{p} -> E p -> Maybe Op

open Env

module _ (e : Env) where
  State = ∀(p : P e) -> E e p

  {-# NON_TERMINATING #-}
  eval : ∀{m} -> (Fin m -> P e) -> ∀{n} -> (Fin n -> P e) -> State -> State
  eval allps {zero} ps s = s
  eval allps {suc n} ps s with op e (s (ps zero))
  ... | nothing = eval allps {n} (λ i -> ps (suc i)) s
  ... | just x with act e x s
  ... | [] = eval allps {n} (λ i -> ps (suc i)) s
  ... | s' ∷ rs = eval allps allps s'

  -- substate : {X : 𝒫 (P e)} -> (∑ X -> E e) -> (P e -> E e) -> 𝒰₀
  -- substate {X} u s = ∀ (x : ∑ X) -> u x ≡ s (fst x)

  -- a : State -> 𝒫 State
  -- a s₀ s₁ = ∑ λ x -> act e x (λ p -> s₀ p) (λ p -> s₁ p)

  -- Trace : (s t : State) -> 𝒰₀
  -- Trace = Path a


------------------------------------------------------------------------
-- example: the SR (send-receive) language


data SRType : Set where
  BB NN 𝟙 : SRType
  _+-SR_ _×-SR_ : (A B : SRType) -> SRType

discrete-SRType : (A B : SRType) -> isDecidable (A ≡-Str B)
discrete-SRType BB BB = just refl-≣
discrete-SRType BB NN = left (λ ())
discrete-SRType BB 𝟙 = left (λ ())
discrete-SRType BB (B +-SR B₁) = left (λ ())
discrete-SRType BB (B ×-SR B₁) = left (λ ())
discrete-SRType NN BB = left (λ ())
discrete-SRType NN NN = just refl-≣
discrete-SRType NN 𝟙 = left (λ ())
discrete-SRType NN (B +-SR B₁) = left (λ ())
discrete-SRType NN (B ×-SR B₁) = left (λ ())
discrete-SRType 𝟙 BB = left (λ ())
discrete-SRType 𝟙 NN = left (λ ())
discrete-SRType 𝟙 𝟙 = just refl-≣
discrete-SRType 𝟙 (B +-SR B₁) = left (λ ())
discrete-SRType 𝟙 (B ×-SR B₁) = left (λ ())
discrete-SRType (A +-SR A₁) BB = left (λ ())
discrete-SRType (A +-SR A₁) NN = left (λ ())
discrete-SRType (A +-SR A₁) 𝟙 = left (λ ())
discrete-SRType (A +-SR A₁) (B +-SR B₁) with discrete-SRType A B | discrete-SRType A₁ B₁
... | left x | left y = left λ {refl-StrId -> y refl-≣}
... | left x | just y = left λ {refl-StrId -> x refl-≣}
... | just x | left y = left λ {refl-StrId -> y refl-≣}
... | just refl-≣ | just refl-≣ = just refl-≣
discrete-SRType (A +-SR A₁) (B ×-SR B₁) = left (λ ())
discrete-SRType (A ×-SR A₁) BB = left (λ ())
discrete-SRType (A ×-SR A₁) NN = left (λ ())
discrete-SRType (A ×-SR A₁) 𝟙 = left (λ ())
discrete-SRType (A ×-SR A₁) (B +-SR B₁) = left (λ ())
discrete-SRType (A ×-SR A₁) (B ×-SR B₁) with discrete-SRType A B | discrete-SRType A₁ B₁
... | left x | left y = left λ {refl-StrId -> y refl-≣}
... | left x | just y = left λ {refl-StrId -> x refl-≣}
... | just x | left y = left λ {refl-StrId -> y refl-≣}
... | just refl-≣ | just refl-≣ = just refl-≣

instance
  isDiscrete:SRType : isDiscrete SRType
  isDiscrete:SRType = record { _≟-Str_ = discrete-SRType }

eval-SRType : SRType -> Set
eval-SRType BB = Bool
eval-SRType NN = ℕ
eval-SRType 𝟙 = Unit
eval-SRType (X +-SR Y) = eval-SRType X +-𝒰 eval-SRType Y
eval-SRType (X ×-SR Y) = eval-SRType X × eval-SRType Y

instance
  _ : Eval SRType Set
  _ = record { ⟦_⟧ = eval-SRType }


module _ {Proc : Set} {{_ : isDiscrete Proc}} where

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

  -- data act-SR : ∀ x -> (∀ p -> π-SR x p -> E-SR p) -> (∀ p -> π-SR x p -> E-SR p) -> Set where
  --   compute : ∀{A B C : SRType} -> ∀ p -> (f : ⟦ A ⟧ -> ⟦ B ⟧) -> (a : ⟦ A ⟧)
  --             -> (ts : SRTerm p B C)
  --             -> act-SR (compute p f)
  --                       (λ {q refl-StrId -> A , C , compute f ∷ ts , a})
  --                       (λ {q refl-StrId -> B , C , ts , f a})
  --   move : ∀{A B X C : SRType} -> ∀ p q -> (a : ⟦ A ⟧) -> (b : ⟦ B ⟧) -> (x : ⟦ X ⟧)
  --        -> (ts : SRTerm p A C) -> (us : SRTerm q (B ×-SR X) C)
  --        -> act-SR (move p q X)
  --             (λ { _ (left refl-StrId) -> A ×-SR X , C , send X q ∷ ts , a , x
  --                ; _ (right refl-StrId) -> B , C , recv X p ∷ us , b
  --                })
  --             (λ { _ (left refl-StrId) -> A , C , ts , a
  --                ; _ (right refl-StrId) -> B ×-SR X , C , us , b , x
  --                })

  act-SR : Op-SR → ∏ E-SR → List (∏ E-SR)
  act-SR (compute p f) s with s p
  ... | A , .A , [] , a = []
  ... | A , B , (c ∷ cs) , a with c
  ... | compute f = (λ q -> case p ≟-Str q of
                              (λ _ -> s q)
                              (λ {refl-StrId -> _ , _ , cs , f a})
                     ) ∷ []
  ... | send X q = []
  ... | recv X q = []
  act-SR (move p q X) s with s p | s q
  ... | _ , _ , [] , _ | sq = []
  ... | _ , _ , (cp ∷ cps) , _ | _ , _ , [] , _ = []
  ... | _ , _ , (cp ∷ cps) , a | _ , _ , (cq ∷ cqs) , b with cp | cq
  ... | compute x | cq = []
  ... | send X₁ q₁ | compute x = []
  ... | send X₁ q₁ | send X₂ q₂ = []
  ... | send X₁ q₁ | recv X₂ q₂ = case X₁ ≟-Str X₂ of
    (λ _ -> [])
    (λ {refl-StrId ->
      (λ r -> case r ≟-Str p of
              (λ _ -> case r ≟-Str q of
                      (λ _ → s r)
                      λ {refl-StrId -> _ , _ , cqs , b , a .snd})
              (λ {refl-StrId -> _ , _ , cps , a .fst})
      ) ∷ []
    })
  ... | recv X₁ q₁ | cq = []

  op-SR : {p : Proc} → E-SR p → Maybe Op-SR
  op-SR (_ , _ , [] , a) = nothing
  op-SR {p} (_ , _ , (compute f ∷ cs) , a) = just (compute p f)
  op-SR {p} (_ , _ , (send X q ∷ cs) , a) = just (move p q X)
  op-SR {p} (_ , _ , (recv X q ∷ cs) , a) = just (move q p X)

  EnvSRTerm : Env
  EnvSRTerm = record
    { P = Proc
    ; E = E-SR
    ; Op = Op-SR
    ; π = π-SR
    ; act = act-SR
    ; op = op-SR
    }



data Proc2 : Set where
  p q : Proc2

allps : Fin 2 -> Proc2
allps zero = p
allps (suc x) = q

discrete-Proc2 : (a b : Proc2) → isDecidable (a ≡-Str b)
discrete-Proc2 p p = just refl-≣
discrete-Proc2 p q = left (λ ())
discrete-Proc2 q p = left (λ ())
discrete-Proc2 q q = just refl-≣

instance
  isDiscrete:Proc2 : isDiscrete Proc2
  isDiscrete:Proc2 = record { _≟-Str_ = discrete-Proc2 }

module test1 where
  term-p : SRTerm p NN NN
  term-p = compute {B = 𝟙 ×-SR NN} (λ x → tt , x) ∷ send NN q ∷ recv NN q ∷ compute snd ∷ []

  term-q : SRTerm q 𝟙 𝟙
  term-q = recv NN p ∷ compute (λ (x , n) -> (x , suc n)) ∷ send NN p ∷ []

  start : State (EnvSRTerm {Proc2})
  start p = NN , NN , term-p , 0
  start q = 𝟙 , 𝟙 , term-q , tt

  end : State (EnvSRTerm {Proc2})
  end p = NN , NN , [] , 1
  end q = 𝟙 , 𝟙 , [] , tt

  res = eval (EnvSRTerm {Proc2}) allps allps start

  res' : _ ×-𝒰 _
  res' = res p , res q

