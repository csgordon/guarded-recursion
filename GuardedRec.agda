open import Data.Sum
open import Data.Fin
open import Data.Product
open import Data.Empty
open import Data.Nat
open import Level
open import Relation.Binary.PropositionalEquality
open import Function

module GuardedRec where

  {- Intensional Type Theory with Guarded Recursive Types qua Fixed Points on Universes -}


  -- Syntactic Motivation
  -- II.A: Fixed Points on Universes
  
  -- We'll try to model the later modality as a type, and make as many
  -- of the paper's definitional equalities as possible hold here
  data ▸_ {l : Level} (T : Set l) : Set l where
    next : T → (▸ T)
   -- open-type : ∀ (x : ⊥) → ▸ T -- random other ctor so handling next in application isn't considered complete.

  _⊛_ : ∀ {l : Level}{A : Set l}{B : Set l} → ▸ (A → B) → (▸ A) → (▸ B)
  next t ⊛ next u = next (t u)
  --t ⊛ next x₁ = {!!}
  --t ⊛ u = {!!}
  

  next-id : ∀ {l} {T : Set l} u → next (λ (x : T) → x) ⊛ u ≡ u
  next-id (next x) = refl
  
  next-right : ∀ {l} {A B : Set l} u (t : A) →
                 u ⊛ next t ≡ next (λ (g : A → B) → g t) ⊛ u
  next-right (next x) t = refl
  
  next-compose : ∀ {l} {A B C : Set l} (s : ▸ (B → C)) t (u : ▸ C) →
                   ((next (_∘′_) ⊛ s) ⊛ t) ⊛ u ≡ s ⊛ (t ⊛ u)
  next-compose (next s') (next t') (next u') = refl
  
  -- So we've gotten the first four definitional equalities to hold definitionally in Agda!
  -- We can also define gfix here, with warnings about the termination checker. 
  gfix : ∀ {l} {A : Set l} → (▸ A → A) → A
  gfix f = f (next (gfix f))
  

  postulate grec : ∀ {l} {U : Set l} → (▸ U → U) → U

  syntax grec (\ x → b) = μ x , b
  
  ▹_ : ∀ {l} {T : Set l} → ▸ T → T
  ▹ next t = t
  
  Str : Set
  Str = μ X , (ℕ × ▹ X)
  


  {- An important subtlety that arises here is that A and B can be in
     different universe levels, as in the Lam example below, where
     A : Set 0 and B : Set 1, since we're building a function of
     type ℕ → Set 0.
  -}
  pfix : ∀ {la lb}{A : Set la}{B : Set lb} → ((A → ▸ B) → A → B) → A → B
  pfix {la}{lb}{A}{B} t = gfix (λ y → t (λ y → next (pfix t y)))
  {- The Coq version is actually:
  --pfix {la}{lb}{A}{B} t = gfix (λ (y : ▸ (A → B)) → t (λ a → y ⊛ next a))
    This doesn't work here because of a level issue with y.  So I
    suspect that it flies in Coq due to some typical ambiguity + cumulativity.
    But the example below is defined in the LICS'13 paper without 
    any such fanciness!  We've defined pfix using the explicit definitional
    equality from the paper, so computationally it behaves correctly.
    But we're still missing something subtle from the paper (or there's
    a bug in the paper?).
  -}
  
  pfix-red : ∀ {l}{A B : Set l} (t : ((A → ▸ B) → A → B)) →
               pfix t ≡ t (λ y → next (pfix t y))
  pfix-red t = refl

  -- Lam n example
  F : ∀ {l} → (ℕ → ▸ (Set l)) → ℕ → Set l
  F X n = Fin n ⊎ ((▹ X n) × (▹ X n)) ⊎ (▹ X (Data.Nat._+_ n  1))
  
  Lam : ℕ → Set Level.zero
  Lam n = pfix (λ X n₁ → F X n₁) n
