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
  


  pfix : ∀ {l}{A B : Set l} → ((A → ▸ B) → A → B) → A → B
  pfix t = gfix (λ y → t (λ y → next (pfix t y)))
  
  pfix-red : ∀ {l}{A B : Set l} (t : ((A → ▸ B) → A → B)) →
               pfix t ≡ t (λ y → next (pfix t y))
  pfix-red t = refl

  -- Lam n example
  F : ∀ {l} → (ℕ → ▸ (Set l)) → ℕ → Set l
  F X n = Fin n ⊎ ((▹ X n) × (▹ X n)) ⊎ (▹ X (Data.Nat._+_ n  1))
  {- This works, but not how I'd expect.  If the level is provided
     explicitly to pfix, we're not producing a result in the right
     universe.  It's possible that the types for the fixpoint params
     should be free to live in different universes, and this is being
     done implicitly in the Coq version via typical ambiguity + cumulativity.
     But the paper doesn't model a universe heirarchy, so these should
     be the same universe...
  -}
  Lam : ∀ {l} → ℕ → Set l
  Lam {l} n = pfix (λ X n → F (λ z → X (Level.lift z)) (lower n)) (Level.lift n)

