Require Import Utf8.

(** * Intensional Type Theory with Guarded Recursive Types qua Fixed Points on Universes *)

(** ** Syntactic Motivation *)
(** *** II.A: Fixed Points on Universes *)
Axiom later : Type -> Type.
Notation "▸ T" := (later T) (at level 50). (* \blacktriangleright *)
Axiom next : forall {T:Type}, T -> ▸ T.
Axiom lapp : forall {A B:Type}, ▸(A->B) -> ▸A -> ▸B.
Notation "t ⊛ u" := (lapp t u) (at level 49). (* \circledast *)

(* "Definitional" equalities *)
Definition nd_compose {A B C:Type} (f:B->C) (g:A->B) : A -> C :=
  λ a, f (g a).
Notation "f ∘ g" := (nd_compose f g) (at level 55).
Axiom next_id : forall (T:Type) u, next (λ (x:T), x) ⊛ u = u.
Axiom next_compose : forall (A B C:Type) s t u,
                       next(@nd_compose A B C) ⊛ s ⊛ t ⊛ u = s ⊛ (t ⊛ u).
Axiom next_app : forall (A B :Type) (t:A->B) u,
                   next t ⊛ next u = next (t u).
Axiom next_right : forall (A B:Type) u (t:A),
                     u ⊛ next t = next (λ (g:A->B), g t) ⊛ u.

(* Fixpoints *)
Axiom gfix : forall {A:Type}, ((▸A)->A) -> A.
Axiom gfix_red : forall {A:Type} (f:(▸A)->A),
                   gfix f = f (next (gfix f)).
                   
Axiom grec : forall {U:Type}, (▸U -> U) -> U.
Notation "'μ' X , A" := (grec (fun X => A)) (at level 44).

Axiom tlater : forall {T:Type}, ▸ T -> T.
Notation "▹ T" := (tlater T) (at level 50). (* \triangleright *)
(** Guarding is enforced by requiring ▹ to force later versions *)

Open Scope type_scope.
Example Str : Type := μ X , nat * ▹ X.

(** ** II.B: Example: A domain equation using dependent types *)

Definition pfix {A B:Type} (t:((A->▸B)->A->B)) : A -> B :=
  gfix (λ (y:▸(A->B)), t (λ a, y ⊛ next a)).
Require Import Setoid.
Lemma pfix_red : forall {A B:Type} t,
                   @pfix A B t = t (λ y, next (pfix t y)).
Proof. intros. unfold pfix.
       rewrite gfix_red at 1. f_equal.
       Require Import FunctionalExtensionality.
       apply FunctionalExtensionality.functional_extensionality.
       intros. rewrite next_app. reflexivity.
Qed.

Require Import Coq.Vectors.Fin.
Definition F X (n:nat) := (Fin.t n + ((▹ X n) * (▹ X n)) + (▹ X (plus n 1))).
Definition Lam (n:nat) : Type :=
  pfix (fun X => λ n, F X n) n.
                              


