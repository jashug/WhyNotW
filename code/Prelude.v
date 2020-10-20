(* Author: Jasper Hugunin *)

(**
We use the -noinit option in _CoqProject to start from a blank slate.
We also use -indices-matter, to be better compatible with HoTT.
*)

#[export] Set Universe Polymorphism.
(* #[export] Set Polymorphic Inductive Cumulativity. (* not needed, just cool *) *)
#[export] Set Primitive Projections. (* strict eta for pairs *)
#[export] Unset Elimination Schemes. (* we'll declare only the ones we need *)

(*
We'll avoid conflicting with Coq's notation levels.
Consists of just Reserved Notations and Scopes.
*)
From Coq Require Export Init.Notations.

(** We use Unicode characters freely in our notations. *)

(** * Functions *)

Notation "'Π' x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[  ' '[  ' Π  x  ..  y ']' ,  '/' P ']'") : type_scope.
Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[  ' '[  ' ∀  x  ..  y ']' ,  '/' P ']'") : type_scope.

(** Can't go far without implication. *)
Notation "A -> B" := (forall (_ : A), B) : type_scope.
Notation "A → B" := (A -> B)
  (at level 99, right associativity, B at level 200) : type_scope.

(** composition of functions *)
Notation "f ∘ g" := (fun x => f (g x))
  (at level 40, left associativity) : core_scope.

(** * Finite types *)
Inductive void : Set := .
Notation "⊥" := void : type_scope.
Notation "0" := ⊥ : type_scope.

Inductive unit : Set := tt.
Notation "⊤" := unit : type_scope.
Notation "1" := ⊤ : type_scope.
Notation "★" := tt : core_scope.

Inductive bool : Set := true | false.
Notation "2" := bool : type_scope.

(** * Dependent pairs *)
Record prod@{i} (A : Type@{i}) (B : A → Type@{i}) : Type@{i} :=
  pair { fst : A ; snd : B fst }.
Arguments pair {A B} & fst snd.
Arguments fst {A B} _.
Arguments snd {A B} _.

Notation "x .1" := (x.(fst))
  (at level 1, left associativity, format "x .1") : core_scope.
Notation "x .2" := (x.(snd))
  (at level 1, left associativity, format "x .2") : core_scope.

Notation "∃ x .. y , P" := (prod _ (fun x => .. (prod _ (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity,
   format "'[  ' '[  ' ∃  x  ..  y ']' ,  '/' P ']'")
  : type_scope.
Notation "'Σ' x .. y , P" := (prod _ (fun x => .. (prod _ (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity,
   format "'[  ' '[  ' Σ  x  ..  y ']' ,  '/' P ']'")
  : type_scope.
Notation "( x , .. , y , z )" := (pair x .. (pair y z) ..) : core_scope.
Notation "( x ; .. ; y ; z )" := (pair x .. (pair y z) ..) : core_scope.

Notation "A * B" := (prod A (fun _ => B))  : type_scope.
Notation "A ∧ B" := (prod A (fun _ => B))
  (at level 80, right associativity) : type_scope.
Notation "A × B" := (prod A (fun _ => B))
  (at level 80, right associativity) : type_scope.

(* tuple notation *)
Notation "[ x ; .. ; y ]" := (pair x .. (pair y ★) ..) : core_scope.
Notation "[ ]" := ★ : core_scope.

(** * W types *)
Inductive W@{i} (A : Type@{i}) (B : A → Type@{i}) : Type@{i} :=
  | sup (a : A) (f : B a → W A B) : W A B.
Arguments sup {A B} & a f.

Definition W_rect@{i j} (A : Type@{i}) (B : A → Type@{i}) (P : W A B → Type@{j})
  (IS : ∀ a f, (∀ b, P (f b)) → P (sup a f)) : ∀ w, P w :=
  fix rect w := match w with sup a f => IS a f (rect ∘ f) end.

(** * Identity/Path types *)
Inductive Id@{i} (A : Type@{i}) (x : A) : A → Type@{i} := refl : Id A x x.
Arguments Id {A} x y.
Arguments refl {A} x, {A x}.

(** A few lemmas about Id *)
Definition cong@{i j} {A : Type@{i}} {B : Type@{j}} (f : A → B) {x y : A}
  (e : Id x y) : Id (f x) (f y) :=
  match e with refl => refl end.
(* Transitivity from the middle. *)
Definition v_trans@{i} {A : Type@{i}} {x y z : A}
  (e1 : Id y x) (e2 : Id y z) : Id x z :=
  match e1 with refl => e2 end.

(** * Sum types *)
(** We define sum types from bool and Σ *)

Definition sum@{i} (A B : Type@{i}) : Type@{i} :=
  Σ (b : 2), match b with false => A | true => B end.
Notation inl a := (false; a).
Notation inr b := (true; b).
Notation inl' := (fun a => inl a).
Notation inr' := (fun b => inr b).

Notation "A + B" := (sum A B) : type_scope.
Notation "A ∨ B" := (sum A B) (at level 85, right associativity) : type_scope.
Notation "A ⊎ B" := (sum A B) (at level 85, right associativity) : type_scope.
Notation "A ⊔ B" := (sum A B) (at level 85, right associativity) : type_scope.

Definition option@{i} (A : Type@{i}) : Type@{i} := sum 1 A.
Notation None := (inl ★).
Notation Some a := (inr a).
Notation Some' := (fun a => Some a).

(** Notation for tests *)
Notation convertible x y := (refl : Id x y).