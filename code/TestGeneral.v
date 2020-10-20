(* Author: Jasper Hugunin *)

From WhyNotW Require Import Prelude.
From WhyNotW Require Import General.

(**
We specialize the general case to several specific inductive types,
and check that we get the expected behavior.
*)

Module test_nat.
(** * Natural numbers: Inductive nat := O | S (n : nat). *)

(* Constructor tags *)
Notation OO := false.
Notation SS := true.

Definition nat_code : Code@{Set} :=
  nonind 2 λ b ↦ match b with OO => nil | SS => ind nil end.

Definition nat := El nat_code.
Definition O := intro nat_code [OO].
Definition S n := intro nat_code [SS; n].

Section nat_rect.
Universe j.
Context
  (P : nat → Type@{j})
  (ISO : P O)
  (ISS : ∀ n, P n → P (S n))
.
Definition IS arg : liftP@{Set Set j} nat_code P arg → P (intro nat_code arg) :=
  match arg with
  | [OO] => λ '[] ↦ ISO
  | [SS; n] => λ '[IH] ↦ ISS n IH
  end.
Definition nat_rect : ∀ n, P n := rec nat_code P IS.

(* Check that the expected equations hold by rec_eq = refl *)
Definition test_eq_O := convertible
  (rec_eq nat_code P IS [OO])
  (convertible (nat_rect O) ISO).
Definition test_eq_S n := convertible
  (rec_eq nat_code P IS [SS; n])
  (convertible (nat_rect (S n)) (ISS n (nat_rect n))).

End nat_rect.
End test_nat.

Module test_code.
(** * The type of codes themselves: this can be used to bootstrap. *)
(** This tests infinitary arguments *)
(*
Inductive Code :=
  | nil
  | nonind (A : Type@{i}) (B : A → Code)
  | inf_ind (Ix : Type@{i}) (B : Code)
  | ind (B : Code) (* morally ind B = inf_ind 1 B *)
.
*)
Section test_code.
Universe i.
Universe i'.
Constraint i <= i'.

(* Constructor tags *)
Notation nil' := (false; false).
Notation nonind' := (false; true).
Notation inf_ind' := (true; false).
Notation ind' := (true; true).

Definition Code_code : Code@{i'} :=
  nonind (2 × 2) λ tag ↦ match tag with
    | nil' => nil
    | nonind' => nonind Type@{i} λ A ↦ inf_ind A nil
    | inf_ind' => nonind Type@{i} λ Ix ↦ ind nil
    | ind' => ind nil
    end.

(* Note that Code@{i} is in Type@{i+1}. *)
Definition Code_ : Type@{i'} := El Code_code.
Definition nil_ : Code_ := intro Code_code [nil'].
Definition nonind_ (A : Type@{i}) (B : A → Code_) : Code_ :=
  intro Code_code [nonind'; A; B].
Definition inf_ind_ (Ix : Type@{i}) (B : Code_) : Code_ :=
  intro Code_code [inf_ind'; Ix; B].
Definition ind_ (B : Code_) : Code_ :=
  intro Code_code [ind'; B].

Section code_rect.
Universe j.
Context
  (P : Code_ → Type@{j})
  (IS_nil : P nil_)
  (IS_nonind : ∀ A B, (∀ a, P (B a)) → P (nonind_ A B))
  (IS_inf_ind : ∀ A B, P B → P (inf_ind_ A B))
  (IS_ind : ∀ B, P B → P (ind_ B))
.

Definition IS arg : liftP@{i' i' j} Code_code P arg → P (intro Code_code arg) :=
  match arg with
  | [nil'] => λ '[] ↦ IS_nil
  | [nonind'; A; B] => λ '[IH] ↦ IS_nonind A B IH
  | [inf_ind'; A; B] => λ '[IH] ↦ IS_inf_ind A B IH
  | [ind'; B] => λ '[IH] ↦ IS_ind B IH
  end.
Definition Code_rect : ∀ A, P A := rec Code_code P IS.

(* Check that the expected equations hold by rec_eq = refl *)
Definition test_eq_nil := convertible
  (rec_eq Code_code P IS [nil'])
  (convertible (Code_rect nil_) IS_nil).
Definition test_eq_nonind A B := convertible
  (rec_eq Code_code P IS [nonind'; A; B])
  (convertible
   (Code_rect (nonind_ A B))
   (IS_nonind A B (Code_rect ∘ B))).
Definition test_eq_inf_ind A B := convertible
  (rec_eq Code_code P IS [inf_ind'; A; B])
  (convertible (Code_rect (inf_ind_ A B)) (IS_inf_ind A B (Code_rect B))).
Definition test_eq_ind B := convertible
  (rec_eq Code_code P IS [ind'; B])
  (convertible (Code_rect (ind_ B)) (IS_ind B (Code_rect B))).
End code_rect.
End test_code.
End test_code.

Module test_list.
(** * Lists: Inductive list A := nil | cons (a : A) (l : list A). *)
(* Because we are working internally, uniform parameters are free. *)
Section test_list.
Universe i.
Context (A : Type@{i}).

(* Constructor tags *)
Notation nil' := false.
Notation cons' := true.

Definition list_code : Code@{i} :=
  nonind 2 λ b ↦ match b with
    | nil' => nil
    | cons' => nonind A λ a ↦ ind nil
    end.

Definition list : Type@{i} := El list_code.
Definition nil : list := intro list_code [nil'].
Definition cons (a : A) (l : list) : list := intro list_code [cons'; a; l].

Section list_rect.
Universe j.
Context
  (P : list -> Type@{j})
  (IS_nil : P nil)
  (IS_cons : ∀ a l, P l → P (cons a l))
.

Definition IS arg : liftP@{i i j} list_code P arg → P (intro list_code arg) :=
  match arg with
  | [nil'] => λ '[] ↦ IS_nil
  | [cons'; a; l] => λ '[IH] ↦ IS_cons a l IH
  end.
Definition list_rect : ∀ l, P l := rec list_code P IS.

(* Check that the expected equations hold by rec_eq = refl *)
Definition test_eq_nil := convertible
  (rec_eq list_code P IS [nil'])
  (convertible (list_rect nil) IS_nil).
Definition test_eq_cons a l := convertible
  (rec_eq list_code P IS [cons'; a; l])
  (convertible (list_rect (cons a l)) (IS_cons a l (list_rect l))).

End list_rect.
End test_list.
End test_list.
