(* Author: Jasper Hugunin *)

From WhyNotW Require Import Prelude.
From WhyNotW Require Import Bootstrap.
From Coq Require Import Ltac.

(* We see that Code = El "Code". *)

Section test_code.
Universes i i' i''.
Constraint i < i', i' < i''.

Definition Code_code : Code@{i' i''} :=
  choice
   (choice
    nil (* nil' *)
    (choice
     (nonind Type@{i} λ A ↦ inf_ind A nil) (* nonind' *)
     (ind (ind nil)))) (* choice' *)
   (choice
    (nonind Type@{i} λ Ix ↦ ind nil) (* inf_ind' *)
    (ind nil)). (* ind' *)

(* Code codes for itself *)
Definition test_bootstrap := convertible
  Code@{i i'}
  (El@{i' i''} Code_code).

End test_code.