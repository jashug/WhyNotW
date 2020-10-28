(* Author: Jasper Hugunin *)

From WhyNotW Require Import Prelude.
From WhyNotW Require Import Bootstrap.

(** * Natural numbers: Inductive nat := O | S (n : nat). *)

(* Constructor tags *)
Notation O' x := (false; x).
Notation S' x := (true; x).

Definition nat_code : Code@{Set _} := choice nil (ind nil).

Definition nat := El nat_code.
Definition O := intro nat_code (O' []).
Definition S n := intro nat_code (S' [n]).

Section nat_rect.
Universe j.
Context
  (P : nat → Type@{j})
  (ISO : P O)
  (ISS : ∀ n, P n → P (S n))
.
Definition IS arg : liftP@{Set _ Set j} nat_code P arg → P (intro nat_code arg) :=
  match arg with
  | O' [] => λ '[] ↦ ISO
  | S' [n] => λ '[IH] ↦ ISS n IH
  end.
Definition nat_rect : ∀ n, P n := rec nat_code P IS.

(* Check that the expected equations hold by rec_eq = refl *)
Definition test_eq_O := convertible
  (rec_eq nat_code P IS (O' []))
  (convertible (nat_rect O) ISO).
Definition test_eq_S n := convertible
  (rec_eq nat_code P IS (S' [n]))
  (convertible (nat_rect (S n)) (ISS n (nat_rect n))).

End nat_rect.