(* Author: Jasper Hugunin

Here we prove that W types plus Id types with strict J and Sg types with eta
are enough to define N without using function extensionality.

Note that function extensionality breaks canonicity for this type
(by breaking canonicity for Id). However, as long as Id satisfies J strictly,
this still computes, which is better than the standard encoding.

Working in Coq we lack strict eta for unit, thus have to work a little harder
in the successor case than in the paper, but it proves no obstacle.
(* *)
 *)
From Coq Require Import Init.Ltac.

From WhyNotW Require Import Prelude.

Notation OO := false.
Notation SS := true.

(* Here is the definition of N: *)
Definition nat_pre : Set :=
  W@{Set} 2 (λ b ↦ match b with OO => 0 | SS => 1 end).
Fixpoint canonical (n : nat_pre) : Set
  := match n with
     | sup OO f =>
       Id (λ XX : 0 ↦ match XX return nat_pre with end) f
     | sup SS f =>
       Σ (prev : nat_pre),
       Id (λ _ ↦ prev) f × canonical (f ★)
     end.

Definition nat : Set := Σ (n : nat_pre), canonical n.
Definition O : nat := (sup OO _; refl).
Definition S (n : nat) : nat := (sup SS _; fst n; refl; snd n).

(*
And here we define induction,
first with an explicit proof term and then again by tactics.
Read whichever you are most comfortable with.
*)
Section induction.
Universe i.
Context
  (P : nat → Type@{i})
  (ISO : P O)
  (ISS : ∀ n, P n → P (S n))
.
Definition nat_rect@{} : ∀ n, P n
  := let fix nat_rect (n_pre : nat_pre)
      : ∀ n_canon : canonical n_pre, P (pair n_pre n_canon)
      := match n_pre with
         | sup OO f => λ 'refl ↦ ISO
         | sup SS f =>
           λ '(pair pred (pair eq pred_canon) : canonical (sup true f)) ↦
           match eq in Id _ f
           return
             ∀ pred_canon : canonical (f ★),
             P (pair (f ★) pred_canon) →
             P (pair (sup true f) (pair pred (pair eq pred_canon)))
           with refl => λ pred_canon IH ↦ ISS (pair pred pred_canon) IH end
           pred_canon (nat_rect (f ★) pred_canon)
         end in
      λ '(pair pre canon) ↦ nat_rect pre canon.

Definition nat_rect_ltac@{} : ∀ n, P n.
intros [n_pre n_canon].
induction n_pre as [a f IH] using W_rect@{Set i}; destruct a.
- (* case S *)
  destruct n_canon as [pred [eq pred_canon]].
  destruct eq.
  apply (ISS (pair pred pred_canon)).
  apply (IH ★).
- (* case O *)
  simpl in n_canon; rename n_canon into eq.
  destruct eq.
  apply ISO.
Defined.

(* And then we check that the expected equations hold strictly. *)
Definition test_eq_O := convertible (nat_rect O) ISO.
Definition test_eq_S n := convertible (nat_rect (S n)) (ISS n (nat_rect n)).

Definition test_eq_O' := convertible (nat_rect_ltac O) ISO.
Definition test_eq_S' n :=
  convertible (nat_rect_ltac (S n)) (ISS n (nat_rect_ltac n)).

End induction.