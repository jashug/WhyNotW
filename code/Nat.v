(* Author: Jasper Hugunin

Here we prove that W types plus Id types with strict J and Sg types with eta
are enough to define N without using function extensionality.

Note that function extensionality breaks canonicity for this type
(by breaking canonicity for Id). However, as long as Id satisfies J strictly,
this still computes, which is better than the standard encoding.

Working in Coq we lack strict eta for unit, thus have to work a little harder
in the successor case than in the paper, but it proves no obstacle.
*)

Set Universe Polymorphism.
Set Primitive Projections.

(*
We define Id to land in Type, prod to have strict eta,
and W since it isn't in the prelude.
*)
Inductive Id@{i} (A : Type@{i}) (x : A) : A -> Type@{i} := refl : Id A x x.
Arguments Id {A} x y.
Arguments refl {A} x, {A x}.

Record prod@{i} (A : Type@{i}) (B : A -> Type@{i}) : Type@{i}
  := pair { p1 : A ; p2 : B p1 }.
Arguments pair {A B} p1 p2.
Arguments p1 {A B} _.
Arguments p2 {A B} _.

Inductive W@{i} (A : Type@{i}) (B : A -> Type@{i}) : Type@{i}
  := sup (a : A) (f : B a -> W A B) : W A B.
Arguments sup {A B} a f.

Notation OO := false.
Notation SS := true.

(* Here is the definition of N: *)
Definition N_pre : Set := W@{Set} bool (fun b => if b then unit else False).
Fixpoint canonical (n : N_pre) : Set
  := match n with
     | sup OO f =>
       Id (fun XX : False => match XX with end) f
     | sup SS f =>
       prod N_pre (fun prev =>
       prod (Id (fun _ => prev) f)
            (fun _ => canonical (f tt)))
     end.

Definition N : Set := prod N_pre canonical.
Definition O : N := pair (sup false _) refl.
Definition S (n : N) : N := pair (sup true _) (pair (p1 n) (pair refl (p2 n))).

(*
And here we define induction,
first with an explicit proof term and then again by tactics.
Read whichever you are most comfortable with.
*)
Section induction.
Universe i.
Context
  (P : N -> Type@{i})
  (ISO : P O)
  (ISS : forall n, P n -> P (S n))
.
Definition N_rect@{} : forall n, P n
  := let fix N_rect (n_pre : N_pre)
      : forall n_good : canonical n_pre, P (pair n_pre n_good)
      := match n_pre with
         | sup OO f => fun (eq : canonical (sup OO f)) =>
           match eq in Id _ f return P (pair (sup false f) eq)
           with refl => ISO end
         | sup SS f =>
           fun '(pair pred (pair eq pred_good) : canonical (sup true f)) =>
           match eq in Id _ f
           return
             forall pred_good : canonical (f tt),
             P (pair (f tt) pred_good) ->
             P (pair (sup true f) (pair pred (pair eq pred_good)))
           with refl => fun pred_good IH => ISS (pair pred pred_good) IH end
           pred_good (N_rect (f tt) pred_good)
         end in
      fun '(pair pre good) => N_rect pre good.

Definition N_rect_ltac@{} : forall n, P n.
intros [n_pre n_good].
induction n_pre as [a f IH] using W_rect@{Set i}; destruct a.
- (* case S *)
  destruct n_good as [pred [eq pred_good]].
  destruct eq.
  apply (ISS (pair pred pred_good)).
  apply (IH tt).
- (* case O *)
  simpl in n_good; rename n_good into eq.
  destruct eq.
  apply ISO.
Defined.

(* And then we check that the expected equations hold strictly. *)
Notation convertible x y := (refl : Id x y).

Check (fun n => convertible (N_rect (S n)) (ISS n (N_rect n))).
Check (convertible (N_rect O) ISO).

Check (fun n => convertible (N_rect_ltac (S n)) (ISS n (N_rect_ltac n))).
Check (convertible (N_rect_ltac O) ISO).

End induction.