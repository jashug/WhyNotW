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
Notation O' x := (false; x).
Notation S' x := (true; x).

Definition nat_code : Code@{Set} := choice nil (ind nil).

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
Definition IS arg : liftP@{Set Set j} nat_code P arg → P (intro nat_code arg) :=
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
End test_nat.

Module test_list.
(** * Lists: Inductive list A := nil | cons (a : A) (l : list A). *)
(* Because we are working internally, uniform parameters are free. *)
Section test_list.
Universe i.
Context (A : Type@{i}).

(* Constructor tags *)
Notation nil' x := (false; x).
Notation cons' x := (true; x).

Definition list_code : Code@{i} :=
  choice nil (nonind A λ a ↦ ind nil).

Definition list : Type@{i} := El list_code.
Definition nil : list := intro list_code (nil' []).
Definition cons (a : A) (l : list) : list := intro list_code (cons' [a; l]).

Section list_rect.
Universe j.
Context
  (P : list -> Type@{j})
  (IS_nil : P nil)
  (IS_cons : ∀ a l, P l → P (cons a l))
.

Definition IS arg : liftP@{i i j} list_code P arg → P (intro list_code arg) :=
  match arg with
  | nil' [] => λ '[] ↦ IS_nil
  | cons' [a; l] => λ '[IH] ↦ IS_cons a l IH
  end.
Definition list_rect : ∀ l, P l := rec list_code P IS.

(* Check that the expected equations hold by rec_eq = refl *)
Definition test_eq_nil := convertible
  (rec_eq list_code P IS (nil' []))
  (convertible (list_rect nil) IS_nil).
Definition test_eq_cons a l := convertible
  (rec_eq list_code P IS (cons' [a; l]))
  (convertible (list_rect (cons a l)) (IS_cons a l (list_rect l))).

End list_rect.
End test_list.
End test_list.

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
(* Constructor tags *)
Notation nil' x := (false; false; x).
Notation nonind' x := (false; true; false; x).
Notation choice' x := (false; true; true; x).
Notation inf_ind' x := (true; false; x).
Notation ind' x := (true; true; x).

Section test_code.
Universe i.
Universe i'.
Constraint i <= i'.

Definition Code_code : Code@{i'} :=
  choice
   (choice
    nil (* nil' *)
    (choice
     (nonind Type@{i} λ A ↦ inf_ind A nil) (* nonind' *)
     (ind (ind nil)))) (* choice' *)
   (choice
    (nonind Type@{i} λ Ix ↦ ind nil) (* inf_ind' *)
    (ind nil)). (* ind' *)

(* Note that Code@{i} is in Type@{i+1}. *)
Definition Code_ : Type@{i'} := El Code_code.
Definition nil_ : Code_ := intro Code_code (nil' []).
Definition nonind_ (A : Type@{i}) (B : A → Code_) : Code_ :=
  intro Code_code (nonind' [A; B]).
Definition inf_ind_ (Ix : Type@{i}) (B : Code_) : Code_ :=
  intro Code_code (inf_ind' [Ix; B]).
Definition ind_ (B : Code_) : Code_ :=
  intro Code_code (ind' [B]).
Definition choice_ (A B : Code_) : Code_ :=
  intro Code_code (choice' [A; B]).

Section code_rect.
Universe j.
Context
  (P : Code_ → Type@{j})
  (IS_nil : P nil_)
  (IS_nonind : ∀ A B, (∀ a, P (B a)) → P (nonind_ A B))
  (IS_inf_ind : ∀ A B, P B → P (inf_ind_ A B))
  (IS_ind : ∀ B, P B → P (ind_ B))
  (IS_choice : ∀ A B, P A → P B → P (choice_ A B))
.

Definition IS arg : liftP@{i' i' j} Code_code P arg → P (intro Code_code arg) :=
  match arg with
  | nil' [] => λ '[] ↦ IS_nil
  | nonind' [A; B] => λ '[IH] ↦ IS_nonind A B IH
  | inf_ind' [A; B] => λ '[IH] ↦ IS_inf_ind A B IH
  | ind' [B] => λ '[IH] ↦ IS_ind B IH
  | choice' [A; B] => λ '[IHA; IHB] ↦ IS_choice A B IHA IHB
  end.
Definition Code_rect : ∀ A, P A := rec Code_code P IS.

(* Check that the expected equations hold by rec_eq = refl *)
Definition test_eq_nil := convertible
  (rec_eq Code_code P IS (nil' []))
  (convertible (Code_rect nil_) IS_nil).
Definition test_eq_nonind A B := convertible
  (rec_eq Code_code P IS (nonind' [A; B]))
  (convertible
   (Code_rect (nonind_ A B))
   (IS_nonind A B (Code_rect ∘ B))).
Definition test_eq_inf_ind A B := convertible
  (rec_eq Code_code P IS (inf_ind' [A; B]))
  (convertible (Code_rect (inf_ind_ A B)) (IS_inf_ind A B (Code_rect B))).
Definition test_eq_ind B := convertible
  (rec_eq Code_code P IS (ind' [B]))
  (convertible (Code_rect (ind_ B)) (IS_ind B (Code_rect B))).
Definition test_eq_choice A B := convertible
  (rec_eq Code_code P IS (choice' [A; B]))
  (convertible
   (Code_rect (choice_ A B))
   (IS_choice A B (Code_rect A) (Code_rect B))).
End code_rect.
End test_code.

Module bootstrap.
(* Code_ doesn't depend on any inductive except W *)
Definition sum_rect@{i j} {A B : Type@{i}} {P : sum@{i} A B → Type@{j}}
  (f : ∀ a, P (inl a)) (g : ∀ b, P (inr b)) s : P s :=
  match s with
  | inl a => f a
  | inr b => g b
  end.
Definition test_Code_eq@{i i' +} := convertible Code_@{i i'}
  (let shapes := (1 ⊔ Type@{i} × 1 ⊔ 1) ⊔ Type@{i} × 1 ⊔ 1 in
   let positions : shapes → Type@{i'} :=
     sum_rect
     (sum_rect
      (λ _ ↦ 0) (* nil *)
      (sum_rect
       (λ (args : Type@{i} × 1) ↦ args.(fst) ⊔ 0) (* nonind *)
       (λ _ ↦ 1 ⊔ (1 ⊔ 0)))) (* choice *)
     (sum_rect
      (λ _ ↦ 1 ⊔ 0) (* inf_ind *)
      (λ _ ↦ 1 ⊔ 0)) in
   let preCode := W shapes positions in
   let _ := convertible preCode (preEl Code_code) in
   Σ (pre_code : (W@{i'} shapes positions)), (* ind *)
   let fix canonical x : Type@{i'} := match x with
     | sup a f =>
       (sum_rect (P := λ a ↦ (positions a → Type@{i'}) → Type@{i'})
        (sum_rect (P := λ a ↦ (positions (inl a) → Type@{i'}) → Type@{i'})
         (λ _ _ ↦ 1)
         (sum_rect (P := λ a ↦ (positions (inl (inr a)) → Type@{i'}) → Type@{i'})
          (λ args canon ↦ (∀ i, canon (inl i)) × 1)
          (λ args canon ↦ canon None × canon (Some None) × 1)))
        (sum_rect (P := λ a ↦ (positions (inr a) → Type@{i'}) → Type@{i'})
         (λ args canon ↦ canon None × 1)
         (λ args canon ↦ canon None × 1))
        a (canonical ∘ f)) ×
       Σ (t :
          (1 ⊔ (* nil *)
           (Σ (A : Type@{i}), (A → preCode) × 1) ⊔ (* nonind *)
           (preCode × preCode × 1) (* choice *)) ⊔
           (Type@{i} × preCode × 1) (* inf_ind *) ⊔
           (preCode × 1) (* ind *)),
         let get_shape : _ → shapes :=
           sum_rect (P := λ _ ↦ shapes)
           (λ t ↦ inl (sum_rect (P := λ _ ↦ 1 ⊔ Type@{i} × 1 ⊔ 1)
            (λ args ↦ inl args) (* nil *)
            (λ t ↦ inr (sum_rect (P := λ _ ↦ Type@{i} × 1 ⊔ 1)
             (λ (args : _ × _ × 1) ↦ inl (args.(fst); args.(snd).(snd))) (* nonind *)
             (λ (args : _ × _ × 1) ↦ inr args.(snd).(snd)) (* choice *)
             t))
            t))
           (λ t ↦ inr (sum_rect (P := λ _ ↦ Type@{i} × 1 ⊔ 1)
            (λ args : _ × _ × 1 ↦ inl (args.(fst); args.(snd).(snd))) (* inf_ind *)
            (λ args ↦ inr args.(snd)) (* ind *)
            t)) in
         let a' : shapes := get_shape t in
         let f' : positions a' → preCode :=
           sum_rect (P := λ t ↦ positions (get_shape t) → preCode)
           (sum_rect (P := λ t ↦ positions (get_shape (inl t)) → preCode)
            (λ _ (XX : 0) ↦ match XX with end) (* nil *)
            (sum_rect (P := λ t ↦ positions (get_shape (inl (inr t))) → preCode)
             (λ args ↦ sum_rect  (* nonind *)
              (args.(snd).(fst))
              (λ XX : 0 ↦ match XX with end))
             (λ args ↦ sum_rect (* choice *)
              (λ '★ ↦ args.(fst))
              (sum_rect
               (λ '★ ↦ args.(snd).(fst))
               (λ XX : 0 ↦ match XX with end)))))
           (sum_rect (P := λ t ↦ positions (get_shape (inr t)) → preCode)
            (λ args ↦ sum_rect (* inf_ind *)
             (λ '★ ↦ args.(snd).(fst))
             (λ XX : 0 ↦ match XX with end))
            (λ args ↦ sum_rect (* ind *)
             (λ '★ ↦ args.(fst))
             (λ XX : 0 ↦ match XX with end)))
           t in
         Id (a'; f') (a; f)
     end in
   canonical pre_code).
(*
Code_rect also doesn't depend on Code when normalized, thus we can
go back to the top of General.v and bootstrap using the normalized definitions.

After doing so, we have Code@{i} = El Code_code, with Code_code : Code@{i+1}.
*)
End bootstrap.
End test_code.
