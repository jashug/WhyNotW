(* Author: Jasper Hugunin *)

Set Universe Polymorphism.
Set Primitive Projections.

(*
We define Id to land in Type, prod to have strict eta,
and W since it isn't in the prelude.
*)
Inductive Id@{i} (A : Type@{i}) (x : A) : A -> Type@{i} := refl : Id A x x.
Arguments Id {A} x y.
Arguments refl {A} x, {A x}.

Definition cong@{i j} {A : Type@{i}} {B : Type@{j}} (f : A -> B) {x y : A}
  (e : Id x y) : Id (f x) (f y) :=
  match e with refl => refl end.
Definition v_trans@{i} {A : Type@{i}} {x y z : A}
  (e1 : Id y x) (e2 : Id y z) : Id x z :=
  match e1 with refl => e2 end.

Record prod@{i} (A : Type@{i}) (B : A -> Type@{i}) : Type@{i} :=
  pair { fst : A ; snd : B fst }.
Arguments pair {A B} & fst snd.
Arguments fst {A B} _.
Arguments snd {A B} _.

Inductive W@{i} (A : Type@{i}) (B : A -> Type@{i}) : Type@{i} :=
  | sup (a : A) (f : B a -> W A B) : W A B.
Arguments sup {A B} a f.

(* composition of functions *)
Notation "f ∘ g" := (fun x => f (g x))
  (at level 40, left associativity) : core_scope.
(* Type of dependent pairs *)
Notation "'Σ' x .. y , p" := (prod _ (fun x => .. (prod _ (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'Σ'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.
Notation "( x ; .. ; y ; z )" := (pair x .. (pair y z) ..) : core_scope.
(* Type of non-dependent pairs *)
Notation "A × B" := (prod A (fun _ => B))
  (at level 40, left associativity) : type_scope.

Section universe_of_datatypes.
Universe i. (* Size of data in our datatypes *)

(*
We adapt Dybjer-Setzer IR codes to the simple inductive case.
Deviating from the paper, we split infinitary and non-infinitary inductive
arguments to compensate for the lack of strict eta for unit
(without which we don't have (unit -> X) equivalent to X).

Another option would be to take a whole telescope, which would be more uniform
and perhaps more friendly to users.
Since we have strict eta for pairs, that is however overkill,
and for expository purposes the following universe should be just right.
*)
Inductive Code :=
  | nil
  | nonind (A : Type@{i}) (B : A -> Code)
  | inf_ind (Ix : Type@{i}) (B : Code)
  | ind (B : Code) (* morally ind B = inf_ind unit B *)
.
(* Note that Code@{i} has itself a code in Code@{j | i <= j}:
Code@{i} : Code@{j | i <= j} :=
  nonind ("nil" + "nonind" (A : Type@{i}) +
          "inf_ind" (Ix : Type@{i}) + "ind") (fun label =>
    match label with
    | "nil" => nil
    | "nonind" A => inf_ind A nil
    | "inf_ind" Ix => ind nil
    | "ind" => ind nil
    end)
*)

(* These codes describe functors: *)
Fixpoint F@{j | i <= j} (A : Code) : Type@{j} -> Type@{j} :=
  match A with
  | nil => fun _ => unit
  | nonind A B => fun X => Σ (a : A), F (B a) X
  | inf_ind Ix B => fun X => (Ix -> X) × F B X
  | ind B => fun X => X × F B X
  end.

Fixpoint Fmap@{j1 j2}
  (A : Code) {X : Type@{j1}} {Y : Type@{j2}} (f : X -> Y)
  : F@{j1} A X -> F@{j2} A Y :=
  match A with
  | nil => fun x => x
  | nonind A B => fun x => (x.(fst); Fmap (B x.(fst)) f x.(snd))
  | inf_ind Ix B => fun x => (f ∘ x.(fst); Fmap B f x.(snd))
  | ind B => fun x => (f x.(fst); Fmap B f x.(snd))
  end.

(* Checking lawfulness is left to the reader *)

(* We next define the standard construction in W types. *)

Fixpoint shapes (A : Code) : Type@{i} :=
  match A with
  | nil => unit
  | nonind A B => Σ (a : A), shapes (B a)
  | inf_ind Ix B => shapes B
  | ind B => shapes B
  end.

Fixpoint positions (A : Code) : shapes A -> Type@{i} :=
  match A with
  | nil => fun _ => False
  | nonind A B => fun x => positions (B x.(fst)) x.(snd)
  | inf_ind Ix B => fun x => sum Ix (positions B x)
  | ind B => fun x => option (positions B x)
  end.

Fixpoint get_shape@{j} {A : Code} {X : Type@{j}} : F@{j} A X -> shapes A :=
  match A return F A X -> shapes A with
  | nil => fun x => x
  | nonind A B => fun x => (x.(fst); get_shape x.(snd))
  | inf_ind Ix B => fun x => get_shape x.(snd)
  | ind B => fun x => get_shape x.(snd)
  end.

Fixpoint get_f@{j} {A : Code} {X : Type@{j}} :
  forall x : F@{j} A X, positions A (get_shape x) -> X :=
  match A with
  | nil => fun _ xx => match xx with end
  | nonind A B => fun x => get_f x.(snd)
  | inf_ind Ix B => fun x p => match p with
    | inl i => x.(fst) i
    | inr p => get_f x.(snd) p
    end
  | ind B => fun x p => match p with
    | None => x.(fst)
    | Some p => get_f x.(snd) p
    end
  end.

Definition get_W_arg@{j} {A : Code} {X : Type@{j}} (x : F@{j} A X) :
  Σ (s : shapes A), (positions A s -> X) :=
  (get_shape x; get_f x).

(* These functors induce a refined notion of forall p : positions A s, P p *)
Fixpoint All@{j} (A : Code) :
  forall {s : shapes A} (P : positions A s -> Type@{j}), Type@{j} :=
  match A with
  | nil => fun _ _ => unit
  | nonind A B => fun s P => All (B s.(fst)) P
  | inf_ind Ix B => fun s P => (forall i, P (inl i)) × All B (P ∘ inr)
  | ind B => fun s P => P None × All B (P ∘ Some)
  end.

Fixpoint All_in@{j} (A : Code) :
  forall {s : shapes A} {P : positions A s -> Type@{j}},
  (forall p : positions A s, P p) -> All@{j} A P :=
  match A with
  | nil => fun s _ _ => s
  | nonind A B => fun s P f => All_in (B s.(fst)) f
  | inf_ind Ix B => fun s P f => (f ∘ inl; All_in B (f ∘ inr))
  | ind B => fun s P f => (f None; All_in B (f ∘ Some))
  end.

(* We can lift predicates over these functors: *)
Definition liftP@{j k} (A : Code) {X : Type@{j}} (P : X -> Type@{k})
  (x : F@{j} A X) : Type@{k} :=
  All@{k} A (P ∘ get_f x).

Definition preEl (A : Code) : Type@{i} := W (shapes A) (positions A).

(*
Then we define the canonical predicate.
A term is canonical if its subterms are canonical
and (s; f) is in the image of get_W_arg.
*)
Fixpoint canonical@{} (A : Code) (x : preEl A) : Type@{i} :=
  match x with
  | sup s f =>
    All A (canonical A ∘ f) ×
    Σ (t : F A (preEl A)), Id (get_W_arg t) (s; f)
  end.

Definition El (A : Code) : Type@{i} := Σ (x : preEl A), canonical A x.

Section split.
(*
We prove an equivalence between F A (Σ (x : X), C x) and
Σ (fx : F A X), All A (C ∘ get_f x)
*)
Context
  {X : Type@{i}}
  {C : X -> Type@{i}}
.

Fixpoint get_heredity {A : Code} :
  forall (x : F A (Σ (x : X), C x)),
  let x_fst := Fmap A fst x in
  All A (s := get_shape x_fst) (C ∘ get_f x_fst) :=
  match A with
  | nil => fun x => x
  | nonind A B => fun x => get_heredity x.(snd)
  | inf_ind Ix B => fun x => (snd ∘ x.(fst); get_heredity x.(snd))
  | ind B => fun x => (snd x.(fst); get_heredity x.(snd))
  end.

(* The pair (Fmap fst, get_heredity) is right-invertible *)
(*
split_view A x hered is equivalent to
Σ (xc : F A (Σ x, C)), Id (Fmap A fst xc; get_hereditary xc) (x; hered)
*)
Inductive split_view (A : Code) :
  forall (x : F A X), All A (C ∘ get_f x) -> Type@{i} :=
  | split_view_refl (x : F A (Σ (x : X), C x)) :
    split_view A (Fmap A fst x) (get_heredity x)
.
Definition split_view_cover_nonind A B x hered :
  split_view (B x.(fst)) x.(snd) hered -> split_view (nonind A B) x hered :=
  fun cover => match cover in split_view _ x_snd hered
  return split_view (nonind A B) (x.(fst); x_snd) hered
  with split_view_refl _ xc =>
    split_view_refl (nonind A B) (x.(fst); xc)
  end.
Definition split_view_cover_inf_ind Ix B x hered :
  split_view B x.(snd) hered.(snd) -> split_view (inf_ind Ix B) x hered :=
  fun cover => match cover in split_view _ x_snd hered_snd
  return split_view (inf_ind Ix B) (x.(fst); x_snd) (hered.(fst); hered_snd)
  with split_view_refl _ xc =>
    split_view_refl (inf_ind Ix B) (fun i => (x.(fst) i; hered.(fst) i); xc)
  end.
Definition split_view_cover_ind B x hered :
  split_view B x.(snd) hered.(snd) -> split_view (ind B) x hered :=
  fun cover => match cover in split_view _ x_snd hered_snd
  return split_view (ind B) (x.(fst); x_snd) (hered.(fst); hered_snd)
  with split_view_refl _ xc =>
    split_view_refl (ind B) ((x.(fst); hered.(fst)); xc)
  end.
Fixpoint split_view_cover (A : Code) :
  forall x hered, split_view A x hered :=
  match A return forall x hered, split_view A x hered with
  | nil => fun 'tt 'tt => split_view_refl nil tt
  | nonind A B => fun x hered =>
    split_view_cover_nonind A B _ _ (split_view_cover (B x.(fst)) x.(snd) hered)
  | inf_ind Ix B => fun x hered =>
    split_view_cover_inf_ind Ix B _ _ (split_view_cover B x.(snd) hered.(snd))
  | ind B => fun x hered =>
    split_view_cover_ind B _ _ (split_view_cover B x.(snd) hered.(snd))
  end.
(* And the fibers are in fact contractible *)
Fixpoint split_view_isContr A :
  forall x hered other, Id other (split_view_cover A x hered) :=
  match A return forall x hered other, Id other (split_view_cover A x hered) with
  | nil => fun x hered '(split_view_refl _ tt) => refl
  | nonind A B => fun x hered '(split_view_refl _ xc) =>
    cong (split_view_cover_nonind A B (Fmap _ fst xc) (get_heredity xc))
    (split_view_isContr _ _ _ (split_view_refl _ xc.(snd)))
  | inf_ind Ix B => fun x hered '(split_view_refl _ xc) =>
    cong (split_view_cover_inf_ind Ix B (Fmap _ fst xc) (get_heredity xc))
    (split_view_isContr _ _ _ (split_view_refl _ xc.(snd)))
  | ind B => fun x hered '(split_view_refl _ xc) =>
    cong (split_view_cover_ind B (Fmap _ fst xc) (get_heredity xc))
    (split_view_isContr _ _ _ (split_view_refl _ xc.(snd)))
  end.
End split.

Definition intro (A : Code) : F@{i} A (El A) -> El A :=
  fun x => let pre_x := Fmap A fst x in
  (sup (get_shape pre_x) (get_f pre_x); get_heredity x; pre_x; refl).

(* Now for induction *)

Section induction.
Universe j.
Context
  (A : Code)
  (P : El A -> Type@{j})
  (IS : forall (x : F A (El A)), liftP@{i j} A P x -> P (intro A x))
.

Fixpoint build_IH@{} (A' : Code) :
  forall x (IH : forall p c, P (get_f (Fmap A' fst x) p; c)),
  All@{j} A' (P ∘ get_f x) :=
  match A' with
  | nil => fun x IH => x
  | nonind A B => fun x IH => build_IH (B x.(fst)) x.(snd) IH
  | inf_ind Ix B => fun x IH =>
    (fun i => IH (inl i) (x.(fst) i).(snd); build_IH B x.(snd) (IH ∘ inr))
  | ind B => fun x IH =>
    (IH None x.(fst).(snd); build_IH B x.(snd) (IH ∘ Some))
  end.

Fixpoint build_IH_eq@{} (A' : Code) (el : forall x, P x) :
  forall x,
  Id (build_IH A' x (fun p c => el _)) (All_in A' (fun p => el _)) :=
  match A' with
  | nil => fun x => refl
  | nonind A B => fun x => build_IH_eq (B x.(fst)) el x.(snd)
  | inf_ind Ix B => fun x =>
    cong (pair (el ∘ x.(fst))) (build_IH_eq B el x.(snd))
  | ind B => fun x =>
    cong (pair (el x.(fst))) (build_IH_eq B el x.(snd))
  end.

Definition rec_helper@{} t (hered : All A (canonical A ∘ _))
  (IH : forall p c, P (get_f t p; c)) :
  split_view A t hered -> P (sup _ _; hered; t; refl) :=
  fun cover => match cover with split_view_refl _ x => fun IH =>
    IS x (build_IH A x IH)
  end IH.
Definition rec@{} : forall x, P x :=
  let fix rec (x : preEl A) : forall c, P (x; c) := match x with
    | sup s f => fun '((hered; t; eq) : canonical A (sup s f)) =>
      match eq as eq in Id _ (s; f)
      return
        forall hered : All A (canonical A ∘ f),
        (forall p c, P (f p; c)) ->
        P (sup s f; hered; t; eq)
      with refl => fun hered IH =>
        rec_helper t hered IH (split_view_cover A t hered)
      end hered (fun p => rec (f p))
    end in
  fun x => rec x.(fst) x.(snd).

Definition rec_eq@{} x
  : Id (rec (intro A x)) (IS x (All_in A (rec ∘ get_f x))) :=
  v_trans
  (cong (rec_helper _ _ (fun p c => rec _))
   (split_view_isContr A _ _ (split_view_refl A x)))
  (cong (IS x) (build_IH_eq A rec x)).

End induction.
End universe_of_datatypes.

Section test_nat.
Notation OO := false.
Notation SS := true.
Definition nat_code : Code@{Set} :=
  nonind bool (fun b => if b then ind nil else nil).
Definition nat' := El nat_code.
Definition O' := intro nat_code (OO; tt).
Definition S' n := intro nat_code (SS; n; tt).
Section nat_ind.
Universe j.
Context
  (P : nat' -> Type@{j})
  (ISO : P O')
  (ISS : forall n, P n -> P (S' n))
.
Definition IS arg : liftP nat_code P arg -> P (intro nat_code arg) :=
  match arg.(fst) as arg_fst
  return
    forall arg_snd, let arg := (arg_fst; arg_snd) in
    liftP nat_code P arg -> P (intro nat_code arg)
  with
  | OO => fun 'tt _ => ISO
  | SS => fun '(n; tt) '(IH; _) => ISS n IH
  end arg.(snd).
Definition nat_rec :=
  rec nat_code P IS.
Notation convertible x y := (refl : Id x y).

(* Check that the expected equations hold *)
Check (convertible (nat_rec O') ISO).
Check (fun n => convertible (nat_rec (S' n)) (ISS n (nat_rec n))).

(* Check that rec_eq simplifies to refl *)
Check (convertible
  (rec_eq nat_code P IS (OO; tt))
  (convertible (nat_rec O') ISO)).
Check (fun n => convertible
  (rec_eq nat_code P IS (SS; n; tt))
  (convertible (nat_rec (S' n)) (ISS n (nat_rec n)))).

End nat_ind.
End test_nat.