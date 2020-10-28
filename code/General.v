(* Author: Jasper Hugunin *)

From WhyNotW Require Import Prelude.

Section universe_of_datatypes.
Universe i. (* Size of data in our datatypes *)

(*
We adapt Dybjer-Setzer IR codes to the simple inductive case.
Deviating from the paper, we split infinitary and non-infinitary inductive
arguments to compensate for the lack of strict eta for unit
(without which we don't have (unit → X) equivalent to X).

We include the choice constructor to avoid getting stuck trying to recurse
under pattern matching on constructor labels.

Another option would be to take a whole telescope, which would be more uniform
and perhaps more friendly to users.
Since we have strict eta for pairs, that is however overkill,
and for expository purposes the following universe should be just right.
*)
Inductive Code :=
  | nil
  | nonind (A : Type@{i}) (B : A → Code)
  | inf_ind (Ix : Type@{i}) (B : Code)
  | ind (B : Code) (* morally ind B = inf_ind 1 B *)
  | choice (A B : Code)
    (* morally choice A B =
       nonind 2 (λ b ↦ match b with false => A | true => B end) *)
.
(* Note that Code@{i} has itself a code in Code@{j | i <= j}:
Code@{i} : Code@{j | i <= j} :=
  nonind ("nil" + "nonind" (A : Type@{i}) +
          "inf_ind" (Ix : Type@{i}) + "ind" + "choice") (fun label =>
    match label with
    | "nil" => nil
    | "nonind" A => inf_ind A nil
    | "inf_ind" Ix => ind nil
    | "ind" => ind nil
    | "choice" => ind (ind nil)
    end)
*)

(* These codes describe functors: *)
Fixpoint F@{j | i <= j} (A : Code) : Type@{j} → Type@{j} :=
  match A with
  | nil => λ X ↦ 1
  | nonind A B => λ X ↦ Σ (a : A), F (B a) X
  | inf_ind Ix B => λ X ↦ (Ix → X) × F B X
  | ind B => λ X ↦ X × F B X
  | choice A B => λ X ↦ F A X ⊔ F B X
  end.

Fixpoint Fmap@{j1 j2}
  (A : Code) {X : Type@{j1}} {Y : Type@{j2}} (f : X → Y)
  : F@{j1} A X → F@{j2} A Y :=
  match A with
  | nil => λ x ↦ x
  | nonind A B => λ x ↦ (x.(fst); Fmap (B x.(fst)) f x.(snd))
  | inf_ind Ix B => λ x ↦ (f ∘ x.(fst); Fmap B f x.(snd))
  | ind B => λ x ↦ (f x.(fst); Fmap B f x.(snd))
  | choice A B => λ x ↦ match x with
    | inl a => inl (Fmap A f a)
    | inr b => inr (Fmap B f b)
    end
  end.

(* Checking lawfulness is left to the reader *)

(* We next define the standard construction in W types. *)

Fixpoint shapes (A : Code) : Type@{i} :=
  match A with
  | nil => 1
  | nonind A B => Σ (a : A), shapes (B a)
  | inf_ind Ix B => shapes B
  | ind B => shapes B
  | choice A B => shapes A ⊔ shapes B
  end.

Fixpoint positions (A : Code) : shapes A → Type@{i} :=
  match A with
  | nil => λ x ↦ 0
  | nonind A B => λ x ↦ positions (B x.(fst)) x.(snd)
  | inf_ind Ix B => λ x ↦ Ix ⊔ positions B x
  | ind B => λ x ↦ 1 ⊔ positions B x
  | choice A B => λ x ↦ match x with
    | inl a => positions A a
    | inr b => positions B b
    end
  end.

Fixpoint get_shape@{j} {A : Code} {X : Type@{j}} : F@{j} A X → shapes A :=
  match A return F A X → shapes A with
  | nil => λ x ↦ x
  | nonind A B => λ x ↦ (x.(fst); get_shape x.(snd))
  | inf_ind Ix B => λ x ↦ get_shape x.(snd)
  | ind B => λ x ↦ get_shape x.(snd)
  | choice A B => λ x ↦ match x with
    | inl a => inl (get_shape a)
    | inr b => inr (get_shape b)
    end
  end.

Fixpoint get_f@{j} {A : Code} {X : Type@{j}} :
  ∀ x : F@{j} A X, positions A (get_shape x) → X :=
  match A with
  | nil => λ _ xx ↦ match xx with end
  | nonind A B => λ x ↦ get_f x.(snd)
  | inf_ind Ix B => λ x p ↦ match p with
    | inl i => x.(fst) i
    | inr p => get_f x.(snd) p
    end
  | ind B => λ x p ↦ match p with
    | None => x.(fst)
    | Some p => get_f x.(snd) p
    end
  | choice A B => λ x ↦ match x with
    | inl a => get_f a
    | inr b => get_f b
    end
  end.

Definition get_W_arg@{j} {A : Code} {X : Type@{j}} (x : F@{j} A X) :
  Σ (s : shapes A), (positions A s → X) :=
  (get_shape x; get_f x).

(* These functors induce a refined notion of forall p : positions A s, P p *)
Fixpoint All@{j} (A : Code) :
  ∀ {s : shapes A} (P : positions A s → Type@{j}), Type@{j} :=
  match A with
  | nil => λ _ _ ↦ 1
  | nonind A B => λ s P ↦ All (B s.(fst)) P
  | inf_ind Ix B => λ s P ↦ (∀ i, P (inl i)) × All B (P ∘ inr')
  | ind B => λ s P ↦ P None × All B (P ∘ Some')
  | choice A B => λ s ↦ match s with
    | inl a => All A (s := a)
    | inr b => All B (s := b)
    end
  end.

Fixpoint All_in@{j} (A : Code) :
  ∀ {s : shapes A} {P : positions A s → Type@{j}}, (∀ p, P p) → All@{j} A P :=
  match A with
  | nil => λ s _ _ ↦ s
  | nonind A B => λ s P f ↦ All_in (B s.(fst)) f
  | inf_ind Ix B => λ s P f ↦ (f ∘ inl'; All_in B (f ∘ inr'))
  | ind B => λ s P f ↦ (f None; All_in B (f ∘ Some'))
  | choice A B => λ s ↦ match s with
    | inl a => λ P f ↦ All_in A (s := a) f
    | inr b => λ P f ↦ All_in B (s := b) f
    end
  end.

(* We can lift predicates over these functors: *)
Definition liftP@{j k} (A : Code) {X : Type@{j}} (P : X → Type@{k})
  (x : F@{j} A X) : Type@{k} :=
  All@{k} A (P ∘ get_f x).

Definition preEl (A : Code) : Type@{i} := W (shapes A) (positions A).

(*
Then we define the canonical predicate.
A term is canonical if its subterms are canonical
and (s; f) is in the image of get_W_arg.
*)
Definition canonical@{} (A : Code) : preEl A → Type@{i} :=
  fix canonical x := match x with
  | sup s f =>
    All A (canonical ∘ f) ×
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
  {C : X → Type@{i}}
.

Fixpoint get_heredity {A : Code} :
  ∀ (x : F A (Σ (x : X), C x)),
  let x_fst := Fmap A fst x in
  All A (s := get_shape x_fst) (C ∘ get_f x_fst) :=
  match A with
  | nil => λ x ↦ x
  | nonind A B => λ x ↦ get_heredity x.(snd)
  | inf_ind Ix B => λ x ↦ (snd ∘ x.(fst); get_heredity x.(snd))
  | ind B => λ x ↦ (snd x.(fst); get_heredity x.(snd))
  | choice A B => λ x ↦ match x with
    | inl a => get_heredity a
    | inr b => get_heredity b
    end
  end.

(* The pair (Fmap fst, get_heredity) is right-invertible *)
(*
split_view A x hered is equivalent to
Σ (xc : F A (Σ x, C)), Id (Fmap A fst xc; get_hereditary xc) (x; hered)
*)
Inductive split_view (A : Code) :
  ∀ (x : F A X), All A (C ∘ get_f x) → Type@{i} :=
  | split_view_refl (x : F A (Σ (x : X), C x)) :
    split_view A (Fmap A fst x) (get_heredity x)
.
Definition split_view_cover_nonind A B x hered :
  split_view (B x.(fst)) x.(snd) hered → split_view (nonind A B) x hered :=
  λ cover ↦ match cover in split_view _ x_snd hered
  return split_view (nonind A B) (x.(fst); x_snd) hered
  with split_view_refl _ xc =>
    split_view_refl (nonind A B) (x.(fst); xc)
  end.
Definition split_view_cover_inf_ind Ix B x hered :
  split_view B x.(snd) hered.(snd) → split_view (inf_ind Ix B) x hered :=
  λ cover ↦ match cover in split_view _ x_snd hered_snd
  return split_view (inf_ind Ix B) (x.(fst); x_snd) (hered.(fst); hered_snd)
  with split_view_refl _ xc =>
    split_view_refl (inf_ind Ix B) (λ i ↦ (x.(fst) i; hered.(fst) i); xc)
  end.
Definition split_view_cover_ind B x hered :
  split_view B x.(snd) hered.(snd) → split_view (ind B) x hered :=
  λ cover ↦ match cover in split_view _ x_snd hered_snd
  return split_view (ind B) (x.(fst); x_snd) (hered.(fst); hered_snd)
  with split_view_refl _ xc =>
    split_view_refl (ind B) ((x.(fst); hered.(fst)); xc)
  end.
Definition split_view_cover_choice_l A B a hered :
  split_view A a hered → split_view (choice A B) (inl a) hered :=
  λ cover ↦ match cover with split_view_refl _ xc =>
    split_view_refl (choice A B) (inl xc)
  end.
Definition split_view_cover_choice_r A B b hered :
  split_view B b hered → split_view (choice A B) (inr b) hered :=
  λ cover ↦ match cover with split_view_refl _ xc =>
    split_view_refl (choice A B) (inr xc)
  end.
Fixpoint split_view_cover (A : Code) :
  ∀ x hered, split_view A x hered :=
  match A with
  | nil => λ 'tt 'tt ↦ split_view_refl nil tt
  | nonind A B => λ x hered ↦
    split_view_cover_nonind A B _ _ (split_view_cover (B x.(fst)) x.(snd) hered)
  | inf_ind Ix B => λ x hered ↦
    split_view_cover_inf_ind Ix B _ _ (split_view_cover B x.(snd) hered.(snd))
  | ind B => λ x hered ↦
    split_view_cover_ind B _ _ (split_view_cover B x.(snd) hered.(snd))
  | choice A B => λ x ↦ match x with
    | inl a => λ hered ↦
      split_view_cover_choice_l A B _ _ (split_view_cover A a hered)
    | inr b => λ hered ↦
      split_view_cover_choice_r A B _ _ (split_view_cover B b hered)
    end
  end.
(* And the fibers are in fact contractible *)
Fixpoint split_view_isContr A :
  ∀ x hered other, Id other (split_view_cover A x hered) :=
  match A with
  | nil => λ x hered '(split_view_refl _ tt) ↦ refl
  | nonind A B => λ x hered '(split_view_refl _ xc) ↦
    cong (split_view_cover_nonind A B (Fmap _ fst xc) (get_heredity xc))
    (split_view_isContr _ _ _ (split_view_refl _ xc.(snd)))
  | inf_ind Ix B => λ x hered '(split_view_refl _ xc) ↦
    cong (split_view_cover_inf_ind Ix B (Fmap _ fst xc) (get_heredity xc))
    (split_view_isContr _ _ _ (split_view_refl _ xc.(snd)))
  | ind B => λ x hered '(split_view_refl _ xc) ↦
    cong (split_view_cover_ind B (Fmap _ fst xc) (get_heredity xc))
    (split_view_isContr _ _ _ (split_view_refl _ xc.(snd)))
  | choice A B => λ x  hered '(split_view_refl _ xc) ↦ match xc with
    | inl a =>
      cong (split_view_cover_choice_l A B (Fmap _ fst a) (get_heredity a))
      (split_view_isContr _ _ _ (split_view_refl _ a))
    | inr b =>
      cong (split_view_cover_choice_r A B (Fmap _ fst b) (get_heredity b))
      (split_view_isContr _ _ _ (split_view_refl _ b))
    end
  end.
End split.

Definition intro (A : Code) : F@{i} A (El A) → El A :=
  λ x ↦ let pre_x := Fmap A fst x in
  (sup (get_shape pre_x) (get_f pre_x); get_heredity x; pre_x; refl).

(* Now for induction *)

Section induction.
Universe j.
Context
  (A : Code)
  (P : El A → Type@{j})
  (IS : ∀ (x : F A (El A)), liftP@{i j} A P x → P (intro A x))
.

Fixpoint build_IH@{} (A' : Code) :
  ∀ x (IH : ∀ p c, P (get_f (Fmap@{i i} A' fst x) p; c)),
  All@{j} A' (P ∘ get_f x) :=
  match A' with
  | nil => λ x IH ↦ x
  | nonind A B => λ x IH ↦ build_IH (B x.(fst)) x.(snd) IH
  | inf_ind Ix B => λ x IH ↦
    (λ i ↦ IH (inl i) (x.(fst) i).(snd); build_IH B x.(snd) (IH ∘ inr'))
  | ind B => λ x IH ↦
    (IH None x.(fst).(snd); build_IH B x.(snd) (IH ∘ Some'))
  | choice A B => λ x ↦ match x with
    | inl a => build_IH A a
    | inr b => build_IH B b
    end
  end.

Fixpoint build_IH_eq@{} (A' : Code) (el : ∀ x, P x) :
  ∀ x,
  Id (build_IH A' x (λ p c ↦ el _)) (All_in A' (λ p ↦ el _)) :=
  match A' with
  | nil => λ x ↦ refl
  | nonind A B => λ x ↦ build_IH_eq (B x.(fst)) el x.(snd)
  | inf_ind Ix B => λ x ↦
    cong (pair (el ∘ x.(fst))) (build_IH_eq B el x.(snd))
  | ind B => λ x ↦
    cong (pair (el x.(fst))) (build_IH_eq B el x.(snd))
  | choice A B => λ x ↦ match x with
    | inl a => build_IH_eq A el a
    | inr b => build_IH_eq B el b
    end
  end.

Definition rec_helper@{} t (hered : All A (canonical A ∘ _))
  (IH : ∀ p c, P (get_f t p; c)) :
  split_view A t hered → P (sup _ _; hered; t; refl) :=
  fun cover => match cover with split_view_refl _ x => λ IH ↦
    IS x (build_IH A x IH)
  end IH.
Definition rec@{} : ∀ x, P x :=
  let fix rec (x : preEl A) : ∀ c, P (x; c) := match x with
    | sup s f => λ '((hered; t; eq) : canonical A (sup s f)) ↦
      match eq in Id _ (s; f)
      return
        ∀ hered : All A (canonical A ∘ f),
        (∀ p c, P (f p; c)) →
        P (sup s f; hered; t; eq)
      with refl => λ hered IH ↦
        rec_helper t hered IH (split_view_cover A t hered)
      end hered (λ p ↦ rec (f p))
    end in
  λ x ↦ rec x.(fst) x.(snd).

Definition rec_eq@{} x
  : Id (rec (intro A x)) (IS x (All_in A (rec ∘ get_f x))) :=
  v_trans
  (cong (rec_helper _ _ (λ p c ↦ rec _))
   (split_view_isContr A _ _ (split_view_refl A x)))
  (cong (IS x) (build_IH_eq A rec x)).

End induction.
End universe_of_datatypes.