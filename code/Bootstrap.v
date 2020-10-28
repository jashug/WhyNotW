(* Author: Jasper Hugunin *)

From WhyNotW Require Import Prelude.

(* Everything defined in terms of the primitive type formers only. *)

#[universes(monomorphic)] Universe UTop. (* For the elimination predicate. *)

Section universe_of_datatypes.
Universe i.
Universe i'. (* morally i+1 *)
Constraint i < i'.

Section define_Code.
(* We first have to manually perform the computation of El Code_code *)
Local Notation "#sum_match s 'as' s' 'return' P 'with' f | g 'end'" :=
  (match s.(fst) as s_fst
   return ∀ s_snd, let s' : _ + _ := (s_fst; s_snd) in P
   with false => f | true => g end s.(snd)).
Local Notation "#sum_rect [ s 'return' P ]" :=
  (λ (f : ∀ a, let s : _ + _ := inl a in P)
     (g : ∀ b, let s : _ + _ := inr b in P) ↦
   λ x ↦ #sum_match x as s return P with f | g end).
Local Notation sum_rect := (#sum_rect[_ return _]).
Definition Ux1 := prod@{i'} Type@{i} λ _ ↦ 1. (* Fix universe level *)
Definition Code_shapes@{|} : Type@{i'} := (1 ⊔ Ux1 ⊔ 1) ⊔ Ux1 ⊔ 1.
Definition Code_positions@{|} : Code_shapes → Type@{i'} :=
  #sum_rect [s return Type@{i'}]
  (#sum_rect [s return Type@{i'}]
   (λ _ ↦ 0) (* nil *)
   (#sum_rect [s return Type@{i'}]
    (λ (args : Ux1) ↦ sum'@{i'} args.(fst) 0) (* nonind *)
    (λ _ ↦ sum'@{i'} 1 (sum'@{i'} 1 0)))) (* choice *)
  (#sum_rect [s return Type@{i'}]
   (λ _ ↦ sum'@{i'} 1 0) (* inf_ind *)
   (λ _ ↦ sum'@{i'} 1 0)).
Definition preCode@{|} : Type@{i'} := W Code_shapes Code_positions.
Definition Code_All@{j | i <= j} {s : Code_shapes}
  (C : Code_positions s → Type@{j}) : Type@{j} :=
  let positions := Code_positions in
  (#sum_rect [a return (positions a → Type@{j}) → Type@{j}]
   (#sum_rect [a return (positions (inl a) → Type@{j}) → Type@{j}]
    (λ _ _ ↦ 1)
    (#sum_rect [a return (positions (inl (inr a)) → Type@{j}) → Type@{j}]
     (λ args C ↦ (∀ i, C (inl i)) × 1)
     (λ args C ↦ C None × C (Some None) × 1)))
   (#sum_rect [a return (positions (inr a) → Type@{j}) → Type@{j}]
    (λ args C ↦ C None × 1)
    (λ args C ↦ C None × 1))
   s C).
Definition Code_F@{j | i < j} (X : Type@{j}) : Type@{j} :=
  (1 ⊔ (* nil *)
   (prod@{j} Type@{i} λ A ↦ (A → X) × 1) ⊔ (* nonind *)
   (X × X × 1)) ⊔ (* choice *)
  (Type@{i} × X × 1) ⊔ (* inf_ind *)
   (X × 1). (* ind *)
Definition Code_Fmap@{j1 j2} {X : Type@{j1}} {Y : Type@{j2}} (f : X → Y) :
  Code_F@{j1} X → Code_F@{j2} Y :=
  #sum_rect [s return Code_F@{j2} Y]
  (inl' ∘ #sum_rect [s return (1 ⊔ (prod@{j2} Type@{i} λ A ↦ (A → Y) × 1) ⊔ (Y × Y × 1))]
   (λ x ↦ inl' x) (* nil *)
   (inr' ∘ #sum_rect [s return (prod@{j2} Type@{i} λ A ↦ (A → Y) × 1) ⊔ (Y × Y × 1)]
    (λ args : prod@{j1} Type@{i} λ A ↦ (A → X) × 1 ↦ (* nonind *)
     inl' (A := prod@{j2} Type@{i} λ A ↦ (A → Y) × 1)
     (args.(fst); f ∘ args.(snd).(fst); args.(snd).(snd)))
    (λ args : X × X × 1 ↦ (* choice *)
     inr' (f args.(fst); f args.(snd).(fst); args.(snd).(snd)))))
  (inr' ∘ #sum_rect [s return (Type@{i} × Y × 1) ⊔ (Y × 1)]
   (λ args : Type@{i} × X × 1 ↦ (* inf_ind *)
    inl'@{j2} (A := Type@{i} × Y × 1)
    (args.(fst); f args.(snd).(fst); args.(snd).(snd)))
   (λ args : X × 1 ↦ inr'@{j2} (f args.(fst); args.(snd)))). (* ind *)
Definition Code_get_shape@{j} {X : Type@{j}} : Code_F@{j} X → Code_shapes :=
  #sum_rect [_ return Code_shapes]
  (λ t ↦ inl'@{i'} (#sum_rect [_ return 1 ⊔ Ux1 ⊔ 1]
   (λ args ↦ inl'@{i'} args) (* nil *)
   (λ t ↦ inr'@{i'} (#sum_rect [_ return Ux1 ⊔ 1]
    (λ (args : prod@{j} Type@{i} λ _ ↦ _ × 1) ↦
     inl'@{i'} (A := Ux1) (args.(fst); args.(snd).(snd))) (* nonind *)
    (λ (args : X × X × 1) ↦ inr'@{i'} args.(snd).(snd)) (* choice *)
    t))
   t))
  (λ t ↦ inr@{i'} (#sum_rect [_ return Ux1 ⊔ 1]
   (λ args : prod@{j} Type@{i} λ _ ↦ prod@{j} _ λ _ ↦ 1 ↦
    inl@{i'} (args.(fst); args.(snd).(snd))) (* inf_ind *)
   (λ args ↦ inr'@{i'} args.(snd)) (* ind *)
   t)).
Definition Code_get_f@{j} {X : Type@{j}} :
  ∀ fx : Code_F@{j} X, Code_positions (Code_get_shape fx) → X :=
  let get_shape := Code_get_shape in
  let positions := Code_positions in
  #sum_rect [t return positions (get_shape t) → X]
  (#sum_rect [t return positions (get_shape (inl t)) → X]
   (λ _ (XX : 0) ↦ match XX with end) (* nil *)
   (#sum_rect [t return positions (get_shape (inl (inr t))) → X]
    (λ args ↦ sum_rect  (* nonind *)
     (args.(snd).(fst))
     (λ XX : 0 ↦ match XX with end))
    (λ args ↦ sum_rect (* choice *)
     (λ '★ ↦ args.(fst))
     (sum_rect
      (λ '★ ↦ args.(snd).(fst))
      (λ XX : 0 ↦ match XX with end)))))
  (#sum_rect [t return positions (get_shape (inr t)) → X]
   (λ args ↦ sum_rect (* inf_ind *)
    (λ '★ ↦ args.(snd).(fst))
    (λ XX : 0 ↦ match XX with end))
   (λ args ↦ sum_rect (* ind *)
    (λ '★ ↦ args.(fst))
    (λ XX : 0 ↦ match XX with end))).
Fixpoint Code_canonical@{} (x : preCode) : Type@{i'} := match x with
  | sup a f => prod@{i'}
    (Code_All (Code_canonical ∘ f)) λ _ ↦
    prod@{i'}
    (Code_F preCode) λ t ↦
    (Id (A := Σ (a : Code_shapes), Code_positions a → preCode)
     (Code_get_shape t; Code_get_f t) (a; f))
  end.

Section split.
Context
  {X : Type@{i'}}
  {C : X → Type@{i'}}
.
Let T := prod@{i'} X C.
Definition Code_get_heredity
  (Hered := λ (x : Code_F T) ↦
   let x_fst := Code_Fmap fst x in
   Code_All (s := Code_get_shape x_fst) (C ∘ Code_get_f x_fst) : Type@{i'}) :
  ∀ x, Hered x :=
  #sum_rect [x return Hered x]
  (#sum_rect [x return Hered (inl x)]
   (λ x ↦ x)
   (#sum_rect [x return Hered (inl (inr x))]
    (λ x : prod@{i'} Type@{i} λ A ↦ (A → T) × 1 ↦
     (snd ∘ x.(snd).(fst); x.(snd).(snd)))
    (λ x : T × T × 1 ↦ (snd x.(fst); snd x.(snd).(fst); x.(snd).(snd)))))
  (#sum_rect [x return Hered (inr x)]
   (λ x : prod@{i'} Type@{i} λ Ix ↦ T × 1 ↦
    (snd x.(snd).(fst); x.(snd).(snd)))
   (λ x : T × 1 ↦ (snd x.(fst); x.(snd)))).

Definition Fiber {A B1 : Type@{i'}} (B2 : B1 → Type@{i'})
  (f : A → B1) (g : ∀ a, B2 (f a)) (b1 : B1) (b2 : B2 b1) : Type@{i'} :=
  Σ (a : A), Id (A := Σ (b1 : B1), B2 b1) (f a; g a) (b1; b2).
Definition Code_split_view
  (x : Code_F X) (hered : Code_All (C ∘ Code_get_f x)) : Type@{i'} :=
  Fiber (λ x ↦ Code_All (C ∘ Code_get_f x))
  (Code_Fmap fst) (Code_get_heredity) x hered.

Section choice.
Context
  {Al Bl Sl : Type@{i'}} {Pl : Sl → Type@{i'}}
  {Alll : ∀ s, (Pl s → Type@{i'}) → Type@{i'}}
  {fl : Al → Bl} {gsl : Bl → Sl} {gfl : ∀ b, Pl (gsl b) → X}
  {gl : ∀ a, Alll (gsl (fl a)) (C ∘ gfl (fl a))}
  {Ar Br Sr : Type@{i'}} {Pr : Sr → Type@{i'}}
  {Allr : ∀ s, (Pr s → Type@{i'}) → Type@{i'}}
  {fr : Ar → Br} {gsr : Br → Sr} {gfr : ∀ b, Pr (gsr b) → X}
  {gr : ∀ a, Allr (gsr (fr a)) (C ∘ gfr (fr a))}
.
Let A : Type@{i'} := Al ⊔ Ar.
Let B : Type@{i'} := Bl ⊔ Br.
Let S : Type@{i'} := Sl ⊔ Sr.
Let P : S → Type@{i'} := sum_rect Pl Pr.
Let All : ∀ s, (P s → Type@{i'}) → Type@{i'} :=
  #sum_rect [s return (P s → Type@{i'}) → Type@{i'}] Alll Allr.
Let f : A → B := sum_rect (inl' ∘ fl) (inr' ∘ fr).
Let gs : B → S := sum_rect (inl' ∘ gsl) (inr' ∘ gsr).
Let gf : ∀ b, P (gs b) → X := #sum_rect [b return P (gs b) → X] gfl gfr.
Let g : ∀ a, All (gs (f a)) (C ∘ gf (f a)) :=
  #sum_rect [a return All (gs (f a)) (C ∘ gf (f a))] gl gr.
Definition Code_split_view_cover_choice_l a hered :
  Fiber (λ x ↦ Alll _ (C ∘ gfl x)) fl gl a hered →
  Fiber (λ x ↦ All _ (C ∘ gf x)) f g (inl a) hered :=
  λ cover ↦ match cover with (xc; e) =>
    match e in Id _ (a; hered) return Fiber _ f g (inl a) hered
    with refl => (inl xc; refl) end
  end.
Definition Code_split_view_cover_choice_r b hered :
  Fiber (λ x ↦ Allr _ (C ∘ gfr x)) fr gr b hered →
  Fiber (λ x ↦ All _ (C ∘ gf x)) f g (inr b) hered :=
  λ cover ↦ match cover with (xc; e) =>
    match e in Id _ (b; hered) return Fiber _ f g (inr b) hered
    with refl => (inr xc; refl) end
  end.
Definition Code_split_view_cover_choice@{|} :
  (∀ a hered, Fiber (λ x ↦ Alll _ (C ∘ gfl x)) fl gl a hered) →
  (∀ b hered, Fiber (λ x ↦ Allr _ (C ∘ gfr x)) fr gr b hered) →
  ∀ x hered, Fiber (λ x ↦ All _ (C ∘ gf x)) f g x hered :=
  λ Hl Hr ↦ #sum_rect [x return ∀ hered, Fiber (λ x ↦ All _ (C ∘ gf x)) f g x hered]
  (λ a hered ↦ Code_split_view_cover_choice_l a hered (Hl a hered))
  (λ b hered ↦ Code_split_view_cover_choice_r b hered (Hr b hered)).
End choice.
Arguments Code_split_view_cover_choice
  {Al Bl Sl Pl Alll fl gsl gfl gl} {Ar Br Sr Pr Allr fr gsr gfr gr} & Hl Hr x hered.
Definition Code_split_view_cover : ∀ x hered, Code_split_view x hered :=
  Code_split_view_cover_choice
  (Code_split_view_cover_choice
   (λ '[] '[] ↦ ([]; refl))
   (Code_split_view_cover_choice
    (λ '[A; B] '[BH] ↦ ([A; λ a ↦ (B a; BH a)]; refl))
    (λ '[A; B] '[AH; BH] ↦ ([(A; AH); (B; BH)]; refl))))
  (Code_split_view_cover_choice
   (λ '[Ix; B] '[BH] ↦ ([Ix; (B; BH)]; refl))
   (λ '[B] '[BH] ↦ ([(B; BH)]; refl))).
End split.

(* This is the true definition of Code. *)
Definition Code@{|} : Type@{i'} := Σ (x : preCode), Code_canonical x.
Definition Code_intro@{|} (x : Code_F Code) : Code :=
  let fst_x := Code_Fmap fst x in
  (sup _ _; Code_get_heredity x; fst_x; refl).

Local Notation nil' x := (inl (inl x)).
Local Notation nonind' x := (inl (inr (inl x))).
Local Notation choice' x := (inl (inr (inr x))).
Local Notation inf_ind' x := (inr (inl x)).
Local Notation ind' x := (inr (inr x)).

Definition nil : Code := Code_intro (nil' []).
Definition nonind (A : Type@{i}) (B : A → Code) : Code :=
  Code_intro (nonind' [A; B]).
Definition inf_ind (Ix : Type@{i}) (B : Code) : Code :=
  Code_intro (inf_ind' [Ix; B]).
Definition ind (B : Code) : Code :=
  Code_intro (ind' [B]).
Definition choice (A B : Code) : Code :=
  Code_intro (choice' [A; B]).

(* Recursion for Code *)
Section Code_rec.
Constraint i <= UTop.
Context
  (P : Code → Type@{UTop})
.
Section general_rec.
Context
  (IS : ∀ (x : Code_F Code), Code_All@{UTop} (P ∘ Code_get_f x) → P (Code_intro x))
.

Section build_IH.
Let Code_All_j {s} := Code_All@{UTop} (s := s).
Local Notation R x :=
  (∀ (IH : ∀ p c, P (Code_get_f (Code_Fmap fst x) p; c)),
   Code_All_j (P ∘ Code_get_f x)).
Definition Code_build_IH@{|} :
  ∀ x, R x :=
  #sum_rect [x return R x]
  (#sum_rect [x return R (inl x)]
   (λ x IH ↦ x) (* nil *)
   (#sum_rect [x return R (inl (inr x))]
    (λ x IH ↦ (* nonind *)
     (λ i ↦ IH (inl i) (x.(snd).(fst) i).(snd); x.(snd).(snd)))
    (λ x IH ↦ (* choice *)
     (IH None x.(fst).(snd); IH (Some None) x.(snd).(fst).(snd);
      x.(snd).(snd)))))
  (#sum_rect [x return R (inr x)]
   (λ x IH ↦ (* inf_ind *)
    (IH None x.(snd).(fst).(snd); x.(snd).(snd)))
   (λ x IH ↦ (* ind *)
    (IH None x.(fst).(snd); x.(snd)))).
End build_IH.

Definition Code_rec_helper@{|} t (hered : Code_All (Code_canonical ∘ _))
  (IH : ∀ p c, P (Code_get_f t p; c)) :
  Code_split_view t hered → P (sup _ _; hered; t; refl) :=
  fun cover => match cover with (x; e) =>
    match e in Id _ (t; hered)
    return (∀ p c, P (Code_get_f t p; c)) → P (sup _ _; hered; t; refl)
    with refl => λ IH ↦
      IS x (Code_build_IH x IH)
    end
  end IH.
Definition Code_rec_gen@{|} : ∀ A, P A :=
  let fix rec x : ∀ c, P (x ; c) := match x with
    | sup s f => λ '((hered; t; eq) : Code_canonical (sup s f)) ↦
      match eq in Id _ (s; f)
      return
        ∀ hered : Code_All@{i'} (Code_canonical ∘ f),
        (∀ p c, P (f p; c)) →
        P (sup s f; hered; t; eq)
      with refl => λ hered IH ↦
        Code_rec_helper t hered IH (Code_split_view_cover t hered)
      end hered (rec ∘ f)
    end in
  λ A ↦ rec A.(fst) A.(snd).
End general_rec.

Context
  (IS_nil : P nil)
  (IS_nonind : ∀ (A : Type@{i}) B, (∀ a, P (B a)) → P (nonind A B))
  (IS_inf_ind : ∀ (Ix : Type@{i}) B, P B → P (inf_ind Ix B))
  (IS_ind : ∀ B, P B → P (ind B))
  (IS_choice : ∀ A B, P A → P B → P (choice A B))
.

Definition IS@{|} (arg : Code_F@{i'} Code) :
  Code_All@{UTop} (P ∘ Code_get_f arg) → P (Code_intro arg) :=
  match arg return Code_All@{UTop} (P ∘ Code_get_f arg) → P (Code_intro arg) with
  | nil' [] => λ '[] ↦ IS_nil
  | nonind' [A; B] => λ '[IH] ↦ IS_nonind A B IH
  | inf_ind' [A; B] => λ '[IH] ↦ IS_inf_ind A B IH
  | ind' [B] => λ '[IH] ↦ IS_ind B IH
  | choice' [A; B] => λ '[IHA; IHB] ↦ IS_choice A B IHA IHB
  end.

Definition Code_rec@{|} := Code_rec_gen IS.
End Code_rec.
Arguments Code_rec P & IS_nil IS_nonind IS_inf_ind IS_ind IS_choice.
End define_Code.

(* ---------------------------------------------------------------- *)
(*
We have now completed the definition of Code from W.
The rest follows General.v, but is *very* slow to typecheck.
*)

Definition F@{j | i <= j, j < UTop} : Code → Type@{j} → Type@{j} :=
  Code_rec (λ A ↦ Type@{j} → Type@{j})
  (λ X ↦ 1)
  (λ A B F_B ↦ λ X ↦ Σ (a : A), (F_B a) X)
  (λ Ix B F_B ↦ λ X ↦ (Ix → X) × F_B X)
  (λ B F_B ↦ λ X ↦ X × F_B X)
  (λ A B F_A F_B ↦ λ X ↦ F_A X ⊔ F_B X).

Definition Fmap@{j1 j2}
  (A : Code) {X : Type@{j1}} {Y : Type@{j2}} (f : X → Y)
  : F@{j1} A X → F@{j2} A Y :=
  Code_rec (λ A ↦ F@{j1} A X → F@{j2} A Y)
  (λ x ↦ x)
  (λ A B Fmap_B ↦ λ x ↦ (x.(fst); (Fmap_B x.(fst)) x.(snd)))
  (λ Ix B Fmap_B ↦ λ x ↦ (f ∘ x.(fst); Fmap_B x.(snd)))
  (λ B Fmap_B ↦ λ x ↦ (f x.(fst); Fmap_B x.(snd)))
  (λ A B Fmap_A Fmap_B ↦ λ x ↦ match x with
    | inl a => inl (Fmap_A a)
    | inr b => inr (Fmap_B b)
    end)
  A.

(* Checking lawfulness is left to the reader *)

(* We next define the standard construction in W types. *)

Definition shapes : Code → Type@{i} :=
  Code_rec (λ A ↦ Type@{i})
  1
  (λ A B shapes_B ↦ Σ (a : A), shapes_B a)
  (λ Ix B shapes_B ↦ shapes_B)
  (λ B shapes_B ↦ shapes_B)
  (λ A B shapes_A shapes_B ↦ shapes_A ⊔ shapes_B).

Definition positions : ∀ A, shapes A → Type@{i} :=
  Code_rec (λ A ↦ shapes A → Type@{i})
  (λ x ↦ 0)
  (λ A B positions_B ↦ λ x ↦ positions_B x.(fst) x.(snd))
  (λ Ix B positions_B ↦ λ x ↦ Ix ⊔ positions_B x)
  (λ B positions_B ↦ λ x ↦ 1 ⊔ positions_B x)
  (λ A B positions_A positions_B ↦ λ x ↦ match x with
    | inl a => positions_A a
    | inr b => positions_B b
    end).

Definition get_shape@{j} {A : Code} {X : Type@{j}} : F@{j} A X → shapes A :=
  Code_rec (λ A ↦ F@{j} A X → shapes A)
  (λ x ↦ x)
  (λ A B get_shape_B ↦ λ x ↦ (x.(fst); get_shape_B _ x.(snd)))
  (λ Ix B get_shape_B ↦ λ x ↦ get_shape_B x.(snd))
  (λ B get_shape_B ↦ λ x ↦ get_shape_B x.(snd))
  (λ A B get_shape_A get_shape_B ↦ λ x ↦ match x with
    | inl a => inl (get_shape_A a)
    | inr b => inr (get_shape_B b)
    end)
  A.

Definition get_f@{j} {A : Code} {X : Type@{j}} :
  ∀ x : F@{j} A X, positions A (get_shape x) → X :=
  Code_rec (λ A ↦ ∀ x : F@{j} A X, positions A (get_shape x) → X)
  (λ _ XX ↦ match XX with end)
  (λ A B get_f_B ↦ λ x ↦ get_f_B _ x.(snd))
  (λ Ix B get_f_B ↦ λ x p ↦ match p with
    | inl i => x.(fst) i
    | inr p => get_f_B x.(snd) p
    end)
  (λ B get_f_B ↦ λ x p ↦ match p with
    | None => x.(fst)
    | Some p => get_f_B x.(snd) p
    end)
  (λ A B get_f_A get_f_B ↦ λ x ↦ match x with
    | inl a => get_f_A a
    | inr b => get_f_B b
    end)
  A.

Definition get_W_arg@{j} {A : Code} {X : Type@{j}} (x : F@{j} A X) :
  Σ (s : shapes A), (positions A s → X) :=
  (get_shape x; get_f x).

(* These functors induce a refined notion of forall p : positions A s, P p *)
Definition All@{j} : ∀ A {s}, (positions A s → Type@{j}) → Type@{j} :=
  Code_rec (λ A ↦ ∀ s, (positions A s → Type@{j}) → Type@{j})
  (λ _ _ ↦ 1)
  (λ A B All_B ↦ λ s P ↦ All_B s.(fst) _ P)
  (λ Ix B All_B ↦ λ s P ↦ (∀ i, P (inl i)) × All_B _ (P ∘ inr'))
  (λ B All_B ↦ λ s P ↦ P None × All_B _ (P ∘ Some'))
  (λ A B All_A All_B ↦ λ s ↦ match s with
    | inl a => All_A a
    | inr b => All_B b
    end).

Definition All_in@{j} :
  ∀ A {s} {P : positions A s → Type@{j}},
  (∀ p, P p) → All@{j} A (s := s) P :=
  Code_rec
  (λ A ↦ ∀ s (P : positions A s → Type@{j}),
   (∀ p, P p) → All@{j} A (s := s) P)
  (λ s _ _ ↦ s)
  (λ A B All_in_B ↦ λ s P f ↦ All_in_B s.(fst) _ _ f)
  (λ Ix B All_in_B ↦ λ s P f ↦ (f ∘ inl'; All_in_B _ _ (f ∘ inr')))
  (λ B All_in_B ↦ λ s P f ↦ (f None; All_in_B _ _ (f ∘ Some')))
  (λ A B All_in_A All_in_B ↦ λ s ↦ match s with
    | inl a => All_in_A a
    | inr b => All_in_B b
    end).

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
Let T : Type@{i} := Σ (x : X), C x.

Definition get_heredity : ∀ {A : Code},
  ∀ (x : F A T),
  let x_fst := Fmap A fst x in
  All A (s := get_shape x_fst) (C ∘ get_f x_fst) :=
  Code_rec
  (λ A ↦ ∀ (x : F A T),
   let x_fst := Fmap A fst x in
   All A (s := get_shape x_fst) (C ∘ get_f x_fst))
  (λ x ↦ x)
  (λ A B get_heredity_B ↦ λ x ↦ get_heredity_B x.(fst) x.(snd))
  (λ Ix B get_heredity_B ↦ λ x ↦ (snd ∘ x.(fst); get_heredity_B x.(snd)))
  (λ B get_heredity_B ↦ λ x ↦ (snd x.(fst); get_heredity_B x.(snd)))
  (λ A B get_heredity_A get_heredity_B ↦ λ x ↦ match x with
    | inl a => get_heredity_A a
    | inr b => get_heredity_B b
    end).

(* The pair (Fmap fst, get_heredity) is right-invertible *)
Definition split_view (A : Code) (x : F A X) (hered : All A (C ∘ get_f x)) :
  Type@{i} :=
  Σ (xc : F A T),
  Id (A := Σ (x : F A X), All A (C ∘ get_f x))
  (Fmap A fst xc; get_heredity xc) (x; hered).
Definition split_view_refl (A : Code) (xc : F A T) :
  split_view A (Fmap A fst xc) (get_heredity xc) :=
  (xc; refl).
Definition split_view_elim@{j} {A} (P : ∀ x hered, split_view A x hered → Type@{j})
  (H : ∀ xc, P (Fmap A fst xc) (get_heredity xc) (split_view_refl A xc)) x hered
  (cover : split_view A x hered) : P x hered cover :=
  match cover.(snd) as e in Id _ (x; hered) return P x hered (cover.(fst); e)
  with refl => H cover.(fst) end.
Definition split_view_cover_nonind A B x hered :
  split_view (B x.(fst)) x.(snd) hered → split_view (nonind A B) x hered :=
  split_view_elim@{i}
  (λ x_snd hered _ ↦ split_view (nonind A B) (x.(fst); x_snd) hered)
  (λ xc ↦ split_view_refl (nonind A B) (x.(fst); xc))
  x.(snd) hered.
Definition split_view_cover_inf_ind Ix B x hered :
  split_view B x.(snd) hered.(snd) → split_view (inf_ind Ix B) x hered :=
  split_view_elim@{i}
  (λ x_snd hered_snd _ ↦
   split_view (inf_ind Ix B) (x.(fst); x_snd) (hered.(fst); hered_snd))
  (λ xc ↦ split_view_refl (inf_ind Ix B) (λ i ↦ (x.(fst) i; hered.(fst) i); xc))
  x.(snd) hered.(snd).
Definition split_view_cover_ind B x hered :
  split_view B x.(snd) hered.(snd) → split_view (ind B) x hered :=
  split_view_elim@{i}
  (λ x_snd hered_snd _ ↦
   split_view (ind B) (x.(fst); x_snd) (hered.(fst); hered_snd))
  (λ xc ↦ split_view_refl (ind B) ((x.(fst); hered.(fst)); xc))
  x.(snd) hered.(snd).
Definition split_view_cover_choice_l A B a hered :
  split_view A a hered → split_view (choice A B) (inl a) hered :=
  split_view_elim@{i}
  (λ a hered _ ↦ split_view (choice A B) (inl a) hered)
  (λ xc ↦ split_view_refl (choice A B) (inl xc))
  a hered.
Definition split_view_cover_choice_r A B b hered :
  split_view B b hered → split_view (choice A B) (inr b) hered :=
  split_view_elim@{i}
  (λ b hered _ ↦ split_view (choice A B) (inr b) hered)
  (λ xc ↦ split_view_refl (choice A B) (inr xc))
  b hered.
Definition split_view_cover : ∀ (A : Code) x hered, split_view A x hered :=
  Code_rec (λ A ↦ ∀ x hered, split_view A x hered)
  (λ '[] '[] ↦ split_view_refl nil [])
  (λ A B split_view_cover_B ↦ λ x hered ↦
   split_view_cover_nonind A B _ _ (split_view_cover_B x.(fst) x.(snd) hered))
  (λ Ix B split_view_cover_B ↦ λ x hered ↦
   split_view_cover_inf_ind Ix B _ _ (split_view_cover_B x.(snd) hered.(snd)))
  (λ B split_view_cover_B ↦ λ x hered ↦
   split_view_cover_ind B _ _ (split_view_cover_B x.(snd) hered.(snd)))
  (λ A B split_view_cover_A split_view_cover_B ↦ λ x ↦ match x with
    | inl a => λ hered ↦
      split_view_cover_choice_l A B _ _ (split_view_cover_A a hered)
    | inr b => λ hered ↦
      split_view_cover_choice_r A B _ _ (split_view_cover_B b hered)
    end).

(* And the fibers are in fact contractible *)
Definition split_view_isContr :
  ∀ A x hered other, Id other (split_view_cover A x hered) :=
  Code_rec (λ A ↦ ∀ x hered other, Id other (split_view_cover A x hered))
  (λ x hered ↦ split_view_elim@{i}
   (λ x hered other ↦ Id other (split_view_cover nil x hered))
   (λ '[] ↦ refl)
   _ _)
  (λ A B split_view_isContr_B ↦ λ x hered ↦ split_view_elim@{i}
   (λ x hered other ↦ Id other (split_view_cover (nonind A B) x hered))
   (λ xc ↦ cong (split_view_cover_nonind A B (Fmap _ fst xc) (get_heredity xc))
    (split_view_isContr_B _ _ _ (split_view_refl _ xc.(snd))))
   _ _)
  (λ Ix B split_view_isContr_B ↦ λ x hered ↦ split_view_elim@{i}
   (λ x hered other ↦ Id other (split_view_cover (inf_ind Ix B) x hered))
   (λ xc ↦ cong (split_view_cover_inf_ind Ix B (Fmap _ fst xc) (get_heredity xc))
    (split_view_isContr_B _ _ (split_view_refl _ xc.(snd))))
   _ _)
  (λ B split_view_isContr_B ↦ λ x hered ↦ split_view_elim@{i}
   (λ x hered other ↦ Id other (split_view_cover (ind B) x hered))
   (λ xc ↦ cong (split_view_cover_ind B (Fmap _ fst xc) (get_heredity xc))
    (split_view_isContr_B _ _ (split_view_refl _ xc.(snd))))
   _ _)
  (λ A B split_view_isContr_A split_view_isContr_B ↦ λ x hered ↦
   split_view_elim@{i}
   (λ x hered other ↦ Id other (split_view_cover (choice A B) x hered))
   (λ xc ↦ match xc with
    | inl a =>
      cong (split_view_cover_choice_l A B (Fmap _ fst a) (get_heredity a))
      (split_view_isContr_A _ _ (split_view_refl _ a))
    | inr b =>
      cong (split_view_cover_choice_r A B (Fmap _ fst b) (get_heredity b))
      (split_view_isContr_B _ _ (split_view_refl _ b))
    end)
   _ _).
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

Definition build_IH@{} :
  ∀ A' x (IH : ∀ p c, P (get_f (Fmap@{i i} A' fst x) p; c)),
  All@{j} A' (P ∘ get_f x) :=
  Code_rec
  (λ A' ↦ ∀ x (IH : ∀ p c, P (get_f (Fmap@{i i} A' fst x) p; c)),
   All@{j} A' (P ∘ get_f x))
  (λ x IH ↦ x)
  (λ A B build_IH_B ↦ λ x IH ↦ build_IH_B x.(fst) x.(snd) IH)
  (λ Ix B build_IH_B ↦ λ x IH ↦
   (λ i ↦ IH (inl i) (x.(fst) i).(snd); build_IH_B x.(snd) (IH ∘ inr')))
  (λ B build_IH_B ↦ λ x IH ↦
   (IH None x.(fst).(snd); build_IH_B x.(snd) (IH ∘ Some')))
  (λ A B build_IH_A build_IH_B ↦ λ x ↦ match x with
    | inl a => build_IH_A a
    | inr b => build_IH_B b
    end).

Definition build_IH_eq@{} (A' : Code) (el : ∀ x, P x) :
  ∀ x, Id (build_IH A' x (λ p c ↦ el _)) (All_in A' (λ p ↦ el _)) :=
  Code_rec
  (λ A' ↦ ∀ x, Id (build_IH A' x (λ p c ↦ el _)) (All_in A' (λ p ↦ el _)))
  (λ x ↦ refl)
  (λ A B build_IH_eq_B ↦ λ x ↦ build_IH_eq_B x.(fst) x.(snd))
  (λ Ix B build_IH_eq_B ↦ λ x ↦
   cong (pair (el ∘ x.(fst))) (build_IH_eq_B x.(snd)))
  (λ B build_IH_eq_B ↦ λ x ↦
   cong (pair (el x.(fst))) (build_IH_eq_B x.(snd)))
  (λ A B build_IH_eq_A build_IH_eq_B ↦ λ x ↦ match x with
    | inl a => build_IH_eq_A a
    | inr b => build_IH_eq_B b
    end)
  A'.

Definition rec_helper@{} t (hered : All A (canonical A ∘ _))
  (IH : ∀ p c, P (get_f t p; c)) :
  split_view A t hered → P (sup _ _; hered; t; refl) :=
  λ cover ↦ split_view_elim@{j}
  (λ t hered _ ↦ (∀ p c, P (get_f t p; c)) → P (sup _ _; hered; t; refl))
  (λ x ↦ λ IH ↦ IS x (build_IH A x IH))
  _ _ cover IH.
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