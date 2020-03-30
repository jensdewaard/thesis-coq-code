Require Export Utf8.
Require Export Program.Basics.
Require Export FunctionalExtensionality.
Require Import Coq.Arith.Even.

Create HintDb soundness.

Ltac inv H := inversion H; subst; clear H.
Ltac inj H := injection H; intros; subst.

Notation "f '$' x" := (f x)
  (at level 20, right associativity, only parsing).

Notation "f ∘ g" := (compose g f).
Definition id := fun {A : Type} (a : A) => a.

Inductive Identity (A : Type) : Type := identity : A → Identity A.
Arguments identity {A} a.

Lemma id_refl : forall {A : Type} (x : A), id x = x.
Proof. reflexivity. Qed.
Lemma id_compose_left : forall {A B} (f : A -> B), id ∘ f = f.
Proof. reflexivity. Qed.
Lemma id_compose_right : forall {A B} (f : A -> B), f ∘ id = f.
Proof. reflexivity. Qed.

Hint Rewrite @id_refl @id_compose_left @id_compose_right : soundness.

Inductive optionA (A : Type) : Type :=
  | SomeA : A → optionA A
  | NoneA : optionA A
  | SomeOrNoneA : A → optionA A.
Arguments SomeA {A} a.
Arguments NoneA {A}.
Arguments SomeOrNoneA {A} a.
Definition optionT (M : Type → Type) (A : Type) : Type := M (option A).
Definition optionAT (M : Type → Type) (A : Type) : Type := M (optionA A).

Definition flip {A B C : Type} (f : A → B → C) (x : B) (y : A) : C :=
  f y x.

Ltac ext := let x := fresh "x" in extensionality x.

Ltac unmatch x :=
  match x with
  | context [match ?y with _ => _ end] => unmatch y
  | _ => destruct x eqn:?
  end.

(* The destr tactic gets rid of let bindings in the goal, match constructs in
 * the goal and equality between pairs in the context *)
Ltac destr :=
  match goal with
  | [ |- context [match ?x with _ => _ end]] => unmatch x
  | [ |- context [let (_, _) := ?x in _]] => destruct x eqn:?
  | H : (_ , _) = (_, _) |- _ => inv H
  | H : _ /\ _ |- _ => destruct H
  | H : match ?x with _ => _ end |- _ => destruct x eqn:?
  | |- _ ∧ _ => split
  end.

Ltac simplify := simpl in *; intros; repeat ext; try destr; 
  destruct_all unit.

Ltac simple_solve := autounfold with soundness; intros;
  repeat (simplify; 
    autorewrite with soundness in * + autounfold with soundness in *;
    intros; subst
  );
  try (unfold compose, id, const; contradiction + discriminate + eauto with soundness).

(* We have some recursive typeclasses instances, for example Monad M -> 
 * Monad (MaybeT M). As typeclass instances search by default is depth first 
 * and unbounded, we set an upperbound here to avoid infinite loops *)
Global Set Typeclasses Depth 10.

Class Inhabited (S : Type) := inhabitent : S.
Arguments inhabitent _ {_}.

Class SubType (sub : Type) (super : Type) : Type := {
  inject : sub → super;
  project : super → option sub
}.

Instance subtype_l : ∀ {A B}, SubType A (A + B) := {
  inject := inl;
  project := λ s, match s with | inl x => Some x | _ => None end
}.

Instance subtype_self : ∀ {A}, SubType A A := {
  inject := id;
  project := λ x, Some x
}.

Instance subtype_r : ∀ {A B C} `{SubType A B}, SubType A (C + B) := {
  inject := inject ∘ inr;
  project := λ s, match s with | inr x => project x | _ => None end
}.

Class top_op (A:Type) : Type := top : A.
Notation "⊤" := top (at level 40).

Inductive toplift (A: Type) := 
  | Top : top_op (toplift A) 
  | NotTop : A → toplift A.
Notation "t +⊤" := (toplift t) (at level 39).

Inductive botlift (A:Type) : Type := 
  | Bot 
  | NotBot (x:A).
Notation "t +⊥" := (botlift t) (at level 39).

