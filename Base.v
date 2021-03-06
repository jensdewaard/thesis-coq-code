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


(* We have some recursive typeclasses instances, for example Monad M -> 
 * Monad (MaybeT M). As typeclass instances search by default is depth first 
 * and unbounded, we set an upperbound here to avoid infinite loops *)
Global Set Typeclasses Depth 10.

Class top_op (A:Type) : Type := top : A.
Notation "⊤" := top (at level 40).

Inductive toplift (A: Type) := 
  | Top : top_op (toplift A) 
  | NotTop : A → toplift A.
Arguments Top {A}.
Arguments NotTop {A}.
Notation "t +⊤" := (toplift t) (at level 39).

Inductive botlift (A:Type) : Type := 
  | Bot 
  | NotBot (x:A).
Arguments Bot {A}.
Arguments NotBot {A}.
Notation "t +⊥" := (botlift t) (at level 39).

Section top_bot_coercions.
  Context {A : Type}.

  Definition A_to_top (a : A) : (A+⊤) := NotTop a.
  Coercion A_to_top : A >-> toplift.

  Definition A_to_bot (a : A) : (A+⊥) := NotBot a.
  Coercion A_to_bot : A >-> botlift.
End top_bot_coercions.

Class SubType (sub : Type) (super : Type) : Type := {
  inject : sub → super;
  project : super → option sub
}.

Instance subtype_l : ∀ {A B}, SubType A (A + B) := {
  inject := inl;
  project := λ s, match s with | inl x => Some x | _ => None end
}.

Instance subtype_r : ∀ {A B}, SubType B (A+B) := {
  inject := inr;
  project := λ s, match s with | inr x => Some x | _ => None end
}.

Instance subtype_trans_r : ∀ {A B C} `{SubType A B}, SubType A (C + B) := {
  inject := inject ∘ inr;
  project := λ s, match s with | inr x => project x | _ => None end
}.

Instance subtype_trans_l {A B C} `{S : SubType A B} : SubType A (B + C).
Proof. destruct S as [inject project]. split.
  - exact (λ a, inl (inject a)).
  - exact (λ bc, match bc with
                 | inr _ => None
                 | inl b => project b
                 end).
Defined.

Instance subtype_top_r : ∀ A, SubType A (A+⊤) := {
  inject := NotTop;
  project := λ a, match a with
                  | Top => None
                  | NotTop x => Some x
                  end;
}.

Instance subtype_bot_r : ∀ A, SubType A (A+⊥) := {
  inject := NotBot;
  project := λ a, match a with
                  | Bot => None
                  | NotBot x => Some x
                  end;
}.

Instance subtype_top_l {A B} `{SubType A B} : 
  SubType (A+⊤) (B+⊤).
Proof. destruct H as [inject project]. split.
  exact (λ a : (A+⊤), match a with
                      | Top => Top
                      | NotTop x => NotTop( inject x)
                      end).
  exact (λ b : (B+⊤), match b with
                      | Top => None
                      | NotTop x => match (project x) with
                                    | Some x' => Some (NotTop x')
                                    | None => None
                                    end
                      end).
Defined.


Notation "℘ A" := (A → Prop) (at level 0, only parsing).
Definition union {U : Type} (A B : U → Prop) : U → Prop :=
  λ u : U, A u ∨ B u.
Infix "∪" := union (at level 40).

Definition intersection {U : Type} (A B : U → Prop) : U → Prop :=
  λ u : U, A u ∧ B u.
Infix "∩" := intersection (at level 40).

Definition subset {U : Type} (A B : U → Prop) : Prop :=
  ∀ u : U, A u → B u.
Infix "⊆" := subset (at level 40).
