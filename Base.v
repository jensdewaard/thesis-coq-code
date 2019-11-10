Require Export Utf8.
Require Import Program.Basics.
Require Import FunctionalExtensionality.

Create HintDb soundness.

Ltac inv H := inversion H; subst; clear H.

Notation "f '$' x" := (f x)
  (at level 20, right associativity, only parsing).

Definition id := fun {A : Type} (a : A) => a.

Lemma id_refl : forall {A : Type} (x : A), id x = x.
Proof. reflexivity. Qed.

Hint Rewrite @id_refl : soundness.

Notation "f ∘ g" := (compose g f).

Ltac ext := let x := fresh "x" in extensionality x.

Ltac unmatch x :=
  match x with
  | context [match ?y with _ => _ end] => unmatch y
  | _ => destruct x eqn:?
  end.

Ltac destr :=
  match goal with
  | [ |- context [match ?x with _ => _ end]] => unmatch x
  | [ |- context [let (_, _) := ?x in _]] => destruct x eqn:?
  | H : (_ , _) = (_, _) |- _ => inv H; subst
  end.

Ltac simplify := simpl; intros; repeat ext; try destr.

Ltac simple_solve := 
  repeat (simplify; autorewrite with soundness + autounfold with soundness);
  unfold compose;
  try (congruence + reflexivity).

Global Set Typeclasses Depth 5.
