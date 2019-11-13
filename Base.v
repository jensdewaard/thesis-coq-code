Require Export Utf8.
Require Export Program.Basics.
Require Export FunctionalExtensionality.

Create HintDb soundness.

Ltac inv H := inversion H; subst; clear H.

Notation "f '$' x" := (f x)
  (at level 20, right associativity, only parsing).

Notation "f ∘ g" := (compose g f).
Definition id := fun {A : Type} (a : A) => a.

Lemma id_refl : forall {A : Type} (x : A), id x = x.
Proof. reflexivity. Qed.
Lemma id_compose_left : forall {A B} (f : A -> B), id ∘ f = f.
Proof. reflexivity. Qed.
Lemma id_compose_right : forall {A B} (f : A -> B), f ∘ id = f.
Proof. reflexivity. Qed.

Hint Rewrite @id_refl @id_compose_left @id_compose_right : soundness.


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
  | H : (_ , _) = (_, _) |- _ => inv H; subst
  end.

Ltac simplify := cbn; intros; repeat ext; try destr.

Ltac simple_solve := cbn; intros;
  repeat (autorewrite with soundness + autounfold with soundness);
  try (unfold compose, id, const; congruence + reflexivity).

(* We have some recursive typeclasses instances, for example Monad M -> 
 * Monad (MaybeT M). As typeclass instances search by default is depth first 
 * and unbounded, we set an upperbound here to avoid infinite loops *)
Global Set Typeclasses Depth 5.
