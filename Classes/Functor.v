Require Export Base.
Require Import Coq.Program.Basics.

Implicit Type M : Type → Type.
Implicit Types A B C : Type.

Class Functor M : Type := {
  fmap : forall {A B}, (A -> B) -> (M A -> M B);
  fmap_id : forall {A}, fmap (@id A) = id;
  fmap_compose : 
    forall {A B C} (f : A -> B) (g : B -> C),
    fmap (f ∘ g) = fmap f ∘ fmap g;
}.
Arguments fmap : simpl never.

Notation "x '<$>' y" := (fmap x y)
  (at level 40, left associativity).

Section methods.
  Context {M} `{M_functor : Functor M}.

  (* g (f a) = compose g f = f ∘ g *)
  Definition fmap_replace_left {A B} : A → M B → M A :=
    (const ∘ fmap).

  Definition fmap_replace_right {A B} : M A → B → M B :=
    flip fmap_replace_left.

  Definition void {A} (fa : M A) : M unit := fmap_replace_left tt fa.
End methods.

Hint Rewrite @fmap_id : soundness.
Hint Rewrite @fmap_compose using unfold compose : soundness.

Infix "<$" := fmap_replace_left (at level 40).
Infix "$>" := fmap_replace_right (at level 40).
