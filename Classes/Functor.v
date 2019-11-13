Require Export Base.
Require Import Coq.Program.Basics.

Class Functor (F : Type -> Type) : Type := {
  fmap : forall {A B}, (A -> B) -> F A -> F B;
  fmap_id : forall {A}, fmap (@id A) = id;
  fmap_compose : 
    forall {A B C : Type} (f : A -> B) (g : B -> C),
    fmap (f ∘ g) = fmap f ∘ fmap g;
}.

Notation "x '<$>' y" := (fmap x y)
  (at level 20, y at level 100, only parsing).

Section methods.
  Context {F : Type -> Type} `{Functor F} {A B : Type}.

  Lemma fmap_compose_simple : forall {A B C} (f : A -> B) (g : B -> C) x,
    fmap (f ∘ g) x = fmap g (fmap f x).
  Proof.
    intros. rewrite fmap_compose. unfold compose. reflexivity.
  Qed.

  Definition fmap_replace_left (a : A) (fb : F B) : F A :=
    fmap (Basics.const a) fb.

  Definition fmap_replace_right (fa : F A) (b : B) : F B :=
    fmap (Basics.const b) fa.

End methods.
Hint Rewrite @fmap_compose_simple : soundness.
Hint Rewrite @fmap_id @fmap_compose : soundness.

Infix "<$" := fmap_replace_left (at level 40).
Infix "$>" := fmap_replace_right (at level 40).
