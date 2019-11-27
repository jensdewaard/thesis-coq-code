Require Export Base.
Require Import Coq.Program.Basics.

Class Functor (F : Type -> Type) : Type := {
  fmap : forall {A B}, (A -> B) -> (F A -> F B);
  fmap_id : forall {A}, fmap (@id A) = id;
  fmap_compose : 
    forall {A B C : Type} (f : A -> B) (g : B -> C),
    fmap (f ∘ g) = fmap f ∘ fmap g;
}.

Notation "x '<$>' y" := (fmap x y)
  (at level 40, left associativity).

Section methods.
  Context {F : Type -> Type} `{F_inst: Functor F}.

  (* g (f a) = compose g f = f ∘ g *)
  Definition fmap_replace_left {A B} : A → F B → F A :=
    (const ∘ fmap).

  Definition fmap_replace_right {A B} : F A → B → F B :=
    flip fmap_replace_left.

  Definition void {A} (fa : F A) : F unit := fmap_replace_left tt fa.
End methods.

Hint Rewrite @fmap_id : soundness.
Hint Rewrite @fmap_compose using unfold compose : soundness.

Infix "<$" := fmap_replace_left (at level 40).
Infix "$>" := fmap_replace_right (at level 40).
