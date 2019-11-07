Require Export Base.

Class Functor (F : Type -> Type) : Type := {
  fmap : forall {A B}, (A -> B) -> F A -> F B;
  fmap_id : forall A, fmap (@id A) = id;
  fmap_compose : 
    forall (A B C : Type) (f : A -> B) (g : B -> C),
    fmap (f ∘ g) = fmap f ∘ fmap g;
}.

Notation "x '<$>' y" := (fmap x y)
  (at level 20, y at level 100, only parsing).
