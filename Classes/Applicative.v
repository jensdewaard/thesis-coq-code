Require Export Base.
Require Import Classes.Functor.
Require Import Coq.Program.Basics.

Class Applicative (F : Type -> Type) `{Functor F} : Type :=
{
  pure : forall {A}, A -> F A;
  app : forall {A B}, F (A -> B) -> F A -> F B;
  app_id : forall {A} f, app (pure (@id A)) f = f;
  app_homomorphism : forall {A B} (f:A -> B) (x:A), 
    app (pure f) (pure x) = pure (f x);
  app_interchange : forall {A B} (u : F (A -> B)) (y : A), 
    app u (pure y) = app (pure (fun f => f y)) u;
  app_compose : forall {A B C} (u : F (B -> C)) (v : F (A -> B)) (w : F A),
    app (app (app (pure compose) (u)) v) (w) = app (u) (app v w);
}.

Notation "x '<*>' y" := (app x y)
  (at level 20, y at level 100, only parsing).
