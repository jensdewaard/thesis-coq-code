Require Export Base.
Require Import Classes.Functor.
Require Import Coq.Program.Basics.

Class Applicative (F : Type -> Type) : Type :=
{
  is_functor :> Functor F;
  pure : forall {A}, A -> F A;
  app : forall {A B}, F (A -> B) -> F A -> F B;
  app_homomorphism : forall {A B} (f:A -> B) (x:A), 
    app (pure f) (pure x) = pure (f x);
  app_interchange : forall {A B} (u : F (A -> B)) (y : A), 
    app u (pure y) = app (pure (fun f => f y)) u;
  app_compose : forall {A B C} (u : F (B -> C)) (v : F (A -> B)) (w : F A),
    app (app (app (pure compose) (u)) v) (w) = app (u) (app v w);
  app_fmap : forall (A B : Type) (f : A -> B) (x : F A), 
    fmap f x = app (pure f) x;
}.

Notation "x '<*>' y" := (app x y)
  (left associativity, at level 40, only parsing).

Hint Rewrite @app_homomorphism @app_compose @app_fmap : soundness.
Hint Rewrite <- @app_interchange : soundness.

Section laws_and_methods.
  Context {F : Type -> Type} `{Applicative F}.
  Context {A B C D : Type}.

  Lemma app_id : forall f, app (pure (@id A)) f = f.
  Proof.
    intros. rewrite <- app_fmap. rewrite fmap_id. reflexivity.
  Qed.

  Lemma fmap_pure : forall (f : A -> B) (x : A),
    fmap f (pure x) = pure (f x).
  Proof. 
    intros. rewrite app_fmap. rewrite app_homomorphism. reflexivity.
  Qed.

  Definition liftA (f : A -> B) (fa : F A) : (F B) := 
    pure f <*> fa.

  Definition liftA2 (f : A -> B -> C) (fa : F A) (fb : F B) : F C :=
    pure f <*> fa <*> fb.

  Definition liftA3 (f : A -> B -> C -> D) (fa : F A) (fb : F B) (fc : F C)
    : F D := pure f <*> fa <*> fb <*> fc.

End laws_and_methods.
Hint Rewrite @app_id @fmap_pure : soundness.
