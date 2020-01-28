Require Export Base.
Require Import Classes.Functor.
Require Import Coq.Program.Basics.
Require Import Coq.Logic.FinFun.

Implicit Type M : Type → Type.
Implicit Type A B C : Type.

Class Applicative M `{M_functor: Functor M} : Type :=
{
  pure : forall {A}, A -> M A;
  pure_inj : ∀ {A}, Injective (A:=A) pure;
  app : forall {A B}, M (A -> B) -> M A -> M B;
  app_id : forall {A} (x : M A), app (pure id) x = x;
  app_homomorphism : forall {A B} (f : A -> B) (x:A), 
    app (pure f) (pure x) = pure (f x);
  app_interchange : forall {A B} (u : M (A -> B)) (y : A), 
    app u (pure y) = app (pure (fun f => f y)) u;
  app_compose : forall {A B C} (u : M (B -> C)) (v : M (A -> B)) (w : M A),
    app u (app v w) = app (app (app (pure compose) u) v) w;
  app_fmap : forall {A B} (f : A -> B) (x : M A), 
    fmap f x = app (pure f) x;
}.
Arguments pure : simpl never.
Arguments app : simpl never.

Infix "<*>" := app (left associativity, at level 40).

Hint Rewrite @app_homomorphism @app_compose @app_interchange : soundness.
Hint Rewrite @app_fmap : soundness.

Section laws_and_methods.
  Context {M} `{Applicative M}.

  Definition pass {A B} (fa : M A) (fb : M B) : M B := 
    (id <$ fa) <*> fb.
  Notation "x >> y" := (pass x y) (right associativity, at level 41).
  Hint Unfold pass : soundness.

  Definition keep {A B} (fa : M A) (fb : M B) : M A :=
    flip pass fa fb.
  Notation "x << y" := (keep x y) (right associativity, at level 41).
  Hint Unfold keep : soundness.

  Lemma pass_right : forall {A B} (x : A) (y : M B), 
    pure x >> y = y.
  Proof. 
    intros. unfold pass. unfold fmap_replace_left. unfold compose. 
    rewrite app_fmap, app_homomorphism, app_id.
    reflexivity.
  Qed.

  Lemma fmap_pure : forall {A B} (f : A -> B) (x : A),
    fmap f (pure x) = pure (f x).
  Proof. 
    intros. rewrite app_fmap, app_homomorphism. reflexivity.
  Qed.

  Definition liftA {A B} (f : A -> B) (fa : M A) : (M B) := 
    pure f <*> fa.

  Definition liftA2 {A B C} (f : A -> B -> C) (fa : M A) (fb : M B) : M C :=
    pure f <*> fa <*> fb.

End laws_and_methods.
Infix ">>" := pass (right associativity, at level 41).
Infix "<<" := keep (right associativity, at level 41).
Notation "x ;; z" := (pass x z)
    (at level 100, z at level 200, only parsing, right associativity).
Hint Rewrite @fmap_pure @pass_right : soundness.

