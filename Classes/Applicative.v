Require Export Base.
Require Import Classes.Functor.
Require Import Coq.Program.Basics.

Implicit Type F : Type → Type.
Implicit Type A B C : Type.

Class Applicative F : Type :=
{
  is_functor :> Functor F;
  pure : forall {A}, A -> F A;
  pure_inj : ∀ {A} (x y : A), pure x = pure y → x = y;
  app : forall {A B}, F (A -> B) -> F A -> F B;
  app_id : forall {A} (x : F A), app (pure id) x = x;
  app_homomorphism : forall {A B} (f:A -> B) (x:A), 
    app (pure f) (pure x) = pure (f x);
  app_interchange : forall {A B} (u : F (A -> B)) (y : A), 
    app u (pure y) = app (pure (fun f => f y)) u;
  app_compose : forall {A B C} (u : F (B -> C)) (v : F (A -> B)) (w : F A),
    app u (app v w) = app (app (app (pure compose) u) v) w;
  app_fmap : forall {A B} (f : A -> B) (x : F A), 
    fmap f x = app (pure f) x;
}.

Infix "<*>" := app (left associativity, at level 40).

Hint Rewrite @app_homomorphism @app_compose @app_interchange : soundness.
Hint Rewrite @app_fmap : soundness.

Section laws_and_methods.
  Context {F} `{Applicative F}.

  Definition pass {A B} (fa : F A) (fb : F B) : F B := 
    (id <$ fa) <*> fb.
  Notation "x >> y" := (pass x y) (right associativity, at level 41).
  Hint Unfold pass : soundness.

  Definition keep {A B} (fa : F A) (fb : F B) : F A :=
    flip pass fa fb.
  Notation "x << y" := (keep x y) (right associativity, at level 41).
  Hint Unfold keep : soundness.

  Lemma pass_right : forall {A B} (x : A) (y : F B), 
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

  Definition liftA {A B} (f : A -> B) (fa : F A) : (F B) := 
    pure f <*> fa.

  Definition liftA2 {A B C} (f : A -> B -> C) (fa : F A) (fb : F B) : F C :=
    pure f <*> fa <*> fb.

End laws_and_methods.
Infix ">>" := pass (right associativity, at level 41).
Infix "<<" := keep (right associativity, at level 41).
Notation "x ;; z" := (pass x z)
    (at level 100, z at level 200, only parsing, right associativity).
Hint Rewrite @fmap_pure @pass_right : soundness.

