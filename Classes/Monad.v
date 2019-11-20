Require Export Base.
Require Import Classes.Functor.
Require Import Classes.Applicative.
Require Import Classes.PreorderedSet.

Class Monad (M : Type -> Type) `{Applicative M} : Type :=
{
  bindM : forall {A B}, M A  -> (A -> M B) -> M B;
  bind_id_left : forall {A B : Type} (f : A -> M B) (a : A), 
    bindM (pure a) f = f a;
  bind_id_right : forall {A : Type} (MA : M A),
    bindM MA pure = MA;
  bind_assoc : forall {A B C : Type} (MA : M A) (f : A -> M B) (g : B -> M C),
    bindM (bindM MA f) g = bindM MA (fun a => bindM (f a) g);
  bind_app : forall {A B : Type} (mf : M (A -> B)) (ma : M A),
    app mf ma = bindM mf (fun f => bindM ma (fun a => pure (f a)));
  bind_fmap : forall {A B C : Type} (f : A -> B) (x : M A) (g : B -> M C),
    bindM (fmap f x) g = bindM x (f ∘ g);
}.
Hint Rewrite @bind_id_left @bind_id_right @bind_assoc @bind_app : soundness.

Ltac solve_monad := repeat (simplify; simple_solve;
  match goal with
  | |- bindM ?f _ = ?f => rewrite <- bind_id_right; f_equal
  | |- bindM ?f _ = bindM ?f _ => f_equal
  | _ => simple_solve
  end).

Section laws.
  Context {M : Type -> Type} `{Monad M}.
  
  Lemma fmap_bind : forall {A B C : Type} (x : M A) (f : A -> M B) (g : B -> C),
    fmap g (bindM x f) = bindM x (fun a : A => fmap g (f a)).
  Proof. 
  Admitted.

  Lemma fmap_bind_pure : forall {A B} (f : A -> B) (x : M A),
    fmap f x = bindM x (fun a : A => pure (f a)).
  Proof.
  Admitted.

End laws.
Hint Rewrite @bind_fmap @fmap_bind @fmap_bind_pure : soundness.

Notation "x '<<' y ; z" := (bindM y (fun x => z))
  (at level 20, y at level 100, z at level 200, only parsing).

Notation "x ;; z" := (bindM x (fun _ => z))
    (at level 100, z at level 200, only parsing, right associativity).


Section MonadTransformer.
  Context {M} `{inst : Monad M}.

  Class MonadT (T : (Type -> Type) -> Type -> Type) `{Monad (T M)} : Type :=
  {
    liftT : forall {A}, M A -> T M A;
    lift_pure : forall {A : Type} (x : A), liftT (pure x) = pure x;
    lift_bind : forall {A B : Type} (x : M A) (f : A -> M B),
      liftT (bindM x f) = bindM (liftT x) (f ∘ liftT);
  }.
End MonadTransformer.
Hint Unfold liftT : soundness.
Hint Rewrite @lift_pure @lift_bind : soundness.
