Require Export Base.
Require Import Classes.Functor.
Require Import Classes.Applicative.

Class Monad (M : Type -> Type) `{Applicative M} : Type :=
{
  bindM : forall {A B}, M A  -> (A -> M B) -> M B;
  bind_id_left : forall (A B : Type) (f : A -> M B) (a : A), 
    bindM (pure a) f = f a;
  bind_id_right : forall (A : Type) (MA : M A),
    bindM MA pure = MA;
  bind_assoc : forall (A B C : Type) (MA : M A) (f : A -> M B) (g : B -> M C),
    bindM (bindM MA f) g = bindM MA (fun a => bindM (f a) g);
}.

Lemma bind_equiv_l {M : Type -> Type} {A B : Type} `{Monad M} : 
  forall (m m' : M A) (k : A -> M B),
  m = m' -> bindM m k = bindM m' k.
Proof.
  intros. subst. reflexivity.
Qed.

Lemma bind_equiv_r {M : Type -> Type} {A B : Type} `{Monad M} : 
  forall (m : M A) (k k' : A -> M B),
  k = k' -> bindM m k = bindM m k'.
Proof.
  intros. subst. reflexivity.
Qed.

Notation "x '<<' y ; z" := (bindM y (fun x => z))
  (at level 20, y at level 100, z at level 200, only parsing).

Notation "x ;; z" := (bindM x (fun _ => z))
    (at level 100, z at level 200, only parsing, right associativity).

Hint Rewrite @bind_id_left @bind_id_right @bind_assoc @bind_equiv_l 
  @bind_equiv_r : soundness.

Section MonadTransformer.
  Context {M} `{inst : Monad M}.

  Class MonadT (T : (Type -> Type) -> Type -> Type) : Type :=
  {
    liftT : forall {A}, M A -> T M A;
  }.
End MonadTransformer.
