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
    mf <*> ma = bindM mf (fun f => bindM ma (fun a => (f ∘ pure) a));
  bind_fmap : forall {A B C : Type} (f : A -> B) (x : M A) (g : B -> M C),
    bindM (f <$> x) g = bindM x (f ∘ g);
  bind_pass : ∀ {A B} (ma : M A) (mb : M B), ma >> mb = bindM ma (λ _, mb);
}.
Hint Rewrite @bind_id_left @bind_id_right @bind_assoc @bind_app : soundness.

Definition composeM {M : Type → Type} `{Monad M}
  {A B C} (f : A -> M B) (g : B -> M C) (x : A) : M C :=
  bindM (f x) g.

Ltac solve_monad := repeat (simplify; simple_solve;
  match goal with
  | |- bindM ?f _ = ?f => rewrite <- bind_id_right; f_equal
  | |- bindM ?f _ = bindM ?f _ => f_equal
  | _ => simple_solve
  end).

Notation "x >>= y" := (bindM x y) (at level 40, left associativity).
Notation "x >=> y" := (composeM x y) (at level 40, left associativity).

Section laws_and_methods.
  Context {M : Type -> Type} `{Monad M}.
  
  Definition join {A} (x : M (M A)) : M A := bindM x id.

  Lemma join_fmap {A : Type} (x : M(M(M(A)))) : 
    join (join <$> x) = join (join x).
  Proof.
    unfold join. rewrite bind_fmap. rewrite bind_assoc.
    f_equal.
  Qed.

  Lemma join_return {A : Type} (x :M A) : 
    join (fmap pure x) = join (pure x).
  Proof.
    unfold join. rewrite bind_id_left. 
    rewrite id_refl. unfold id. rewrite bind_fmap.
    unfold compose. apply bind_id_right. 
  Qed.
 
  Lemma fmap_bind : forall {A B C : Type} (x : M A) (f : A -> M B) (g : B -> C),
    fmap g (bindM x f) = bindM x (fun a : A => fmap g (f a)).
  Proof. 
    intros. rewrite app_fmap. rewrite bind_app. rewrite bind_id_left.
    rewrite bind_assoc. f_equal. ext. rewrite app_fmap.
    rewrite bind_app. rewrite bind_id_left. f_equal.
  Qed.

  Lemma fmap_bind_pure : forall {A B} (f : A -> B) (x : M A),
    fmap f x = bindM x (fun a : A => (f ∘ pure) a).
  Proof.
    intros. rewrite <- bind_fmap. rewrite bind_id_right. reflexivity.
  Qed.

  Lemma composeM_assoc : forall {A B C D} 
    (f : A -> M B) (g : B -> M C) (h : C -> M D),
    f >=> (g >=> h) = (f >=> g) >=> h.
  Proof.
    intros. unfold composeM. ext. rewrite bind_assoc. f_equal.
  Qed.

  Lemma composeM_pure_left : forall {A B} (f : A -> M B),
    pure >=> f = f.
  Proof.
    intros. unfold composeM. ext. rewrite bind_id_left. reflexivity.
  Qed.

  Lemma composeM_pure_right : ∀ {A B} (f : A → M B),
    f >=> pure = f.
  Proof.
    intros. unfold composeM. ext. rewrite bind_id_right. reflexivity.
  Qed.

  Lemma composeM_comp : ∀ {A B C} (f : A → B) (g : B → M C),
    (f ∘ pure) >=> g = f ∘ g.
  Proof.
    intros. unfold composeM, compose. ext.
    rewrite bind_id_left. reflexivity.
  Qed.

  Lemma composeM_fmap : ∀ {A B C} (f : A → M B) (g : B → C),
    f >=> (g ∘ pure) = f ∘ fmap g.
  Proof.
    intros. unfold composeM. ext. rewrite <- bind_fmap. rewrite bind_id_right.
    reflexivity. 
  Qed.

End laws_and_methods.
Hint Rewrite @bind_fmap @fmap_bind @fmap_bind_pure : soundness.
Hint Rewrite <- @bind_pass : soundness.

Notation "x >>= y" := (bindM x y) (at level 40, left associativity).
Notation "x >=> y" := (composeM x y) (at level 40, left associativity).
Notation "x '<-' y ; z" := (bindM y (fun x => z))
  (at level 20, y at level 100, z at level 200, only parsing).


Section MonadTransformer.
  Context {M} `{inst : Monad M}.

  Class MonadT (T : (Type -> Type) -> Type -> Type) `{Monad (T M)} : Type :=
  {
    liftT : ∀ {A}, M A -> T M A;
    lift_pure : ∀  {A : Type} (x : A), liftT (pure x) = pure x;
    lift_bind : ∀ {A B : Type} (x : M A) (f : A -> M B),
      liftT (x >>= f) = liftT x >>= (f ∘ liftT);
  }.
End MonadTransformer.
Hint Unfold liftT : soundness.
Hint Rewrite @lift_pure @lift_bind : soundness.
