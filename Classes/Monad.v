Require Export Base.
Require Import Classes.Functor.
Require Import Classes.Applicative.
Require Import Classes.PreorderedSet.

Implicit Type M : Type → Type.
Implicit Type T : (Type → Type) → Type → Type.
Implicit Type A B C D : Type.

Class Monad M `{Applicative M}: Type :=
{
  bindM : ∀ {A B}, M A  → (A → M B) → M B;
  bind_id_left : ∀ {A B} (f : A → M B) (a : A), 
    bindM (pure a) f = f a;
  bind_id_right : ∀ {A} (MA : M A),
    bindM MA pure = MA;
  bind_assoc : ∀ {A B C} (MA : M A) (f : A → M B) (g : B → M C),
    bindM (bindM MA f) g = bindM MA (λ a, bindM (f a) g);
  bind_app : ∀ {A B} (mf : M (A → B)) (ma : M A),
    mf <*> ma = bindM mf (λ f, bindM ma (λ a, (f ∘ pure) a));
  bind_fmap : ∀ {A B C} (f : A → B) (x : M A) (g : B → M C),
    bindM (f <$> x) g = bindM x (f ∘ g);
  bind_pass : ∀ {A B} (ma : M A) (mb : M B), ma >> mb = bindM ma (λ _, mb);
}.
Arguments bindM : simpl never.
Hint Unfold bindM : soundness.

Hint Rewrite @bind_id_left @bind_id_right @bind_assoc @bind_app : soundness.

Definition skip {M} `{Monad M} := pure tt.

Definition composeM {M : Type → Type} `{Monad M}
  {A B C} (f : A → M B) (g : B → M C) (x : A) : M C :=
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
  Context {M} `{Monad M}.

  Definition join {A} (x : M (M A)) : M A := bindM x id.

  Lemma join_fmap {A : Type} (x : M(M(M(A)))) : 
    join (join <$> x) = join (join x).
  Proof.
    unfold join. rewrite bind_fmap. rewrite bind_assoc.
    f_equal.
  Qed.

  Lemma join_return {A} (x : M A) : 
    join (fmap pure x) = join (pure x).
  Proof.
    unfold join. rewrite bind_id_left. 
    rewrite id_refl. unfold id. rewrite bind_fmap.
    unfold compose. apply bind_id_right. 
  Qed.
 
  Lemma fmap_bind : ∀ {A B C} (x : M A) (f : A → M B) (g : B → C),
    fmap g (bindM x f) = bindM x (λ a, fmap g (f a)).
  Proof. 
    intros. rewrite app_fmap. rewrite bind_app. rewrite bind_id_left.
    rewrite bind_assoc. f_equal. ext. rewrite app_fmap.
    rewrite bind_app. rewrite bind_id_left. f_equal.
  Qed.

  Lemma fmap_bind_pure : ∀ {A B} (f : A → B) (x : M A),
    fmap f x = bindM x (λ a, (f ∘ pure) a).
  Proof.
    intros. rewrite <- bind_fmap. rewrite bind_id_right. reflexivity.
  Qed.

  Lemma composeM_assoc : ∀ {A B C D} 
    (f : A → M B) (g : B → M C) (h : C → M D),
    f >=> (g >=> h) = (f >=> g) >=> h.
  Proof.
    intros. unfold composeM. ext. rewrite bind_assoc. f_equal.
  Qed.

  Lemma composeM_pure_left : ∀ {A B} (f : A → M B),
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
Notation "x '<-' y ; z" := (bindM y (λ x, z))
  (at level 20, y at level 100, z at level 200, only parsing).


Section MonadTransformer.
  Context {M} `{inst : Monad M}.

  Class MonadT T `{Monad (T M)} : Type :=
  {
    liftT : ∀ {A}, M A → T M A;
    lift_pure : ∀  {A} (x : A), liftT (pure x) = pure x;
    lift_bind : ∀ {A B} (x : M A) (f : A → M B),
      liftT (x >>= f) = liftT x >>= (f ∘ liftT);
  }.
End MonadTransformer.
Hint Unfold liftT : soundness.
Hint Rewrite @lift_pure @lift_bind : soundness.
