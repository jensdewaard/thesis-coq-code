Require Export Base.

Implicit Type M : Type → Type.
Implicit Type T : (Type → Type) → Type → Type.
Implicit Type A B C D : Type.

Class Monad M : Type :=
{
  returnM : ∀ {A}, A → M A;
  bindM : ∀ {A B}, M A  → (A → M B) → M B;
  bind_id_left : ∀ {A B} (f : A → M B) (a : A), 
    bindM (returnM a) f = f a;
  bind_id_right : ∀ {A} (MA : M A),
    bindM MA returnM = MA;
  bind_assoc : ∀ {A B C} (MA : M A) (f : A → M B) (g : B → M C),
    bindM (bindM MA f) g = bindM MA (λ a, bindM (f a) g);
}.
Arguments bindM : simpl never.
Arguments returnM: simpl never.
Hint Unfold bindM : soundness.
Hint Rewrite @bind_id_left @bind_id_right @bind_assoc : soundness.

Definition join {M} `{Monad M} {A} 
  (mma : M (M A)) : M A :=
  bindM mma id.

Ltac solve_monad := repeat (simplify; simple_solve;
  match goal with
  | |- bindM ?f _ = ?f => rewrite <- bind_id_right; f_equal
  | |- bindM ?f _ = bindM ?f _ => f_equal
  | _ => simple_solve
  end).

Notation "x >>= y" := (bindM x y) (at level 40, left associativity).
Notation "x '<-' y ; z" := (bindM y (λ x, z))
  (at level 20, y at level 100, z at level 200, only parsing).
Notation "x ;; z" := (bindM x (λ _, z))
    (at level 100, z at level 200, only parsing, right associativity).

Section MonadTransformer.
  Context {M} `{M_monad : Monad M}.

  Class MonadT T `{TM_monad : Monad (T M)} : Type :=
  {
    liftT : ∀ {A}, M A → T M A;
    lift_return : ∀  {A} (x : A), liftT (returnM x) = returnM x;
    lift_bind : ∀ {A B} (x : M A) (f : A → M B),
      liftT (x >>= f) = liftT x >>= (f ∘ liftT);
  }.
End MonadTransformer.
Hint Unfold liftT : soundness.
Hint Rewrite @lift_return @lift_bind : soundness.
