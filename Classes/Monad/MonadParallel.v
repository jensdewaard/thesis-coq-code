Require Import Classes.Monad.

Class MonadParallel (M : Type → Type) `{Monad M} :=
{
  bindM2 : ∀ {A B C}, M A → M B → (A → B → M C) → M C;
}.
