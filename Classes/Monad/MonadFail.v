Require Export Base.
Require Import Classes.Monad.

Class MonadFail M {MM : Monad M} : Type := {
  fail : ∀ {A : Type}, M A;
  fail_left: ∀ {A B} (m : A → M B), (@fail A) >>= m = fail;
}.
Arguments fail : simpl never.
Hint Rewrite @fail_left : soundness.
