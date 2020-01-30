Require Export Base.
Require Import Classes.Monad.
Require Import Classes.Applicative.
Require Import Classes.Galois.

Class MonadFail M `{M_monad : Monad M} : Type := {
  fail {A : Type} : M A;
  fail_left: ∀ {A B} (m : A → M B), (@fail A) >>= m = fail;
}.
Arguments fail : simpl never.
Hint Rewrite @fail_left : soundness.
