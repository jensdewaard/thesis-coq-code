Require Export Base.
Require Import Classes.Monad Classes.Galois.

Class MonadFail M {BM : bind_op M} : Type := {
  fail : ∀ {A : Type}, M A;
  fail_left: ∀ {A B} (m : A → M B), fail >>= m = fail;
}.
Arguments fail : simpl never.
Hint Rewrite @fail_left : monads.

Class MonadFail_sound (M M' : Type → Type) 
  {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')}
  `{MF : MonadFail M} `{MF' : MonadFail M'} : Prop :=
  fail_sound : ∀ {A A' : Type} {GA : Galois A A'} (m' : M' A'),
    γ (fail (A:=A) (M:=M)) m'.
