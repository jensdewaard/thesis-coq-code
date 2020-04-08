Require Export Base.
Require Import Classes.Monad Classes.Joinable Classes.Galois.

Class MonadJoin M {MM : Monad M} : Type := {
  mjoin : ∀ {A} {JA : Joinable A A} {JI : JoinableIdem JA}, M A → M A → M A;
  mjoin_return : ∀ {A} {JA : Joinable A A} {JI : JoinableIdem JA} (x y : A),
    mjoin (returnM x) (returnM y) = returnM (x ⊔ y);
}.
Hint Rewrite @mjoin_return : monads.

Infix "<⊔>" := mjoin (at level 40).

Definition mjoin_option A {JA : Joinable A A} {JI : JoinableIdem JA} : 
  option A → option A → option A :=
  λ m1 : option A, λ m2 : option A,
    match m1, m2 with
    | Some x, Some y => Some (x ⊔ y)
    | _, _ => None
    end.

Instance option_monadjoin : MonadJoin option.
Proof.
  split with mjoin_option. reflexivity.
Defined.
