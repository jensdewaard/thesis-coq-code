Require Export Base.
Require Import Classes.Monad Classes.Joinable Classes.Galois.

Class MonadJoin M {MM : Monad M} : Type := {
  mjoin : ∀ {A} {JA : Joinable A A}, M A → M A → M A;
  mjoin_return : ∀ {A} {JA : Joinable A A} (x y : A),
    mjoin (returnM x) (returnM y) = returnM (x ⊔ y);
}.
Hint Rewrite @mjoin_return : monads.

Infix "<⊔>" := mjoin (at level 40).
