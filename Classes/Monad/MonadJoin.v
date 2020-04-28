Require Export Base.
Require Import Classes.Monad Classes.Joinable Classes.Galois.

Class MonadJoin M `{MM : Monad M} : Type := {
  mjoin : ∀ {A} {JA : Joinable A A} {JI : JoinableIdem JA}, M A → M A → M A;
  mjoin_return : ∀ {A} {JA : Joinable A A} {JI : JoinableIdem JA} (x y : A),
    mjoin (returnM x) (returnM y) = returnM (x ⊔ y);
}.
Hint Rewrite @mjoin_return : monads.
Infix "<⊔>" := mjoin (at level 40).

Class MonadJoinSound (M M' : Type → Type) `{MM : Monad M} {MJ : MonadJoin M}
  `{MM' : Monad M'} {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')} : Type :=
{
  mjoin_sound_left : ∀ {A A'} {JA : Joinable A A} {JAI : JoinableIdem JA} 
    {GA : Galois A A'} {JS : JoinableSound JA} (m1 m2 : M A) (m' : M' A'),
    γ m1 m' → γ (m1 <⊔> m2) m';
  mjoin_sound_right : ∀ {A A'} {JA : Joinable A A} {JAI : JoinableIdem JA}
    {GA : Galois A A'} {JS : JoinableSound JA} (m1 m2 : M A) (m' : M' A'),
    γ m2 m' → γ (m1 <⊔> m2) m';
}.

