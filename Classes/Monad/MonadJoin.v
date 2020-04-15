Require Export Base.
Require Import Classes.Monad Classes.Joinable Classes.Galois.

Class MonadJoin M {MM : Monad M} : Type := {
  mjoin : ∀ {A} {JA : Joinable A A} {JI : JoinableIdem JA}, M A → M A → M A;
  mjoin_return : ∀ {A} {JA : Joinable A A} {JI : JoinableIdem JA} (x y : A),
    mjoin (returnM x) (returnM y) = returnM (x ⊔ y);
}.
Hint Rewrite @mjoin_return : monads.
Infix "<⊔>" := mjoin (at level 40).

Class MonadJoinSound (M M' : Type → Type) {MM : Monad M} {MJ : MonadJoin M}
  {MM' : Monad M'} {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')} : Type :=
{
  mjoin_sound_left : ∀ {A A'} {JA : Joinable A A} {JAI : JoinableIdem JA} 
    {GA : Galois A A'} {JS : JoinableSound JA} (m1 m2 : M A) (m' : M' A'),
    γ m1 m' → γ (m1 <⊔> m2) m';
  mjoin_sound_right : ∀ {A A'} {JA : Joinable A A} {JAI : JoinableIdem JA}
    {GA : Galois A A'} {JS : JoinableSound JA} (m1 m2 : M A) (m' : M' A'),
    γ m2 m' → γ (m1 <⊔> m2) m';
}.

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
Hint Resolve option_monadjoin : soundness.

Instance option_monadjoin_sound : MonadJoinSound option option.
Proof.
  constructor; intros.
  - destruct m1, m2; try constructor. destruct m'.
    + constructor. apply join_sound.  constructor. inversion H;subst.
      apply H2.
    + inversion H.
  - destruct m1, m2; try constructor. destruct m'.
    + constructor. apply join_sound. right. inversion H; subst.
      apply H2.
    + inversion H. 
Qed.
