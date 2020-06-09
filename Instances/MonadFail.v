Require Import Classes.Monad.MonadFail.
Require Import Classes.Galois.
Require Import Classes.Joinable.
Require Import Classes.Monad.
Require Import Types.Stores.
Require Import Types.State.
Require Import Types.Option.

Implicit Type A : Type.
Implicit Type M : Type → Type.

Section fail_option.
  Lemma none_left : ∀ A B (f : A → option B), bind_option (@None A) f = None.
  Proof.
    reflexivity.
  Qed.
      
  Global Instance fail_option : MonadFail option :=
  {
    fail := @None;
    fail_left := none_left;
  }.
End fail_option.

Instance fail_option_sound : MonadFail_sound option option.
Proof.
  intros A A' GA m'. constructor.
Qed.
Hint Resolve fail_option_sound : soundness.

Section fail_optionT.
  Context M `{MM : Monad M}.

  Definition fail_optionT {A} : optionT M A := returnM None.

  Lemma fail_optionT_left : ∀ (A B : Type) (m : A → optionT M B),
    fail_optionT >>= m = fail_optionT.
  Proof.
    intros A B m. unfold fail_optionT. 
    unfold bindM; simpl; unfold bind_op_optionT, bind_optionT. 
    rewrite bind_id_left. reflexivity.
  Qed.

  Global Instance monadfail_optionT : MonadFail (optionT M) := {
    fail_left := fail_optionT_left;
  }.
End fail_optionT.

Section fail_stateT.
  Context {M : Type -> Type} {RO : return_op M} `{MF : MonadFail M}.
  Context {S : Type}.

  Definition fail_stateT {A} : StateT S M A := 
    λ st, fail >>= λ a, returnM (a, st). 

  Lemma fail_stateT_left : ∀ (A B : Type) (f : A → StateT S M B),
    fail_stateT >>= f = fail_stateT.
  Proof.
    intros; unfold fail_stateT; extensionality s.
    rewrite fail_left. 
    unfold bindM at 1; simpl; unfold bind_op_stateT, bind_stateT. 
    repeat rewrite fail_left; reflexivity.
  Qed.

  Arguments fail_stateT [A].
  Global Instance monad_fail_stateT : MonadFail (StateT S M) :=
  {
    fail := fail_stateT;
    fail_left := fail_stateT_left;
  }.
End fail_stateT.

Instance monadfail_stateT_sound {M M'} 
  {RM : return_op M} {RM' : return_op M'}
  {BM : bind_op M} {BM' : bind_op M'}
  {MF : MonadFail M} {MF' : MonadFail M'}
  {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')}
  {S S'} {GS : Galois S S'}:
    MonadFail_sound M M' →
    MonadFail_sound (StateT S M) (StateT S' M').
Proof.
  intros MS A A' GA m'. unfold fail; simpl.
  unfold fail_stateT. intros st st' Hst.
  rewrite fail_left. apply fail_sound.
Qed.
Hint Resolve monadfail_stateT_sound : soundness.

Section fail_optionAT.
  Context {S : Type} {JS : Joinable S S} {JI : JoinableIdem JS}.

  Definition fail_optionAT {A} : optionAT (StateT S option) A := 
    fail >>= λ a, returnM (SomeA a).

  Lemma fail_optionAT_left : ∀ (A B : Type) 
    (f : A → optionAT (StateT S option) B),
    fail_optionAT >>= f = fail_optionAT.
  Proof.
    intros A B f. unfold fail_optionAT. repeat rewrite fail_left.
    easy.
  Qed.

  Global Instance monadfail_optionAT : MonadFail (optionAT (StateT S option)) :=
  {
    fail_left := fail_optionAT_left;
  }.
End fail_optionAT.

Instance monadfail_optionAT_sound {S S'} {JS : Joinable S S} 
  {JI : JoinableIdem JS} {GS : Galois S S'} :
    MonadFail_sound (optionAT (StateT S option)) (optionT (StateT S' option)).
Proof.
  intros A A' GA m'. 
  unfold fail; simpl; unfold fail_optionAT. 
  rewrite fail_left. 
  unfold fail; simpl; unfold fail_stateT.
  intros s s' Hs. 
  rewrite fail_left.
  constructor.
Qed.
Hint Resolve monadfail_optionAT_sound : soundness.
