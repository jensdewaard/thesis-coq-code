Require Export Base.
Require Import Utf8 Classes.Joinable Classes.Monad Classes.Galois
  Classes.Monad.MonadJoin Classes.PreorderedSet.

Definition StateT S M A : Type := S → M (A*S)%type.
Definition State (S A : Type) := StateT S Identity A.

Class SType (S : Type) {PS : PreorderedSet S} {JS : Joinable S S} :=
{
  S_le_refl : ∀ s, s ⊑ s;
}.

Instance galois_stateT {M M' : Type → Type} 
  {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')}
  {S S'} {GS : Galois S S'} : 
  ∀ A A', Galois A A' → Galois (StateT S M A) (StateT S' M' A').
Proof.
  intros A A' GA. unfold StateT. apply galois_fun. apply GS.
  apply GM. apply galois_pairs; assumption.
Defined.

Section Monad_StateT.
  Context {M} `{MM : Monad M}.
  Context {S : Type} `{SType S}.

  Definition return_stateT {A} (a : A) :=
    λ st : S, returnM (a, st).
  Hint Unfold return_stateT : monads.
  Global Instance return_op_stateT : return_op (StateT S M) := @return_stateT.

  Definition bind_stateT {A B} (m : StateT S M A) 
    (f : A -> StateT S M B) : StateT S M B :=
    λ st, m st >>= λ p : (A*S)%type, let (a,st') := p in f a st'.
  Arguments bind_stateT [A B] m f.
  Hint Unfold bind_stateT : monads.
  Global Instance bind_op_stateT : bind_op (StateT S M) := @bind_stateT.

  Lemma bind_stateT_id_left : ∀ (A B : Type) (f : A → StateT S M B) (a : A), 
    bind_stateT (return_stateT a) f = f a.
  Proof.
    intros; unfold bind_stateT, return_stateT; extensionality s.
    rewrite bind_id_left; reflexivity.
  Qed.
  Arguments bind_stateT_id_left [A B] f a.

  Lemma bind_stateT_id_right : ∀ (A : Type) (m : StateT S M A), 
    bind_stateT m return_stateT = m.
  Proof.
    intros. autounfold with monads. ext.
    rewrite <- bind_id_right. f_equal. ext. destruct x0.
    reflexivity.
  Qed.
  Arguments bind_stateT_id_right [A] m.

  Lemma bind_stateT_assoc : ∀ (A B C : Type) (m : StateT S M A) 
    (f : A → StateT S M B) (g : B → StateT S M C),
    bind_stateT (bind_stateT m f) g =
    bind_stateT m (λ a : A, bind_stateT (f a) g).
  Proof.
    intros; unfold bind_stateT; extensionality s.
    rewrite bind_assoc; f_equal; extensionality p.
    destruct p; reflexivity.
  Qed.
  Arguments bind_stateT_assoc [A B C] m f g.

  Global Instance monad_stateT : Monad (StateT S M) :=
  {
    bind_id_left := bind_stateT_id_left;
    bind_id_right := bind_stateT_id_right;
    bind_assoc := bind_stateT_assoc;
  }. 
  
  Definition bind2_stateT {A B} (m : StateT S M A)
      (f : A → StateT S M B) : StateT S M B :=
      λ st : S, 
        m st >>= λ p, let (a, st') := p : (A*S)%type  in f a (st ⊔ st').

  Instance bind2_stateT_op : bind2_op (StateT S M) := @bind2_stateT.
End Monad_StateT.


Section stateT_sound.
  Context (M M' : Type → Type) `{MM : Monad M} `{MM' : Monad M'}.
  Context {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')}.
  Context {S S' : Type} {GS : Galois S S'}.
  Context {RS : return_sound M M'}.
  Context {BS : bind_sound M M'}.

  Global Instance return_stateT_sound : 
    return_sound (StateT S M) (StateT S' M').
  Proof.
    unfold return_sound, returnM; simpl.
    unfold return_op_stateT, return_stateT. 
    intros A A' GA a a' Ha s s' Hs; eauto with soundness.
  Qed.

  Global Instance bind_stateT_sound : bind_sound (StateT S M) (StateT S' M').
  Proof.
    unfold bind_sound, bindM; simpl; unfold bind_stateT; intros.
    intros s s' Hs. apply bindM_sound; eauto with soundness.
    intros p q Hpq. destruct p, q; eauto with soundness. 
    gamma_destruct; simpl in *.
    apply H0; assumption.
  Qed.
End stateT_sound.
Hint Resolve return_stateT_sound bind_stateT_sound : soundness.

Section mjoin_stateT.
  Context {S : Type} {JS: Joinable S S} {JSI : JoinableIdem JS}. 
  Context {M : Type → Type} `{MM : Monad M} {JM : MonadJoin M}.

  Definition mjoin_stateT {A : Type} {JA : Joinable A A} {JI : JoinableIdem JA}
    (m1 m2 : StateT S M A) : StateT S M A := λ s : S, (m1 s) <⊔> (m2 s).

  Lemma mjoin_stateT_return : ∀ (A : Type) {JA : Joinable A A} 
    {JAI : JoinableIdem JA} (x y : A),
    mjoin_stateT (return_stateT x) (return_stateT y) = 
    return_stateT (x ⊔ y).
  Proof.
    intros A JA JAI x y. unfold mjoin_stateT. unfold return_stateT. ext.
    rewrite mjoin_return. unfold join_op. unfold pair_joinable; simpl.
    rewrite JSI. reflexivity.
  Qed.

  Global Instance stateT_monadjoin : MonadJoin (StateT S M) :=
  {
    mjoin := @mjoin_stateT;
    mjoin_return := mjoin_stateT_return;
  }.
End mjoin_stateT.
Hint Resolve stateT_monadjoin : soundness.

Instance stateT_monadjoin_sound {S S'} {JS : Joinable S S} {GS : Galois S S'}
  {JSS : JoinableSound JS}
  {JSI : JoinableIdem JS} {M M' : Type → Type} `{MM : Monad M} `{MM' : Monad M'}
  {JM : MonadJoin M} {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')}
  {MS : MonadJoinSound M M'} :
  MonadJoinSound (StateT S M) (StateT S' M').
Proof. split; intros. 
  - intros ???. eapply mjoin_sound_left. apply H. assumption.
  - intros ???. apply mjoin_sound_right. apply H. assumption.
Qed.
Hint Resolve stateT_monadjoin_sound : soundness.

Instance stateT_joinable {S} {JS : Joinable S S} {M} `{MM : Monad M}
  {JM : ∀ A B, Joinable A B → Joinable (M A) (M B)}
  {A B} {JA : Joinable A B} : Joinable (StateT S M A) (StateT S M B) :=
    λ m1, λ m2, λ st, (m1 st) ⊔ (m2 st).
Hint Resolve stateT_joinable : soundness.

