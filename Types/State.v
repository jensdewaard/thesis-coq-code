Require Export Base.
Require Import Utf8 Classes.Joinable Classes.Monad Classes.Galois
  Classes.Monad.MonadJoin Classes.PreorderedSet.

Definition State (S A : Type) := S -> (A * S).
Definition StateT S M A : Type := S → M (A*S)%type.

Definition gamma_state {S S'} {GS : Galois S S'} {A A'} {GA : Galois A A'} : 
  State S A → State S' A' → Prop := λ s : State S A, λ s' : State S' A', 
    ∀ st st', γ st st' → γ (s st) (s' st').
Arguments gamma_state {S S' GS} A A' GA.

Instance galois_state {S S'} {GS : Galois S S'} : 
  ∀ A A', Galois A A' → Galois (State S A) (State S' A') := gamma_state.

Instance galois_stateT {M M' : Type → Type} 
  {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')}
  {S S'} {GS : Galois S S'} : 
  ∀ A A', Galois A A' → Galois (StateT S M A) (StateT S' M' A').
Proof.
  intros A A' GA. unfold StateT. apply galois_fun. apply GS.
  apply GM. apply galois_pairs; assumption.
Defined.

Section state_joinable.
  Context {S} {JS : Joinable S S}.
  Context {A B} {JA : Joinable A B}.

  Global Instance state_joinable : Joinable (State S A) (State S B) :=
    λ st, λ st',  
    λ x, (((fst (st x)) ⊔ (fst (st' x)), 
              ((snd (st x)) ⊔ (snd (st' x))))).
End state_joinable.

Section State_Monad.
  Context {S : Type}.

  Definition return_state {A} (a :A) : State S A := 
    λ st : S, (a, st).
  Global Instance return_op_state : return_op (State S) := @return_state.

  Definition bind_state {A B} 
    (m : State S A) (f : A -> State S B) : State S B :=
    λ st, let (x, st') := (m st) in f x st'.
  Arguments bind_state [A B] m f.
  Hint Unfold bind_state : monads.
  Global Instance bind_op_state : bind_op (State S) := @bind_state.

  Lemma bind_state_id_left : ∀ (A B : Type) (f : A → State S B) (a : A),
    bind_state (return_state a) f = f a.
  Proof. easy. Qed.

  Lemma bind_state_id_right : ∀ (A : Type) (m : State S A),
    bind_state m return_state = m.
  Proof. 
    intros; unfold bind_state, return_state; extensionality s.
    destruct (m s); reflexivity.
  Qed.

  Lemma bind_state_assoc : ∀ (A B C : Type) (m : State S A) 
    (f : A → State S B) (g : B → State S C),
    bind_state (bind_state m f) g =
    bind_state m (λ a : A, bind_state (f a) g).
  Proof. 
    intros; unfold bind_state, return_state; extensionality s.
    destruct (m s) as [a s'], (f a s'); reflexivity.
  Qed.

  Global Instance monad_state : Monad (State S) :=
  {
    bind_id_left := bind_state_id_left;
    bind_id_right := bind_state_id_right;
    bind_assoc := bind_state_assoc;
  }. 
End State_Monad.

Definition state_le {S} {PS : PreorderedSet S} {A} {PA : PreorderedSet A} 
  (m m' : State S A) : Prop :=
  ∀ s s', s ⊑ s' -> m s ⊑ m' s'.

Lemma state_le_refl {S} {PS : PreorderedSet S} {A} {PA : PreorderedSet A} :
  ∀ m : State S A, state_le m m.
Proof.
  unfold state_le; intros m s s' Hs.
  (* need monotone m *)
Admitted.

Lemma state_le_trans {S} {PS : PreorderedSet S} {A} {PA : PreorderedSet A} :
  ∀ x y z : State S A,
  state_le x y →
  state_le y z →
  state_le x z.
Proof.
  unfold state_le; intros x y z Hxy Hyz s s' Hs.
  apply preorder_trans with (y s).
  + apply Hxy; apply preorder_refl.
  + apply Hyz; apply Hs.
Qed.

(*
Instance state_preordered {S} {PS : PreorderedSet S} :
  ∀ A, PreorderedSet A -> PreorderedSet (State S A) :=
{
  preorder := state_le;
  preorder_refl := state_le_refl;
  preorder_trans := state_le_trans;
}.

Instance state_ordered {S} {PS : PreorderedSet S} : OrderedMonad (State S).
Proof. split.
  - intros A PA a1 a2 Ha. unfold returnM, return_op_state, return_state.
    intros s s' Hs; constructor; assumption.
  - intros A B PA PB m m' f f' Hm Hf Hff' s s' Hs.
    unfold bindM, bind_op_state, bind_state. 
    apply Hm in Hs.
    destruct (m s) as [a s2], (m' s') as [a' s2'].
    inversion Hs as [????  Ha Hs2]; subst; clear Hs.
    assert (state_le (f a) (f' a')).
    { eapply state_le_trans. apply Hf. apply Ha. apply Hff'. }
    apply H. apply Hs2.
Qed.
*)

Instance state_ordered {S} {PS : PreorderedSet S} : OrderedMonad (State S).
Proof. split.
  - intros A PA a1 a2 Ha; constructor; intros s.
    constructor.
    + assumption.
    + apply preorder_refl.
  - intros A B PA PB m m' f f' Hm Hf Hf'; constructor; intros s.
    unfold bindM, bind_op_state, bind_state. 
    assert (m s ⊑ m' s) as Hms.
    { destruct Hm; auto. }
    destruct (m s) as [a s2], (m' s) as [a' s2'].
    inversion Hms; subst.
    assert (f a ⊑ f' a').
    { eapply preorder_trans. apply Hf. apply H2. apply Hf'. }
    inversion H; subst.
    assert (f a s2 ⊑ f' a' s2). 
    { apply H0. }
    eapply preorder_trans. apply H1.
    assert (monotone (f' a')). admit.
    apply H3. apply H4.
Admitted.

Instance return_state_sound {S S' : Type} {GS : Galois S S'} : 
  return_sound (State S) (State S').
Proof.
  unfold return_sound; unfold returnM; simpl; intros; unfold return_state.
  constructor; simpl; eauto with soundness. 
Qed.
Hint Resolve return_state_sound : soundness.

Instance bind_state_sound {S S' : Type} {GS : Galois S S'} :
  bind_sound (State S) (State S').
Proof.
  unfold bind_sound, bindM; simpl; intros A A' B b' GA GB m m' f f' Hm Hf. 
  unfold bind_op_state, bind_state; intros s s' Hs. 
  apply Hm in Hs.
  destruct (m s), (m' s'). 
  inversion Hs; subst; clear Hs; simpl in *.
  apply Hf; assumption.
Qed.
Hint Resolve bind_state_sound : soundness.

Section Monad_StateT.
  Context {M} `{MM : Monad M}.
  Context {S : Type}.

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
End Monad_StateT.

Section stateT.
  Context (M M' : Type → Type) `{MM : Monad M} `{MM' : Monad M'}.
  Context {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')}.
  Context {S S' : Type} {GS : Galois S S'}.
  Context {RS : return_sound M M'}.
  Context {BS : bind_sound M M'}.

  Global Instance return_stateT_sound : 
    return_sound (StateT S M) (StateT S' M').
  Proof.
    unfold return_sound, returnM; simpl.
    unfold return_op_stateT, return_state. 
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
End stateT.
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
