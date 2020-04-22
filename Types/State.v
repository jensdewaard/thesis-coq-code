Require Export Base.
Require Import Utf8 Classes.Joinable Classes.Monad Classes.Galois
  Classes.Monad.MonadJoin.

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

  Definition bind_state {A B} 
    (m : State S A) (f : A -> State S B) : State S B :=
    λ st, let (x, st') := (m st) in f x st'.
  Arguments bind_state [A B] m f.
  Hint Unfold bind_state : monads.

  Lemma bind_state_id_left : ∀ (A B : Type) (f : A → State S B) (a : A),
    bind_state (return_state a) f = f a.
  Proof. simple_solve. Qed.

  Lemma bind_state_id_right : ∀ (A : Type) (m : State S A),
    bind_state m return_state = m.
  Proof. simple_solve. Qed.

  Lemma bind_state_assoc : ∀ (A B C : Type) (m : State S A) 
    (f : A → State S B) (g : B → State S C),
    bind_state (bind_state m f) g =
    bind_state m (λ a : A, bind_state (f a) g).
  Proof. simple_solve. Qed.

  Global Instance monad_state : Monad (State S) :=
  {
    bind_id_left := bind_state_id_left;
    bind_id_right := bind_state_id_right;
    bind_assoc := bind_state_assoc;
  }. 
End State_Monad.

Section Monad_StateT.
  Context {M} `{M_monad : Monad M}.
  Context {S : Type}.

  Definition return_stateT {A} (a : A) :=
    λ st : S, returnM (a, st).
  Hint Unfold return_stateT : monads.

  Definition bind_stateT {A B} (m : StateT S M A) 
    (f : A -> StateT S M B) : StateT S M B :=
    λ st, m st >>= λ p : (A*S)%type, let (a,st') := p in f a st'.
  Arguments bind_stateT [A B] m f.
  Hint Unfold bind_stateT : monads.

  Lemma bind_stateT_id_left : ∀ (A B : Type) (f : A → StateT S M B) (a : A), 
    bind_stateT (return_stateT a) f = f a.
  Proof.
    autounfold with monads. intros. ext. 
    rewrite bind_id_left. reflexivity.
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
    intros. autounfold with monads. ext.
    autorewrite with monads. f_equal. repeat rewrite bind_assoc. extensionality p.
    destruct p. reflexivity.
  Qed.
  Arguments bind_stateT_assoc [A B C] m f g.

  Global Instance monad_stateT : Monad (StateT S M) :=
  {
    bind_id_left := bind_stateT_id_left;
    bind_id_right := bind_stateT_id_right;
    bind_assoc := bind_stateT_assoc;
  }. 
End Monad_StateT.

Section mjoin_stateT.
  Context {S : Type} {JS: Joinable S S} {JSI : JoinableIdem JS}. 
  Context {M : Type → Type} {MM : Monad M} {JM : MonadJoin M}.

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
  {JSI : JoinableIdem JS} {M M' : Type → Type} {MM : Monad M} {MM' : Monad M'}
  {JM : MonadJoin M} {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')}
  {MS : MonadJoinSound M M'} :
  MonadJoinSound (StateT S M) (StateT S' M').
Proof. split; intros. 
  - intros ???. eapply mjoin_sound_left. apply H. assumption.
  - intros ???. apply mjoin_sound_right. apply H. assumption.
Qed.
Hint Resolve stateT_monadjoin_sound : soundness.

Instance stateT_joinable {S} {JS : Joinable S S} {M} {MM : Monad M}
  {JM : ∀ A B, Joinable A B → Joinable (M A) (M B)}
  {A B} {JA : Joinable A B} : Joinable (StateT S M A) (StateT S M B) :=
    λ m1, λ m2, λ st, (m1 st) ⊔ (m2 st).
Hint Resolve stateT_joinable : soundness.

Section joinsecond_state.
  Context {ST : Type} {JST : Joinable ST ST} {JI : JoinableIdem JST}.
    
  Definition joinsecond_state {A} (f : A → A) (m : State ST A) 
    : State ST A := m >>= λ a, returnM (f a).
  Arguments joinsecond_state [A].

  Lemma joinsecond_state_return : ∀ (A : Type) (f : A → A) (a : A),
  joinsecond_state f (return_state a) = 
  return_state (f a).
  Proof.
    intros. unfold joinsecond_state. unfold bindM; simpl; unfold bind_state.
    unfold return_state; simpl.
    ext. unfold returnM; simpl; unfold return_state.
    reflexivity.
  Qed.

  Lemma joinsecond_state_bind : ∀ (A B : Type) (f : A → A) (g : B → B)
    (m : State ST A) (k : A → State ST B),
  (∀ a, k (f a) = k a >>= (λ b, return_state (g b))) →
  joinsecond_state f m >>= k = joinsecond_state g (m >>= k).
  Proof. 
    intros. unfold joinsecond_state. extensionality s. 
    rewrite bind_assoc. rewrite bind_assoc. f_equal. ext.
    rewrite <- H. unfold bindM; simpl. unfold bind_state. 
    ext. unfold returnM; simpl; unfold return_state. reflexivity.
  Qed.

  Lemma joinsecond_state_compose : ∀ (A : Type) (f : A → A) (g : A → A)
    (m : State ST A),
  joinsecond_state (g ∘ f) m = joinsecond_state f (joinsecond_state g m).
  Proof.
    intros A f g m. unfold joinsecond_state, compose. rewrite bind_assoc.
    f_equal. 
  Qed.
End joinsecond_state.
Arguments joinsecond_state {ST} A.

Instance joinsecondable_state {S : Type} 
  {JS : Joinable S S} {JI : JoinableIdem JS} : joinsecondable (State S) :=
{
  joinsecond := joinsecond_state;
  joinsecond_return := joinsecond_state_return;
  joinsecond_bind := joinsecond_state_bind;
  joinsecond_compose := joinsecond_state_compose;
}.

Instance joinsecondable_state_sound {S S' : Type} 
  {JS : Joinable S S} {JS' : Joinable S' S'} 
  {JSI : JoinableIdem JS} {JSI' : JoinableIdem JS'} {GS : Galois S S'} :
  joinsecondable_sound (State S) (State S').
Proof.
  constructor. intros A A' GA f m m' Hf Hm. unfold joinsecond; simpl.
  unfold joinsecond_state. unfold bindM; simpl; unfold bind_state.
  unfold returnM; simpl; unfold return_state.
  intros s s' Hs. apply Hm in Hs. destruct (m s), (m' s'). 
  inversion Hs; subst. split; simpl in *; auto.
Qed.

Section joinsecond_stateT.
  Context {S : Type} {JS : Joinable S S} {JI : JoinableIdem JS}.
  Context {M : Type → Type} {MM : Monad M}.

  Definition joinsecond_stateT {A} 
    (f : A → A) (m : StateT S M A) : StateT S M A :=
    m >>= λ a, returnM (f a).
  Arguments joinsecond_stateT [A].

  Lemma joinsecond_stateT_return : ∀ (A : Type) (f : A → A) (a : A),
    joinsecond_stateT f (return_stateT a) = 
    return_stateT (f a).
  Proof.
    intros A f a. unfold joinsecond_stateT. 
    unfold bindM; simpl; unfold bind_stateT.
    unfold return_stateT; simpl. ext.
    rewrite bind_id_left. reflexivity. 
  Qed.

  Lemma joinsecond_stateT_bind : ∀ (A B : Type) (f : A → A) (g : B → B)
    (m : StateT S M A) (k : A → StateT S M B),
  (∀ a, k (f a) = k a >>= (λ b, return_stateT (g b))) →
  joinsecond_stateT f m >>= k = joinsecond_stateT g (m >>= k).
  Proof. 
    intros. unfold joinsecond_stateT. 
    unfold bindM; simpl. unfold bind_stateT. extensionality s.
    autorewrite with monads. f_equal. ext. destruct x.
    unfold returnM; simpl; unfold return_stateT.
    autorewrite with monads. rewrite H.  unfold bindM at 1; simpl.
    unfold bind_stateT, return_stateT. reflexivity.
  Qed.

  Lemma joinsecond_stateT_compose : ∀ (A : Type) (f g : A → A) 
    (m : StateT S M A),
    joinsecond_stateT (g ∘ f) m = joinsecond_stateT f (joinsecond_stateT g m).
  Proof.
    intros A f g m.
    unfold joinsecond_stateT. rewrite bind_assoc. f_equal. ext.
    unfold returnM, bindM; simpl; unfold return_stateT, bind_stateT; ext.
    autorewrite with monads. reflexivity. 
  Qed.

  Global Instance joinsecondable_stateT : joinsecondable (StateT S M) := {
    joinsecond := joinsecond_stateT;
    joinsecond_return := joinsecond_stateT_return;
    joinsecond_bind := joinsecond_stateT_bind;
    joinsecond_compose := joinsecond_stateT_compose;
  }.
End joinsecond_stateT.

Instance joinsecondable_stateT_sound {S S' : Type} 
  {JS : Joinable S S} {JSI : JoinableIdem JS} {GS : Galois S S'}
  {M M' : Type → Type} {MM : Monad M} {MM' : Monad M'}
  {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')} :
  return_sound M M' → bind_sound M M' →
  joinsecondable_sound (StateT S M) (StateT S' M').
Proof.
  intros RS BS;
  constructor; intros A A' GA f m m' Hf Hm. 
  unfold joinsecond; simpl; unfold joinsecond_stateT.
  intros s s' Hs. 
  unfold bindM; simpl; unfold bind_stateT.
  apply Hm in Hs. rewrite <- bind_id_right. apply bindM_sound. apply Hs.
  intros a a' Ha; destruct a. apply returnM_sound. 
  destruct a'. inversion Ha; subst.
  split; simpl; auto. 
Qed.
    
