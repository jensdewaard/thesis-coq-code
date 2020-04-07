Require Export Base.
Require Import Utf8 Classes.Joinable Classes.Monad Classes.Galois.

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
  Context {S A} `{S_joinable : Joinable S S, A_joinable : Joinable A A}.

  Global Instance state_joinable : Joinable (State S A) (State S A) :=
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
  Hint Unfold bind_state : soundness.

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
Hint Unfold bind_state : soundness.

Section Monad_StateT.
  Context {M} `{M_monad : Monad M}.
  Context {S : Type}.

  Definition return_stateT {A} (a : A) :=
    λ st : S, returnM (a, st).
  Hint Unfold return_stateT : soundness.

  Definition bind_stateT {A B} (m : StateT S M A) 
    (f : A -> StateT S M B) : StateT S M B :=
    λ st, m st >>= λ p : (A*S)%type, let (a,st') := p in f a st'.
  Arguments bind_stateT [A B] m f.
  Hint Unfold bind_stateT : soundness.

  Lemma bind_stateT_id_left : ∀ (A B : Type) (f : A → StateT S M B) (a : A), 
    bind_stateT (return_stateT a) f = f a.
  Proof.
    autounfold with soundness. intros. ext. 
    rewrite bind_id_left. reflexivity.
  Qed.
  Arguments bind_stateT_id_left [A B] f a.

  Lemma bind_stateT_id_right : ∀ (A : Type) (m : StateT S M A), 
    bind_stateT m return_stateT = m.
  Proof.
    intros. autounfold with soundness. ext.
    rewrite <- bind_id_right. f_equal. ext. destruct x0.
    reflexivity.
  Qed.
  Arguments bind_stateT_id_right [A] m.

  Lemma bind_stateT_assoc : ∀ (A B C : Type) (m : StateT S M A) 
    (f : A → StateT S M B) (g : B → StateT S M C),
    bind_stateT (bind_stateT m f) g =
    bind_stateT m (λ a : A, bind_stateT (f a) g).
  Proof.
    intros. autounfold with soundness. ext.
    autorewrite with soundness. f_equal. extensionality p.
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
Hint Unfold bind_stateT : soundness.

Section MonadT_StateT.
  Context {S : Type}.

  Definition lift_stateT {M} `{Monad M} {A} (m : M A) : StateT S M A :=
    λ st, m >>= λ a, returnM (a, st).
  Hint Unfold lift_stateT : soundness.
  
  Lemma lift_stateT_pure {M} `{Monad M} {A} : ∀ (a : A), 
    lift_stateT (returnM a) = return_stateT a.
  Proof.
    intros. autounfold with soundness. ext.
    autorewrite with soundness. reflexivity.
  Qed.

  Lemma lift_stateT_bind {M} `{Monad M} {A B} : ∀ (m : M A) (f : A → M B),
    lift_stateT (m >>= f) = bind_stateT (lift_stateT m) (f ∘ lift_stateT (A:=B)).
  Proof.
    intros. simpl.
    autounfold with soundness. ext. autorewrite with soundness.
    f_equal. ext. autorewrite with soundness. reflexivity.
  Qed.

  Global Instance monadT_stateT : MonadT (StateT S) :=
  {
    lift_return := @lift_stateT_pure;
    lift_bind := @lift_stateT_bind;
  }. 
End MonadT_StateT.
