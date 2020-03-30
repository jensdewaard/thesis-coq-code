Require Export Base.
Require Export Classes.Monad.
Require Import Classes.Joinable.
Require Import Classes.JoinableMonad.
Require Import Classes.PreorderedSet.
Require Import Coq.Program.Basics.
Require Import FunctionalExtensionality.
Require Import Language.Statements.
Require Import Types.Maps.
Require Import Types.State.
Require Import Instances.Joinable.
Require Import Instances.Preorder.

Implicit Type S A B C : Type.
Implicit Type M : Type → Type.

Section Identity_Monad.
  Definition bind_id {A B} 
    (m : Identity A) (f : A → Identity B) : Identity B := 
      match m with
      | identity a => f a
      end.
  
  Lemma bind_id_id_left : ∀ (A B : Type) (f : A → Identity B) (a : A),
    bind_id (identity a) f = f a.
  Proof.
    reflexivity.
  Qed.

  Lemma bind_id_id_right : ∀ (A : Type) (m : Identity A),
    bind_id m identity = m.
  Proof.
    intros. destruct m. reflexivity.
  Qed.

  Lemma bind_id_assoc : ∀ (A B C : Type) (m : Identity A)
    (f : A → Identity B) (g : B → Identity C),
    bind_id (bind_id m f) g = bind_id m (λ a : A, bind_id (f a) g).
  Proof.
    intros. destruct m; simpl. reflexivity.
  Qed.

  Lemma identity_inj : ∀ A (x y : A),
    identity x = identity y → x = y.
  Proof.
    intros A x y H. inversion H. reflexivity.
  Qed.

  Global Instance monad_identity : Monad Identity :=
  {
    bind_id_left := bind_id_id_left;
    bind_id_right := bind_id_id_right;
    bind_assoc := bind_id_assoc;
  }.
End Identity_Monad.

Section option_monad.
  Definition bind_option {A B} 
    (m : option A) (f : A -> option B) : option B :=
    match m with
    | None => None
    | Some a => f a
    end.
  Hint Unfold bind_option : soundness.

  Lemma bind_option_id_left : ∀ {A B} (f : A → option B) (a : A), 
    bind_option (Some a) f = f a.
  Proof. simple_solve. Qed.
  Arguments bind_option_id_left [A B] f a.

  Lemma bind_option_id_right : ∀ {A} (m : option A), 
    bind_option m Some = m.
  Proof. simple_solve. Qed.
  Arguments bind_option_id_right [A] m.

  Lemma bind_option_assoc : ∀ {A B C} (m : option A) 
    (f : A → option B) (g : B → option C),
  bind_option (bind_option m f) g = bind_option m (λ a : A, bind_option (f a) g).
  Proof. simple_solve. Qed.
  Arguments bind_option_assoc [A B C] m f g.

  Global Instance option_monad : Monad option :=
  {
    bind_id_left := bind_option_id_left;
    bind_id_right := bind_option_id_right;
    bind_assoc := bind_option_assoc;
  }. 
End option_monad.
Hint Rewrite @bind_option_id_left @bind_option_id_right : soundness.

Section optionA_monad.
  Definition bind_optionA {A B : Type}
    (m : optionA A) (f : A -> optionA B) : optionA B :=
    match m with
    | NoneA => NoneA
    | SomeA a => f a
    | SomeOrNoneA a => match (f a) with
                       | NoneA => NoneA
                       | SomeA b => SomeOrNoneA b
                       | SomeOrNoneA b => SomeOrNoneA b
                       end
    end.
  Arguments bind_optionA [_ _].
  Hint Unfold bind_optionA : soundness.

  Lemma bind_optionA_id_left : ∀ {A B} (f : A → optionA B) (a : A),
  bind_optionA (SomeA a) f = f a.
  Proof. simple_solve. Qed.
  Arguments bind_optionA_id_left [A B] f a.

  Lemma bind_optionA_id_right :  ∀ {A} (m : optionA A),
    bind_optionA m SomeA = m.
  Proof. solve_monad. Qed.
  Arguments bind_optionA_id_right [A].

  Lemma bind_optionA_assoc : ∀ {A B C} (m : optionA A) 
    (f : A → optionA B) (g : B → optionA C),
    bind_optionA (bind_optionA m f) g =
    bind_optionA m (λ a : A, bind_optionA (f a) g).
  Proof. solve_monad. Qed.
  Arguments bind_optionA_assoc [A B C] m f g.

  Global Instance optionA_monad : Monad optionA :=
  {
    bind_id_left := bind_optionA_id_left;
    bind_id_right := bind_optionA_id_right;
    bind_assoc := bind_optionA_assoc;
  }. 
End optionA_monad.
Hint Rewrite @bind_optionA_id_left @bind_optionA_id_right : soundness.

Section optionT_Monad.
  Context {M} `{M_monad : Monad M}.

  Definition bind_optionT {A B} (m : optionT M A) 
    (f : A -> optionT M B) : optionT M B :=
    bindM (M:=M) m (λ v : option A,
      match v with
      | None => (returnM None)
      | Some a => f a
      end).
  Arguments bind_optionT [A B] m f.
  Hint Unfold bind_optionT : soundness.

  Lemma bind_optionT_id_left : ∀ {A B} (f : A → optionT M B) (a : A), 
    bind_optionT (returnM (M:=M) (Some a)) f = f a.
  Proof. 
    intros. unfold bind_optionT.
    rewrite bind_id_left. reflexivity.
  Qed.
  Arguments bind_optionT_id_left [A B] f a.

  Lemma bind_optionT_id_right : ∀ {A} (m : optionT M A),
    bind_optionT m (λ a, returnM (M:=M) (Some a)) = m.
  Proof. 
    intros. unfold bind_optionT.
    rewrite <- (bind_id_right (M:=M)). f_equal. 
    ext; destruct x; reflexivity.
  Qed.
  Arguments bind_optionT_id_right [A] m.

  Lemma bind_optionT_assoc : ∀ {A B C} (m : optionT M A) 
    (f : A → optionT M B) (g : B → optionT M C),
    bind_optionT (bind_optionT m f) g =
    bind_optionT m (λ a : A, bind_optionT (f a) g).
  Proof. 
    intros. unfold bind_optionT. autorewrite with soundness.
    f_equal. ext. destruct x; eauto with soundness.
    autorewrite with soundness. reflexivity.
  Qed.
  Arguments bind_optionT_assoc [A B C] m f g.

  Global Instance monad_optionT : Monad (optionT M) :=
  {
    bind_id_left := bind_optionT_id_left;
    bind_id_right := bind_optionT_id_right;
    bind_assoc := bind_optionT_assoc;
  }. 
End optionT_Monad.
Hint Unfold bind_optionT : soundness.
Hint Rewrite @bind_optionT_id_left @bind_optionT_id_right : soundness.

Section optionT_monadT.
  Definition lift_optionT {M : Type → Type} `{Monad M} {A} (m : M A) : optionT M A :=
    bindM (M:=M) m (λ a, returnM (Some a)).
  Hint Unfold lift_optionT : soundness.

  Lemma lift_optionT_pure {M : Type → Type} `{Monad M} : ∀ {A : Type} (a : A),
    lift_optionT (returnM (M:=M) a) = returnM (M:=M) (Some a).
  Proof. 
    intros. unfold lift_optionT. 
    rewrite bind_id_left. reflexivity.
  Qed.

  Lemma lift_optionT_bind {M : Type → Type} `{Monad M} : 
    ∀ (A B : Type) (m : M A) (f : A → M B),
  lift_optionT (m >>= f) = bind_optionT (lift_optionT m) (f ∘ (lift_optionT (A:=B))).
  Proof. 
    intros. unfold lift_optionT, bind_optionT.
    autorewrite with soundness. f_equal; ext. autorewrite with soundness.
    reflexivity.
  Qed.

  Global Instance monadT_optionT : MonadT (optionT) :=
  {
    lift_return := @lift_optionT_pure;
    lift_bind := @lift_optionT_bind;
  }. 
End optionT_monadT.

Section optionAT_monad.
  Context {M} `{M_monad : Monad M}.

  Definition bind_optionAT {A B} 
    (Mma : optionAT M A)
    (f : A -> optionAT M B) : optionAT M B :=
  bindM (M:=M) Mma (fun ma =>
    match ma with
    | NoneA => returnM NoneA
    | SomeA a => f a
    | SomeOrNoneA a => (
        bindM (M:=M) (f a) (fun mfa =>
                       match mfa with
                       | NoneA => returnM NoneA
                       | SomeA b => returnM (SomeOrNoneA b)
                       | SomeOrNoneA b => returnM (SomeOrNoneA b)
                       end))
    end).
  Hint Unfold bind_optionAT : soundness.

  Lemma bind_optionAT_id_left : ∀ {A B} (f : A → optionAT M B) (a : A), 
    bind_optionAT (returnM (M:=M) (SomeA a)) f = f a.
  Proof. 
    unfold bind_optionAT; simpl. intros.
    rewrite bind_id_left. reflexivity.
  Qed.
  Arguments bind_optionAT_id_left [A B] f a.

  Lemma bind_optionAT_id_right : ∀ (A : Type) (m : optionAT M A), 
    bind_optionAT m (λ a, returnM (M:=M) (SomeA a))= m.
  Proof. 
    unfold bind_optionAT.  intros. rewrite <- (bind_id_right (M:=M)).
    f_equal; extensionality x. 
    destruct x; autorewrite with soundness; try reflexivity.
  Qed.

  Lemma bind_optionAT_assoc : ∀ {A B C} (m : optionAT M A) 
    (f : A → optionAT M B) (g : B → optionAT M C),
    bind_optionAT (bind_optionAT m f) g =
    bind_optionAT m (λ a : A, bind_optionAT (f a) g).
  Proof. 
    intros. unfold bind_optionAT. autorewrite with soundness.
    f_equal; ext. destruct x; simpl. 
    1-2: autorewrite with soundness; reflexivity.
    autorewrite with soundness. f_equal; ext.
    destruct x; autorewrite with soundness. 
    f_equal. reflexivity. f_equal; ext.
    destruct x; autorewrite with soundness; reflexivity.
  Qed.
  Arguments bind_optionAT_assoc [A B C] m f g.

  Global Instance monad_optionAT : Monad (optionAT M) :=
  {
    bind_id_left := bind_optionAT_id_left;
    bind_id_right := bind_optionAT_id_right;
    bind_assoc := bind_optionAT_assoc;
  }. 
End optionAT_monad.
Hint Unfold bind_optionAT : soundness.

Section optionAT_MonadT.
  Definition lift_optionAT {M} `{Monad M} {A} (m : M A) : optionAT M A :=
    bindM (M:=M) m (λ a, returnM (M:=M) (SomeA a)).
  Hint Unfold lift_optionAT : soundness.

  Definition lift_optionAT_pure {M} `{Monad M} {A} : ∀ (a : A),
    lift_optionAT (returnM a) = returnM a.
  Proof. solve_monad. Qed.

  Definition lift_optionAT_bind {M} `{Monad M} {A B}: ∀ (m : M A) (f : A → M B),
    lift_optionAT (m >>= f) = bind_optionAT (lift_optionAT m) (f ∘ lift_optionAT (A:=B)).
  Proof. 
    unfold lift_optionAT, bind_optionAT. intros.
    autorewrite with soundness. f_equal; ext. autorewrite with soundness.
    reflexivity.
  Qed.

  Global Instance monadT_optionAT : MonadT optionAT :=
  {
    lift_return := @lift_optionAT_pure;
    lift_bind := @lift_optionAT_bind;
  }. 
End optionAT_MonadT.

Section State_Monad.
  Context {S : Type} `{S_joinable : Joinable S}.

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
