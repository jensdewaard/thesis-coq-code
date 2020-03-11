Require Export Base.
Require Export Classes.Monad.
Require Import Classes.Joinable.
Require Import Classes.JoinableMonad.
Require Import Classes.PreorderedSet.
Require Import Coq.Program.Basics.
Require Import FunctionalExtensionality.
Require Import Language.Statements.
Require Import Types.Maps.
Require Import Types.Maybe.
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

Section Maybe_Monad.
  Definition bind_maybe {A B} 
    (m : Maybe A) (f : A -> Maybe B) : Maybe B :=
    match m with
    | None => None
    | Just a => f a
    end.
  Arguments bind_maybe [A B].
  Hint Unfold bind_maybe : soundness.

  Lemma bind_maybe_id_left : ∀ {A B} (f : A → Maybe B) (a : A), 
    bind_maybe (Just a) f = f a.
  Proof. simple_solve. Qed.
  Arguments bind_maybe_id_left [A B] f a.

  Lemma bind_maybe_id_right : ∀ {A} (m : Maybe A), 
    bind_maybe m Just = m.
  Proof. simple_solve. Qed.
  Arguments bind_maybe_id_right [A].

  Lemma bind_maybe_assoc : ∀ {A B C} (m : Maybe A) 
    (f : A → Maybe B) (g : B → Maybe C),
  bind_maybe (bind_maybe m f) g = bind_maybe m (λ a : A, bind_maybe (f a) g).
  Proof. simple_solve. Qed.
  Arguments bind_maybe_assoc [A B C] m f g.

  Global Instance monad_maybe : Monad Maybe :=
  {
    bind_id_left := bind_maybe_id_left;
    bind_id_right := bind_maybe_id_right;
    bind_assoc := bind_maybe_assoc;
  }. 
End Maybe_Monad.
Hint Rewrite @bind_maybe_id_left @bind_maybe_id_right : soundness.

Section AbstractMaybe_Monad.
  Definition bind_maybeA {A B : Type}
    (m : AbstractMaybe A) (f : A -> AbstractMaybe B) : AbstractMaybe B :=
    match m with
    | NoneA => NoneA
    | JustA a => f a
    | JustOrNoneA a => match (f a) with
                       | NoneA => NoneA
                       | JustA b => JustOrNoneA b
                       | JustOrNoneA b => JustOrNoneA b
                       end
    end.
  Arguments bind_maybeA [_ _].
  Hint Unfold bind_maybeA : soundness.

  Lemma bind_maybeA_id_left : ∀ {A B} (f : A → AbstractMaybe B) (a : A),
  bind_maybeA (JustA a) f = f a.
  Proof. simple_solve. Qed.
  Arguments bind_maybeA_id_left [A B] f a.

  Lemma bind_maybeA_id_right :  ∀ {A} (m : AbstractMaybe A),
    bind_maybeA m JustA = m.
  Proof. solve_monad. Qed.
  Arguments bind_maybeA_id_right [A].

  Lemma bind_maybeA_assoc : ∀ {A B C} (m : AbstractMaybe A) 
    (f : A → AbstractMaybe B) (g : B → AbstractMaybe C),
    bind_maybeA (bind_maybeA m f) g =
    bind_maybeA m (λ a : A, bind_maybeA (f a) g).
  Proof. solve_monad. Qed.
  Arguments bind_maybeA_assoc [A B C] m f g.

  Global Instance monad_abstract_maybe : Monad AbstractMaybe :=
  {
    bind_id_left := bind_maybeA_id_left;
    bind_id_right := bind_maybeA_id_right;
    bind_assoc := bind_maybeA_assoc;
  }. 
End AbstractMaybe_Monad.
Hint Rewrite @bind_maybeA_id_left @bind_maybeA_id_right : soundness.

Section MaybeT_Monad.
  Context {M} `{M_monad : Monad M}.

  Definition bind_maybeT {A B} (m : MaybeT M A) 
    (f : A -> MaybeT M B) : MaybeT M B :=
    bindM (M:=M) m (λ v : Maybe A,
      match v with
      | None => NoneT
      | Just a => f a
      end
    ).
  Arguments bind_maybeT [A B] m f.
  Hint Unfold bind_maybeT : soundness.

  Lemma bind_maybeT_id_left : ∀ {A B} (f : A → MaybeT M B) (a : A), 
    bind_maybeT (JustT a) f = f a.
  Proof. 
    intros. unfold bind_maybeT, JustT. 
    rewrite bind_id_left. reflexivity.
  Qed.
  Arguments bind_maybeT_id_left [A B] f a.

  Lemma bind_maybeT_id_right : ∀ {A} (m : MaybeT M A),
    bind_maybeT m JustT = m.
  Proof. 
    intros. unfold bind_maybeT, NoneT, JustT. 
    rewrite <- (bind_id_right (M:=M)). f_equal. 
    ext; destruct x; reflexivity.
  Qed.
  Arguments bind_maybeT_id_right [A] m.

  Lemma bind_maybeT_assoc : ∀ {A B C} (m : MaybeT M A) 
    (f : A → MaybeT M B) (g : B → MaybeT M C),
    bind_maybeT (bind_maybeT m f) g =
    bind_maybeT m (λ a : A, bind_maybeT (f a) g).
  Proof. 
    intros. unfold bind_maybeT. autorewrite with soundness.
    f_equal. ext. destruct x; eauto with soundness.
    unfold NoneT. autorewrite with soundness. reflexivity.
  Qed.
  Arguments bind_maybeT_assoc [A B C] m f g.

  Global Instance monad_maybeT : Monad (MaybeT M) :=
  {
    bind_id_left := bind_maybeT_id_left;
    bind_id_right := bind_maybeT_id_right;
    bind_assoc := bind_maybeT_assoc;
  }. 
End MaybeT_Monad.
Hint Unfold bind_maybeT : soundness.
Hint Rewrite @bind_maybeT_id_left @bind_maybeT_id_right : soundness.

Section MaybeT_MonadT.
  Context {M} `{M_monad : Monad M}.
  
  Definition lift_maybeT {A} (m : M A) : MaybeT M A :=
    bindM (M:=M) m (λ a, JustT a).
  Arguments lift_maybeT [_] _.
  Hint Unfold lift_maybeT : soundness.

  Lemma lift_maybeT_pure : ∀ (A : Type) (a : A),
    lift_maybeT (returnM a) = returnM a.
  Proof. solve_monad. Qed.

  Lemma lift_maybeT_bind : ∀ (A B : Type) (m : M A) (f : A → M B),
  lift_maybeT (m >>= f) = bind_maybeT (lift_maybeT m) (f ∘ (lift_maybeT (A:=B))).
  Proof. 
    intros. unfold lift_maybeT, bind_maybeT, NoneT, JustT. 
    autorewrite with soundness. f_equal; ext. autorewrite with soundness.
    reflexivity.
  Qed.

  Global Instance monadT_maybeT : MonadT (MaybeT) :=
  {
    lift_return := lift_maybeT_pure;
    lift_bind := lift_maybeT_bind;
  }. 
End MaybeT_MonadT.

Section MaybeAT_Monad.
  Context {M} `{M_monad : Monad M}.

  Definition bind_maybeAT {A B} 
    (Mma : MaybeAT M A)
    (f : A -> MaybeAT M B) : MaybeAT M B :=
  bindM (M:=M) Mma (fun ma =>
    match ma with
    | NoneA => returnM NoneA
    | JustA a => f a
    | JustOrNoneA a => (
        bindM (M:=M) (f a) (fun mfa =>
                       match mfa with
                       | NoneA => returnM NoneA
                       | JustA b => returnM (JustOrNoneA b)
                       | JustOrNoneA b => returnM (JustOrNoneA b)
                       end))
    end).
  Hint Unfold bind_maybeAT : soundness.

  Lemma bind_maybeAT_id_left : ∀ {A B} (f : A → MaybeAT M B) (a : A), 
    bind_maybeAT (JustAT a) f = f a.
  Proof. 
    unfold JustAT, bind_maybeAT; simpl. intros.
    rewrite bind_id_left. reflexivity.
  Qed.
  Arguments bind_maybeAT_id_left [A B] f a.

  Lemma bind_maybeAT_id_right : ∀ (A : Type) (m : MaybeAT M A), 
    bind_maybeAT m JustAT = m.
  Proof. 
    unfold bind_maybeAT, JustAT. intros. rewrite <- (bind_id_right (M:=M)).
    f_equal; extensionality x. 
    destruct x; autorewrite with soundness; try reflexivity.
  Qed.

  Lemma bind_maybeAT_assoc : ∀ {A B C} (m : MaybeAT M A) 
    (f : A → MaybeAT M B) (g : B → MaybeAT M C),
    bind_maybeAT (bind_maybeAT m f) g =
    bind_maybeAT m (λ a : A, bind_maybeAT (f a) g).
  Proof. 
    intros. unfold bind_maybeAT. autorewrite with soundness.
    f_equal; ext. destruct x; simpl. reflexivity. autorewrite with soundness.
    f_equal; ext.
    destruct x; autorewrite with soundness. 1, 3: reflexivity.
    f_equal; ext. destruct x. autorewrite with soundness.
    reflexivity. autorewrite with soundness. reflexivity.
    autorewrite with soundness. reflexivity.
    autorewrite with soundness. reflexivity.
  Qed.
  Arguments bind_maybeAT_assoc [A B C] m f g.

  Global Instance monad_maybeAT 
  : Monad (MaybeAT M) :=
  {
    bind_id_left := bind_maybeAT_id_left;
    bind_id_right := bind_maybeAT_id_right;
    bind_assoc := bind_maybeAT_assoc;
  }. 
End MaybeAT_Monad.
Hint Unfold bind_maybeAT : soundness.

Section MaybeAT_MonadT.
  Context {M} `{M_monad : Monad M}.

  Definition lift_maybeAT {A} (m : M A) : MaybeAT M A :=
    bindM (M:=M) m (λ a, JustAT a).
  Arguments lift_maybeAT [A].
  Hint Unfold lift_maybeAT : soundness.

  Definition lift_maybeAT_pure : ∀ {A} (a : A),
    lift_maybeAT (returnM a) = returnM a.
  Proof.
    solve_monad.
  Qed.
  Arguments lift_maybeAT_pure [A] a.

  Definition lift_maybeAT_bind : ∀ {A B} (m : M A) (f : A → M B),
    lift_maybeAT (m >>= f) = bind_maybeAT (lift_maybeAT m) (f ∘ lift_maybeAT (A:=B)).
  Proof. 
    unfold lift_maybeAT, bind_maybeAT, JustAT. intros.
    autorewrite with soundness. f_equal; ext. autorewrite with soundness.
    reflexivity.
  Qed.
  Arguments lift_maybeAT_bind [A B] m f.

  Global Instance monadT_maybeAT : MonadT MaybeAT :=
  {
    lift_return := lift_maybeAT_pure;
    lift_bind := lift_maybeAT_bind;
  }. 
End MaybeAT_MonadT.

Section State_Monad.
  Context {S : Type} `{S_inhabited : !Inhabited S} `{S_joinable : Joinable S}.

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
  Context {S : Type} `{S_inhabited : !Inhabited S}.

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
  Context {M} `{M_monad :Monad M}.
  Context {S : Type} `{!Inhabited S}.

  Definition lift_stateT {A} (m : M A) : StateT S M A :=
    λ st, m >>= λ a, returnM (a, st).
  Arguments lift_stateT [A] m.
  Hint Unfold lift_stateT : soundness.
  
  Lemma lift_stateT_pure : ∀ (A : Type) (m : A), 
    lift_stateT (returnM m) = return_stateT m.
  Proof.
    intros. autounfold with soundness. ext.
    autorewrite with soundness. reflexivity.
  Qed.
  Arguments lift_stateT_pure [A] m.

  Lemma lift_stateT_bind : ∀ (A B : Type) (m : M A) (f : A → M B),
    lift_stateT (m >>= f) = bind_stateT (lift_stateT m) (f ∘ lift_stateT (A:=B)).
  Proof.
    intros. simpl.
    autounfold with soundness. ext. autorewrite with soundness.
    f_equal. ext. autorewrite with soundness. reflexivity.
  Qed.
  Arguments lift_stateT_bind [A B] m f.

  Global Instance monadT_stateT : MonadT (StateT S) :=
  {
    liftT := lift_stateT;
    lift_return := lift_stateT_pure;
    lift_bind := lift_stateT_bind;
  }. 
End MonadT_StateT.
