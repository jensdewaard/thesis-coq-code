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
    (i : Identity A) (f : A → Identity B) : Identity B := 
      match i with
      | identity a => f a
      end.
  
  Lemma bind_id_id_left : ∀ (A B : Type) (f : A → Identity B) (a : A),
    bind_id (identity a) f = f a.
  Proof.
    reflexivity.
  Qed.

  Lemma bind_id_id_right : ∀ (A : Type) (ia : Identity A),
    bind_id ia identity = ia.
  Proof.
    intros. destruct ia. reflexivity.
  Qed.

  Lemma bind_id_assoc : ∀ (A B C : Type) (ia : Identity A)
    (f : A → Identity B) (g : B → Identity C),
    bind_id (bind_id ia f) g = bind_id ia (λ a : A, bind_id (f a) g).
  Proof.
    intros. destruct ia; simpl. reflexivity.
  Qed.

  Lemma identity_inj : ∀ A (x y : A),
    identity x = identity y → x = y.
  Proof.
    intros A x y H. inversion H. reflexivity.
  Qed.

  Definition widen_id {A : Type} (i : Identity A) : Identity A := i.

  Lemma widen_id_return : ∀ (A : Type) (a : A), widen_id (identity a) = identity a.
  Proof.
    intros. unfold widen_id. reflexivity.
  Qed.

  Global Instance monad_identity : Monad Identity :=
  {
    widen := @widen_id;
    widen_return := widen_id_return;
    bind_id_left := bind_id_id_left;
    bind_id_right := bind_id_id_right;
    bind_assoc := bind_id_assoc;
  }.
End Identity_Monad.

Section Maybe_Monad.
  Definition bind_maybe {A B} 
    (m : Maybe A) (k : A -> Maybe B) : Maybe B :=
    match m with
    | None => None
    | Just a => k a
    end.
  Arguments bind_maybe [A B].
  Hint Unfold bind_maybe : soundness.

  Lemma bind_maybe_id_left : ∀ {A B} (f : A → Maybe B) (a : A), 
    bind_maybe (Just a) f = f a.
  Proof. simple_solve. Qed.
  Arguments bind_maybe_id_left [A B] f a.

  Lemma bind_maybe_id_right : ∀ {A} (MA : Maybe A), 
    bind_maybe MA Just = MA.
  Proof. simple_solve. Qed.
  Arguments bind_maybe_id_right [A].

  Lemma bind_maybe_assoc : ∀ {A B C} (MA : Maybe A) 
    (f : A → Maybe B) (g : B → Maybe C),
  bind_maybe (bind_maybe MA f) g = bind_maybe MA (λ a : A, bind_maybe (f a) g).
  Proof. simple_solve. Qed.
  Arguments bind_maybe_assoc [A B C] MA f g.

  Lemma just_inj : ∀ A (x y : A),
    Just x = Just y → x = y.
  Proof. 
    intros A x y Heq. inversion Heq. reflexivity.
  Qed.

  Definition widen_maybe {A : Type} (m : Maybe A) := (id (A:=Maybe A) m).

  Lemma widen_maybe_return : ∀ (A : Type) (a : A),
    widen_maybe (Just a) = Just a.
  Proof.
    unfold widen_maybe. intros. rewrite id_refl. reflexivity.
  Qed.

  Global Instance monad_maybe : Monad Maybe :=
  {
    widen := @widen_maybe;
    widen_return := widen_maybe_return;
    bind_id_left := bind_maybe_id_left;
    bind_id_right := bind_maybe_id_right;
    bind_assoc := bind_maybe_assoc;
  }. 
End Maybe_Monad.
Hint Rewrite @bind_maybe_id_left @bind_maybe_id_right : soundness.

Section AbstractMaybe_Monad.
  Definition bind_maybeA {A B : Type}
    (m : AbstractMaybe A) (k : A -> AbstractMaybe B) : AbstractMaybe B :=
    match m with
    | NoneA => NoneA
    | JustA a => k a
    | JustOrNoneA a => match (k a) with
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

  Lemma bind_maybeA_id_right :  ∀ {A} (MA : AbstractMaybe A),
    bind_maybeA MA JustA = MA.
  Proof. solve_monad. Qed.
  Arguments bind_maybeA_id_right [A].

  Lemma bind_maybeA_assoc : ∀ {A B C} (MA : AbstractMaybe A) 
    (f : A → AbstractMaybe B) (g : B → AbstractMaybe C),
    bind_maybeA (bind_maybeA MA f) g =
    bind_maybeA MA (λ a : A, bind_maybeA (f a) g).
  Proof. solve_monad. Qed.
  Arguments bind_maybeA_assoc [A B C] MA f g.

  Lemma justA_inj : ∀ A (x y : A),
    JustA x = JustA y → x = y.
  Proof.
    intros A x y Heq. inversion Heq. reflexivity.
  Qed.

  Definition widen_maybeA {A : Type} (am : AbstractMaybe A) := id am.

  Lemma widen_maybeA_return : ∀ A (a : A),
    widen_maybeA (JustA a) = JustA a.
  Proof.
    intros. unfold widen_maybeA. rewrite id_refl. reflexivity.
  Qed.

  Global Instance monad_abstract_maybe : Monad AbstractMaybe :=
  {
    bindM := bind_maybeA;
    widen_return := widen_maybeA_return;
    bind_id_left := bind_maybeA_id_left;
    bind_id_right := bind_maybeA_id_right;
    bind_assoc := bind_maybeA_assoc;
  }. 
End AbstractMaybe_Monad.
Hint Rewrite @bind_maybeA_id_left @bind_maybeA_id_right : soundness.

Section MaybeT_Monad.
  Context {M} `{M_monad : Monad M}.

  Definition bind_maybeT {A B} (x : MaybeT M A) 
    (f : A -> MaybeT M B) : MaybeT M B :=
    bindM (M:=M) x (λ v : Maybe A,
      match v with
      | None => NoneT
      | Just a => f a
      end
    ).
  Arguments bind_maybeT [A B] x f.
  Hint Unfold bind_maybeT : soundness.

  Lemma bind_maybeT_id_left : ∀ {A B} (f : A → MaybeT M B) (a : A), 
    bind_maybeT (JustT a) f = f a.
  Proof. 
    intros. unfold bind_maybeT, JustT. 
    rewrite bind_id_left. reflexivity.
  Qed.
  Arguments bind_maybeT_id_left [A B] f a.

  Lemma bind_maybeT_id_right : ∀ {A} (MA : MaybeT M A),
    bind_maybeT MA JustT = MA.
  Proof. 
    intros. unfold bind_maybeT, NoneT, JustT. 
    replace (MA) with (bindM (M:=M) MA returnM) at 2.
    f_equal. ext; destruct x; reflexivity.
    rewrite <- (bind_id_right (M:=M)). reflexivity.
  Qed.
  Arguments bind_maybeT_id_right [A] MA.

  Lemma bind_maybeT_assoc : ∀ {A B C} (MA : MaybeT M A) 
    (f : A → MaybeT M B) (g : B → MaybeT M C),
    bind_maybeT (bind_maybeT MA f) g =
    bind_maybeT MA (λ a : A, bind_maybeT (f a) g).
  Proof. 
    intros. unfold bind_maybeT. autorewrite with soundness.
    f_equal. ext. destruct x; eauto with soundness.
    unfold NoneT. autorewrite with soundness. reflexivity.
  Qed.
  Arguments bind_maybeT_assoc [A B C] MA f g.

  Definition widen_maybeT {A : Type} (m : MaybeT M A) : MaybeT M A := 
    (id (widen (M:=M) m)).

  Lemma widen_maybeT_return : ∀ A (a : A),
    widen_maybeT (returnM (M:=M) (Just a)) = returnM (M:=M) (Just a).
  Proof.
    intros. unfold widen_maybeT. rewrite id_refl. rewrite widen_return.
    reflexivity.
  Qed.

  Global Instance monad_maybeT : Monad (MaybeT M) :=
  {
    widen_return := widen_maybeT_return;
    bind_id_left := bind_maybeT_id_left;
    bind_id_right := bind_maybeT_id_right;
    bind_assoc := bind_maybeT_assoc;
  }. 
End MaybeT_Monad.
Hint Unfold bind_maybeT : soundness.
Hint Rewrite @bind_maybeT_id_left @bind_maybeT_id_right : soundness.

Section MaybeT_MonadT.
  Context {M} `{M_monad : Monad M}.
  
  Definition lift_maybeT {A} (Ma : M A) : MaybeT M A :=
    bindM (M:=M) Ma (λ a, JustT a).
  Arguments lift_maybeT [_] _.
  Hint Unfold lift_maybeT : soundness.

  Lemma lift_maybeT_pure : ∀ (A : Type) (x : A),
    lift_maybeT (returnM x) = returnM x.
  Proof. solve_monad. Qed.

  Lemma lift_maybeT_bind : ∀ (A B : Type) (x : M A) (f : A → M B),
  lift_maybeT (x >>= f) = bind_maybeT (lift_maybeT x) (f ∘ (lift_maybeT (A:=B))).
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
  Context {M} `{M_monad : Monad M} `{JoinableMonad M}.

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

  Lemma bind_maybeAT_id_right : ∀ (A : Type) (MA : MaybeAT M A), 
    bind_maybeAT MA JustAT = MA.
  Proof. 
    unfold bind_maybeAT, JustAT. intros. rewrite <- (bind_id_right (M:=M)).
    f_equal; extensionality x. 
    destruct x; autorewrite with soundness; try reflexivity.
  Qed.

  Lemma bind_maybeAT_assoc : ∀ {A B C} (MA : MaybeAT M A) 
    (f : A → MaybeAT M B) (g : B → MaybeAT M C),
    bind_maybeAT (bind_maybeAT MA f) g =
    bind_maybeAT MA (λ a : A, bind_maybeAT (f a) g).
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
  Arguments bind_maybeAT_assoc [A B C] MA f g.

  Definition widen_maybeAT {A : Type} (m : MaybeAT M A) : MaybeAT M A := 
    (id (widen (M:=M) m)).

  Lemma widen_maybeAT_return : ∀ A (a : A),
    widen_maybeAT (returnM (M:=M) (JustA a)) = returnM (M:=M) (JustA a).
  Proof.
    intros. unfold widen_maybeAT. rewrite id_refl, widen_return. reflexivity.
  Qed.

  Global Instance monad_maybeAT 
  : Monad (MaybeAT M) :=
  {
    widen_return := widen_maybeAT_return;
    bind_id_left := bind_maybeAT_id_left;
    bind_id_right := bind_maybeAT_id_right;
    bind_assoc := bind_maybeAT_assoc;
  }. 
End MaybeAT_Monad.
Hint Unfold bind_maybeAT : soundness.

Section MaybeAT_MonadT.
  Context {M} `{M_monad : Monad M}.

  Definition lift_maybeAT {A} (Ma : M A) : MaybeAT M A :=
    bindM (M:=M) Ma (λ a, JustAT a).
  Arguments lift_maybeAT [A].
  Hint Unfold lift_maybeAT : soundness.

  Definition lift_maybeAT_pure : ∀ {A} (x : A),
    lift_maybeAT (returnM x) = returnM x.
  Proof.
    solve_monad.
  Qed.
  Arguments lift_maybeAT_pure [A] x.

  Definition lift_maybeAT_bind : ∀ {A B} (x : M A) (f : A → M B),
    lift_maybeAT (x >>= f) = bind_maybeAT (lift_maybeAT x) (f ∘ lift_maybeAT (A:=B)).
  Proof. 
    unfold lift_maybeAT, bind_maybeAT, JustAT. intros.
    autorewrite with soundness. f_equal; ext. autorewrite with soundness.
    reflexivity.
  Qed.
  Arguments lift_maybeAT_bind [A B] x f.

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

  Lemma return_state_inj : ∀ A (x y : A),
    return_state x = return_state y → x = y.
  Proof.
    intros A x y H. unfold return_state in H. unfold Inhabited in S_inhabited.
    eapply equal_f in H. Unshelve. inversion H. reflexivity. apply S_inhabited.
  Qed.

  Definition bind_state {A B} 
    (p : State S A) (k : A -> State S B) : State S B :=
    λ st, let (x, st') := (p st) in k x st'.

  Arguments bind_state [A B] p k.
  Hint Unfold bind_state : soundness.

  Lemma bind_state_id_left : ∀ (A B : Type) (f : A → State S B) (a : A),
    bind_state (return_state a) f = f a.
  Proof. simple_solve. Qed.

  Lemma bind_state_id_right : ∀ (A : Type) (MA : State S A),
    bind_state MA return_state = MA.
  Proof. simple_solve. Qed.

  Lemma bind_state_assoc : ∀ (A B C : Type) (MA : State S A) 
    (f : A → State S B) (g : B → State S C),
    bind_state (bind_state MA f) g =
    bind_state MA (λ a : A, bind_state (f a) g).
  Proof. simple_solve. Qed.

  Definition widen_state {A : Type} (s : State S A) :=
    λ st, let (a, st') := (s st) in (a, st ⊔ st').

  Lemma widen_state_return : ∀ A (a : A),
    widen_state (return_state a) = return_state a.
  Proof.
    unfold return_state, widen_state. intros. ext. rewrite join_idem.
    reflexivity.
  Qed.
  
  Global Instance monad_state : Monad (State S) :=
  {
    widen_return := widen_state_return;
    bind_id_left := bind_state_id_left;
    bind_id_right := bind_state_id_right;
    bind_assoc := bind_state_assoc;
  }. 
End State_Monad.
Hint Unfold bind_state : soundness.

Section Monad_StateT.
  Context {M} `{M_monad : Monad M}.
  Context {S : Type} `{S_inhabited : !Inhabited S} `{S_joinable : Joinable S}.

  Definition return_stateT {A} (a : A) :=
    λ st : S, returnM (a, st).
  Hint Unfold return_stateT : soundness.

  Definition bind_stateT {A B} (MA : StateT S M A) 
    (f : A -> StateT S M B) : StateT S M B :=
    fun st => bindM (MA st) 
      (fun p : (A*S)%type => let (a,st') := p in f a st').
  Arguments bind_stateT [A B] MA f.
  Hint Unfold bind_stateT : soundness.

  Lemma bind_stateT_id_left : ∀ (A B : Type) (f : A → StateT S M B) (a : A), 
    bind_stateT (return_stateT a) f = f a.
  Proof.
    autounfold with soundness. intros. ext. 
    rewrite bind_id_left. reflexivity.
  Qed.
  Arguments bind_stateT_id_left [A B] f a.

  Lemma bind_stateT_id_right : ∀ (A : Type) (MA : StateT S M A), 
    bind_stateT MA return_stateT = MA.
  Proof.
    intros. autounfold with soundness. ext.
    rewrite <- bind_id_right. f_equal. ext. destruct x0.
    reflexivity.
  Qed.
  Arguments bind_stateT_id_right [A] MA.

  Lemma bind_stateT_assoc : ∀ (A B C : Type) (MA : StateT S M A) 
    (f : A → StateT S M B) (g : B → StateT S M C),
    bind_stateT (bind_stateT MA f) g =
    bind_stateT MA (λ a : A, bind_stateT (f a) g).
  Proof.
    intros. autounfold with soundness. ext.
    autorewrite with soundness. f_equal. ext.
    destruct x0. reflexivity.
  Qed.
  Arguments bind_stateT_assoc [A B C] MA f g.

  Definition widen_stateT {A : Type} (s : StateT S M A) :=
    λ st, let m := (s st) in widen m.

  Lemma widen_stateT_return : ∀ A (a : A),
    widen_stateT (return_stateT a) = return_stateT a.
  Proof.
    intros. unfold widen_stateT, return_stateT. ext. rewrite widen_return.
    reflexivity.
  Qed.
  
  Global Instance monad_stateT : Monad (StateT S M) :=
  {
    widen_return := widen_stateT_return;
    bind_id_left := bind_stateT_id_left;
    bind_id_right := bind_stateT_id_right;
    bind_assoc := bind_stateT_assoc;
  }. 
End Monad_StateT.
Hint Unfold bind_stateT : soundness.

Section MonadT_StateT.
  Context {M} `{M_monad :Monad M}.
  Context {S : Type} `{!Inhabited S}.

  Definition lift_stateT {A} (MA : M A) : StateT S M A :=
    fun st => bindM MA (fun a => returnM (a, st)).
  Arguments lift_stateT [A] MA.
  Hint Unfold lift_stateT : soundness.
  
  Lemma lift_stateT_pure : ∀ (A : Type) (x : A), 
    lift_stateT (returnM x) = return_stateT x.
  Proof.
    intros. autounfold with soundness. ext.
    autorewrite with soundness. reflexivity.
  Qed.
  Arguments lift_stateT_pure [A] x.

  Lemma lift_stateT_bind : ∀ (A B : Type) (x : M A) (f : A → M B),
    lift_stateT (x >>= f) = bind_stateT (lift_stateT x) (f ∘ lift_stateT (A:=B)).
  Proof.
    intros. simpl.
    autounfold with soundness. ext. autorewrite with soundness.
    f_equal. ext. autorewrite with soundness. reflexivity.
  Qed.
  Arguments lift_stateT_bind [A B] x f.

  Global Instance monadT_stateT : MonadT (StateT S) :=
  {
    liftT := lift_stateT;
    lift_return := lift_stateT_pure;
    lift_bind := lift_stateT_bind;
  }. 
End MonadT_StateT.
