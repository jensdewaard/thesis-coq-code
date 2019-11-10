Require Export Base.
Require Import Coq.Program.Basics.
Require Import Classes.Applicative.
Require Import Classes.Functor.
Require Export Classes.Monad.
Require Import FunctionalExtensionality.
Require Import Language.Statements.
Require Import Types.Maps.

Inductive Maybe (A : Type) : Type :=
    | Just : A -> Maybe A
    | None : Maybe A.
Arguments Just {_}.
Arguments None {_}.

Ltac solve_monad := repeat (simple_solve;
  match goal with
  | |- bindM ?f _ = ?f => rewrite <- bind_id_right; f_equal
  | |- bindM ?f _ = bindM ?f _ => apply bind_equiv_r
  | _ => simple_solve
  end).

Section Maybe_Functor.
  Definition fmap_maybe {A B : Type} (f : A -> B) (ma : Maybe A) : Maybe B :=
    match ma with
    | Just a => Just (f a)
    | None => None
    end.
  Arguments fmap_maybe [_ _] _ _.
  Hint Unfold fmap_maybe : soundness.

  Lemma fmap_maybe_id : ∀ A : Type, fmap_maybe (@id A) = id.
  Proof. simple_solve. Qed.

  Lemma fmap_maybe_compose : ∀ (A B C : Type) (f : A → B) (g : B → C),
    fmap_maybe (f ∘ g) = fmap_maybe f ∘ fmap_maybe g.
  Proof. simple_solve. Qed.

  Global Instance functor_maybe : Functor (Maybe) := 
  {
    fmap := fmap_maybe;
    fmap_id := fmap_maybe_id;
    fmap_compose := fmap_maybe_compose;
  }.
End Maybe_Functor.
Hint Rewrite fmap_maybe_id fmap_maybe_compose : soundness.

Section Maybe_Applicative.
  Definition app_maybe {A B : Type} 
    (Mf : Maybe (A -> B)) (Ma : Maybe A) : Maybe B :=
    match Mf, Ma with
    | None, _ => None
    | _, None => None
    | Just f, Just x => Just (f x)
    end.
  Arguments app_maybe [_ _] _ _.
  Hint Unfold app_maybe : soundness.

  Lemma app_maybe_id : 
    ∀ (A : Type) (f : Maybe A), app_maybe (Just id) f = f.
  Proof. simple_solve. Qed.

  Lemma app_maybe_homomorphism :
    ∀ (A B : Type) (f : A → B) (x : A), 
    app_maybe (Just f) (Just x) = Just (f x).
  Proof. simple_solve. Qed.

  Lemma app_maybe_interchange :
    ∀ (A B : Type) (u : Maybe (A → B)) (y : A),
    app_maybe u (Just y) = app_maybe (Just (λ f : A → B, f y)) u.
  Proof. simple_solve. Qed.

  Lemma app_maybe_compose :
    ∀ (A B C : Type) (u : Maybe (B → C)) (v : Maybe (A → B)) (w : Maybe A),
    app_maybe (app_maybe (app_maybe (Just compose) u) v) w =
    app_maybe u (app_maybe v w).
  Proof. simple_solve. Qed.

  Global Instance applicative_maybe : Applicative Maybe :=
  {
    pure := @Just;
    app := app_maybe;
    app_id := app_maybe_id;
    app_homomorphism := app_maybe_homomorphism;
    app_interchange := app_maybe_interchange;
    app_compose := app_maybe_compose;
  }.
End Maybe_Applicative.
Hint Rewrite app_maybe_id app_maybe_homomorphism : soundness.

Section Maybe_Monad.
  Definition bind_maybe {A B : Type} 
    (m : Maybe A) (k : A -> Maybe B) : Maybe B :=
    match m with
    | None => None
    | Just a => k a
    end.
  Arguments bind_maybe [_ _].
  Hint Unfold bind_maybe : soundness.

  Lemma bind_maybe_id_left : ∀ (A B : Type) (f : A → Maybe B) (a : A), 
    bind_maybe (Just a) f = f a.
  Proof. simple_solve. Qed.

  Lemma bind_maybe_id_right : ∀ (A : Type) (MA : Maybe A), 
    bind_maybe MA Just = MA.
  Proof. simple_solve. Qed.

  Lemma bind_maybe_assoc : ∀ (A B C : Type) (MA : Maybe A) 
    (f : A → Maybe B) (g : B → Maybe C),
  bind_maybe (bind_maybe MA f) g = bind_maybe MA (λ a : A, bind_maybe (f a) g).
  Proof. simple_solve. Qed.

  Global Instance monad_maybe : Monad Maybe :=
  {
    bindM := bind_maybe;
    bind_id_left := bind_maybe_id_left;
    bind_id_right := bind_maybe_id_right;
    bind_assoc := bind_maybe_assoc;
  }.
End Maybe_Monad.
Hint Rewrite bind_maybe_id_left bind_maybe_id_right : soundness.

Inductive AbstractMaybe (A : Type) : Type :=
  | JustA : A -> AbstractMaybe A
  | JustOrNoneA : A -> AbstractMaybe A
  | NoneA : AbstractMaybe A.
Arguments JustA {_}.
Arguments JustOrNoneA {_}.
Arguments NoneA {_}.

Section AbstractMaybe_Functor.
  Definition fmap_abstract_maybe {A B : Type} 
    (f : A -> B) (ma : AbstractMaybe A) : AbstractMaybe B :=
    match ma with
    | JustA a => JustA (f a)
    | JustOrNoneA a => JustOrNoneA (f a)
    | NoneA => NoneA
    end. 
  Arguments fmap_abstract_maybe [_ _] _ _.
  Hint Unfold fmap_abstract_maybe : soundness.

  Lemma fmap_abstract_maybe_id : ∀ A : Type, fmap_abstract_maybe (@id A) = id.
  Proof. simple_solve. Qed.

  Lemma fmap_abstract_maybe_compose : ∀ (A B C : Type) (f : A → B) (g : B → C),
  fmap_abstract_maybe (f ∘ g) = fmap_abstract_maybe f ∘ fmap_abstract_maybe g.
  Proof. simple_solve. Qed.

  Global Instance functor_abstract_maybe : Functor AbstractMaybe :=
  {
    fmap := fmap_abstract_maybe;
    fmap_id := fmap_abstract_maybe_id;
    fmap_compose := fmap_abstract_maybe_compose;
  }.
End AbstractMaybe_Functor.
Hint Rewrite fmap_abstract_maybe_id fmap_abstract_maybe_compose : soundness.

Section AbstractMaybe_Applicative.
  Definition app_abstract_maybe {A B : Type} (Mf : AbstractMaybe (A -> B))
    (Ma : AbstractMaybe A) : AbstractMaybe B :=
  match Mf, Ma with
  | NoneA, _ => NoneA
  | _, NoneA => NoneA
  | JustOrNoneA f, JustOrNoneA a
  | JustOrNoneA f, JustA a 
  | JustA f, JustOrNoneA a => JustOrNoneA (f a)
  | JustA f, JustA a => JustA (f a)
  end.
  Arguments app_abstract_maybe [_ _] _ _.
  Hint Unfold app_abstract_maybe : soundness.

  Lemma app_abstract_maybe_id : ∀ (A : Type) (f : AbstractMaybe A),
    app_abstract_maybe (JustA id) f = f.
  Proof. simple_solve. Qed.

  Lemma app_abstract_maybe_homomorphism : ∀ (A B : Type) (f : A → B) (x : A),
  app_abstract_maybe (JustA f) (JustA x) = JustA (f x).
  Proof. simple_solve. Qed.

  Lemma app_abstract_maybe_interchange : ∀ (A B : Type) 
    (u : AbstractMaybe (A → B)) (y : A),
    app_abstract_maybe u (JustA y) =
    app_abstract_maybe (JustA (λ f : A → B, f y)) u.
  Proof. simple_solve. Qed.

  Lemma app_abstract_maybe_compose : ∀ (A B C : Type) 
    (u : AbstractMaybe (B → C)) (v : AbstractMaybe (A → B)) 
    (w : AbstractMaybe A),
    app_abstract_maybe
      (app_abstract_maybe (app_abstract_maybe (JustA compose) u) v) w =
    app_abstract_maybe u (app_abstract_maybe v w).
  Proof. simple_solve. Qed.

  Global Instance applicative_abstract_maybe : Applicative AbstractMaybe :=
  {
    pure := @JustA;
    app := app_abstract_maybe;
    app_id := app_abstract_maybe_id;
    app_homomorphism := app_abstract_maybe_homomorphism; 
    app_interchange := app_abstract_maybe_interchange;
    app_compose := app_abstract_maybe_compose;
  }.
End AbstractMaybe_Applicative.
Hint Resolve app_abstract_maybe_id app_abstract_maybe_homomorphism : soundness.

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
  Arguments bind_maybeA [_].
  Hint Unfold bind_maybeA : soundness.

  Lemma bind_maybeA_id_left : ∀ (A B : Type) (f : A → AbstractMaybe B) (a : A),
  bind_maybeA B (JustA a) f = f a.
  Proof. simple_solve. Qed.

  Lemma bind_maybeA_id_right :  ∀ (A : Type) (MA : AbstractMaybe A),
    bind_maybeA A MA JustA = MA.
  Proof. simple_solve. Qed.

  Lemma bind_maybeA_assoc : ∀ (A B C : Type) (MA : AbstractMaybe A) 
    (f : A → AbstractMaybe B) (g : B → AbstractMaybe C),
    bind_maybeA C (bind_maybeA B MA f) g =
    bind_maybeA C MA (λ a : A, bind_maybeA C (f a) g).
  Proof. simple_solve. Qed.

  Global Instance monad_abstract_maybe : Monad AbstractMaybe :=
  {
    bindM := bind_maybeA;
    bind_id_left := bind_maybeA_id_left;
    bind_id_right := bind_maybeA_id_right;
    bind_assoc := bind_maybeA_assoc;
  }.
End AbstractMaybe_Monad.
Hint Rewrite bind_maybeA_id_left bind_maybeA_id_right : soundness.

Definition MaybeT (M : Type -> Type) (A : Type) : Type := M (Maybe A).

Section MaybeT_Functor.
  Context {M : Type -> Type} `{Monad M}.

  Definition fmap_maybeT {A B : Type} (f : A -> B)
    (m : MaybeT M A) : MaybeT M B :=  fmap (fmap (F:=Maybe) f) m. 
  Arguments fmap_maybeT [_ _] _ _.
  Hint Unfold fmap_maybeT : soundness.

  Lemma fmap_maybeT_id : ∀ A : Type, fmap_maybeT (@id A) = id.
  Proof. simple_solve. Qed.

  Lemma fmap_maybeT_compose : ∀ (A B C : Type) (f : A → B) (g : B → C),
  fmap_maybeT (f ∘ g) = fmap_maybeT f ∘ fmap_maybeT g.
  Proof. simple_solve. Qed.

  Global Instance functor_maybeT : Functor (MaybeT M) :=
  {
    fmap := fmap_maybeT;
    fmap_id := fmap_maybeT_id;
    fmap_compose := fmap_maybeT_compose;
  }.
End MaybeT_Functor.

Hint Rewrite fmap_maybeT_id fmap_maybeT_compose : soundness.

Section MaybeT_Applicative.
  Context {M : Type -> Type} `{inst : Monad M}.

  Definition pure_maybeT {A : Type} (x : A) :  M (Maybe A) :=
    pure (Just x).
  Arguments pure_maybeT [_] _.
  Hint Unfold pure_maybeT : soundness.

  Definition app_maybeT {A B : Type} (Mmf : M (Maybe (A -> B)))
    (Mma : M (Maybe A)) : M (Maybe B) :=
    bindM Mmf (fun mf =>
    bindM Mma (fun ma =>
      pure (app_maybe mf ma))).
  Arguments app_maybeT [_ _] _ _.
  Hint Unfold app_maybeT : soundness.

  Lemma app_maybeT_id : ∀ (A : Type) (f : M (Maybe A)),
    app_maybeT (pure_maybeT id) f = f.
  Proof. solve_monad. Qed.

  Lemma app_maybeT_homomorphism : ∀ (A B : Type) (f : A → B) (x : A),
  app_maybeT (pure_maybeT f) (pure_maybeT x) = pure_maybeT (f x).
  Proof. solve_monad. Qed.

  Lemma app_maybeT_interchange : ∀ (A B : Type) (u : MaybeT M (A → B)) (y : A),
  app_maybeT u (pure_maybeT y) = app_maybeT (pure_maybeT (λ f : A → B, f y)) u.
  Proof. solve_monad. Qed.

  Lemma app_maybeT_compose : ∀ (A B C : Type) (u : MaybeT M (B → C)) 
    (v : MaybeT M (A → B))  (w : MaybeT M A),
    app_maybeT (app_maybeT (app_maybeT (pure_maybeT compose) u) v) w =
    app_maybeT u (app_maybeT v w).
  Proof. solve_monad. Qed.

  Global Instance applicative_maybeT : Applicative (MaybeT M) :=
  {
    pure := pure_maybeT;
    app := app_maybeT;
    app_id := app_maybeT_id;
    app_homomorphism := app_maybeT_homomorphism;
    app_interchange := app_maybeT_interchange;
    app_compose := app_maybeT_compose;
  }.
End MaybeT_Applicative.
Hint Unfold pure_maybeT app_maybeT : soundness.
Hint Rewrite app_maybeT_id app_maybeT_homomorphism : soundness.

Section MaybeT_Monad.
  Context {M : Type -> Type} `{inst : Monad M}.

  Definition bind_maybeT {A B : Type} (Mma : M (Maybe A))
    (f : A -> M (Maybe B)) : M (Maybe B) :=
    @bindM M _ _ _ (Maybe A) (Maybe B) Mma (fun ma =>
      match ma with
      | None => pure None
      | Just a => f a
      end
    ).
  Arguments bind_maybeT [_ _] _ _.
  Hint Unfold bind_maybeT : soundness.

  Lemma bind_maybeT_id_left : ∀ (A B : Type) (f : A → MaybeT M B) (a : A), 
    bind_maybeT (pure a) f = f a.
  Proof. solve_monad. Qed.

  Lemma bind_maybeT_id_right : ∀ (A : Type) (MA : MaybeT M A),
    bind_maybeT MA pure = MA.
  Proof. solve_monad. Qed.

  Lemma bind_maybeT_assoc : ∀ (A B C : Type) (MA : MaybeT M A) 
    (f : A → MaybeT M B) (g : B → MaybeT M C),
    bind_maybeT (bind_maybeT MA f) g =
    bind_maybeT MA (λ a : A, bind_maybeT (f a) g).
  Proof. solve_monad. Qed.

  Global Instance monad_maybeT : Monad (MaybeT M) :=
  {
    bindM := bind_maybeT;
    bind_id_left := bind_maybeT_id_left;
    bind_id_right := bind_maybeT_id_right;
    bind_assoc := bind_maybeT_assoc;
  }.
End MaybeT_Monad.
Hint Unfold bind_maybeT : soundness.
Hint Rewrite bind_maybeT_id_left bind_maybeT_id_right : soundness.

Section MaybeT_MonadT.
  Context {M : Type -> Type} `{Monad M}.
  
  Definition lift_maybeT {A : Type} (Ma : M A) : M (Maybe A) :=
    fmap Just Ma.
  Arguments lift_maybeT [_] _.

  Global Instance monadT_maybeT : MonadT (MaybeT) :=
  {
    liftT := lift_maybeT;
  }.
End MaybeT_MonadT.

Definition MaybeAT (M : Type -> Type) (A : Type) : Type := M (AbstractMaybe A).

Section MaybeAT_Functor.
  Context {M : Type -> Type} `{inst : Functor M}.

  Definition fmap_maybeAT {A B : Type} 
    (f : A -> B) (Ma : MaybeAT M A) : MaybeAT M B :=
    fmap (fmap_abstract_maybe f) Ma.
  Arguments fmap_maybeAT [_ _] _ _.
  Hint Unfold fmap_maybeAT : soundness.

  Global Instance functor_maybeAT : Functor (MaybeAT M) :=
  {
    fmap := fmap_maybeAT;
  }. all: solve_monad. Defined.
End MaybeAT_Functor.

Section MaybeAT_Applicative.
  Context {M : Type -> Type} `{inst : Monad M}.

  Definition pure_maybeAT {A : Type} (x : A) : MaybeAT M A :=
    pure (JustA x).
  Arguments pure_maybeAT [_] _.
  Hint Unfold pure_maybeAT : soundness.

  Definition app_maybeAT {A B : Type} (Mmf : M (AbstractMaybe (A -> B)))
    (Mma : M (AbstractMaybe A)) : M (AbstractMaybe B) :=
    bindM Mmf (fun mf : AbstractMaybe (A -> B) =>
    bindM Mma (fun ma : AbstractMaybe A =>
      pure (app_abstract_maybe mf ma))).
  Arguments app_maybeAT [_ _] _ _.
  Hint Unfold app_maybeAT : soundness.

  Lemma app_maybeAT_id : ∀ (A : Type) (f : MaybeAT M A), 
    app_maybeAT (pure_maybeAT id) f = f.
  Proof. solve_monad. Qed.

  Lemma app_maybeAT_homomorphism : ∀ (A B : Type) (f : A → B) (x : A),
    app_maybeAT (pure_maybeAT f) (pure_maybeAT x) = pure_maybeAT (f x).
  Proof. solve_monad. Qed.

  Lemma app_maybeAT_interchange : ∀ (A B : Type) (u : MaybeAT M (A → B)) (y : A),
    app_maybeAT u (pure_maybeAT y) = 
    app_maybeAT (pure_maybeAT (λ f : A → B, f y)) u.
  Proof. solve_monad. Qed.

  Lemma app_maybeAT_compose : ∀ (A B C : Type) 
    (u : MaybeAT M (B → C)) (v : MaybeAT M (A → B)) (w : MaybeAT M A),
    app_maybeAT (app_maybeAT (app_maybeAT (pure_maybeAT compose) u) v) w =
    app_maybeAT u (app_maybeAT v w).
  Proof. solve_monad. Qed.

  Global Instance applicative_maybeAT : Applicative (MaybeAT M) :=
  {
    pure := pure_maybeAT;
    app := app_maybeAT;
    app_id := app_maybeAT_id;
    app_homomorphism := app_maybeAT_homomorphism;
    app_interchange := app_maybeAT_interchange;
    app_compose := app_maybeAT_compose;
  }.
End MaybeAT_Applicative.
Hint Unfold pure_maybeAT app_maybeAT : soundness.

Section MaybeAT_Monad.
  Context {M : Type -> Type} `{Monad M}.

  Definition bind_maybeAT {A B} 
    (Mma : M (AbstractMaybe A))
    (f : A -> M (AbstractMaybe B)) : M (AbstractMaybe B) :=
  @bindM M _ _ _ (AbstractMaybe A) (AbstractMaybe B) Mma (fun ma =>
    match ma with
    | NoneA => pure NoneA
    | JustA a => f a
    | JustOrNoneA a => 
        @bindM M _ _ _ (AbstractMaybe B) (AbstractMaybe B) (f a) (fun mfa =>
                       match mfa with
                       | NoneA => pure NoneA
                       | JustA b => pure (JustOrNoneA b)
                       | JustOrNoneA b => pure (JustOrNoneA b)
                       end)
    end).
  Arguments bind_maybeAT [_ _].
  Hint Unfold bind_maybeAT : soundness.

  Lemma bind_maybeAT_id_left : ∀ (A B : Type) (f : A → MaybeAT M B) (a : A), 
    bind_maybeAT (pure a) f = f a.
  Proof. solve_monad. Qed.

  Lemma bind_maybeAT_id_right : ∀ (A : Type) (MA : MaybeAT M A), 
    bind_maybeAT MA pure = MA.
  Proof. solve_monad. Qed.

  Lemma bind_maybeAT_assoc : ∀ (A B C : Type) (MA : MaybeAT M A) 
    (f : A → MaybeAT M B) (g : B → MaybeAT M C),
    bind_maybeAT (bind_maybeAT MA f) g =
    bind_maybeAT MA (λ a : A, bind_maybeAT (f a) g).
  Proof. solve_monad. Qed.

  Global Instance monad_maybeAT 
  : Monad (MaybeAT M) :=
  {
    bindM := bind_maybeAT;
    bind_id_left := bind_maybeAT_id_left;
    bind_id_right := bind_maybeAT_id_right;
    bind_assoc := bind_maybeAT_assoc;
  }.
End MaybeAT_Monad.

Section MaybeAT_MonadT.
  Context {M : Type -> Type} `{Monad M}.

  Definition lift_maybeAT {A : Type} (Ma : M A) : MaybeAT M A :=
    fmap JustA Ma.
  Arguments lift_maybeAT [_].

  Global Instance monadT_maybeAT : MonadT MaybeAT :=
  {
    liftT := lift_maybeAT;
  }.
End MaybeAT_MonadT.

Definition State (S A : Type) := S -> (A * S).

Section State_Functor.
  
  Definition fmap_state {S A B : Type} 
    (f : A -> B) (Fa : State S A) : State S B :=
  fun st => let (x, s) := Fa st in (f x, s).
  Arguments fmap_state [_ _ _] _ _.
  Hint Unfold fmap_state : soundness.

  Global Instance functor_state (S : Type) : Functor (State S) :=
  {
    fmap := @fmap_state S;
  }. all: solve_monad. Defined.

End State_Functor.

Section State_Applicative.
  Definition pure_state {S A : Type} (a : A) : State S A :=
    fun st => (a, st).

  Definition app_state {S A B : Type} 
    (Mf : State S (A -> B)) (Ma : State S A) : State S B :=
    fun st => let (f, st') := Mf st in 
              let (a, st'') := Ma st' in (f a, st'').
  Hint Unfold pure_state app_state : soundness.

  Global Instance applicative_state (S : Type) : Applicative (State S) :=
  {
    pure := @pure_state S;
    app := @app_state S;
  }. all: simple_solve. Defined.
End State_Applicative.

Section State_Monad.
  Definition bind_state {S A B : Type} 
    (p : State S A) (k : A -> State S B) : State S B :=
    fun st => match (p st) with
              | (x, st') => k x st'
              end.
  Hint Unfold bind_state : soundness.

  Global Instance monad_state (S : Type) :  Monad (State S) :=
  {
    bindM := @bind_state S;
  }. all: simple_solve. Defined.
End State_Monad.

Definition StateT (S : Type) (M : Type -> Type) (A : Type) : Type :=
  S -> M (A*S)%type.

Section Functor_StateT.
  Context {M : Type -> Type} `{Monad M}.

  Definition fmap_stateT (S : Type) {A B} (f : A -> B) (m : StateT S M A)
    : StateT S M B :=
    fun s : S => bindM (m s) 
      (fun x => let (a, s') := x : (A*S)%type in pure (f a, s')).
  Hint Unfold fmap_stateT : soundness.

  Global Instance functor_stateT (S : Type) : Functor (StateT S M) :=
  {
    fmap := @fmap_stateT S;
  }. all: solve_monad. Defined.
End Functor_StateT.

Section Applicative_StateT.
  Context {M : Type -> Type} `{Monad M}.

  Definition pure_stateT (S : Type) {A : Type} (x : A) : StateT S M A :=
    fun s => pure (x, s).

  Definition app_stateT
    (S : Type) {A B : Type}
    (sf : StateT S M (A -> B)) (sa : StateT S M A) : StateT S M B :=
    fun st : S =>
    bindM (sf st) (fun '(f, stf) =>
      bindM (sa stf) (fun '(a, sta) =>
        pure (f a, sta))).
  Hint Unfold pure_stateT app_stateT : soundness.

  Global Instance applicative_stateT (S : Type) : Applicative (StateT S M) :=
  {
    pure := @pure_stateT S;
    app := @app_stateT S;
  }. all: solve_monad. Defined.
End Applicative_StateT.
Hint Unfold pure_stateT app_stateT : soundness.

Section Monad_StateT.
  Context {M : Type -> Type} `{Monad M}.

  Definition bind_stateT (S : Type) {A B : Type} 
    (MA : StateT S M A) (f : A -> StateT S M B) : StateT S M B :=
    fun st => bindM (MA st) (fun '(a, st') => f a st').
  Hint Unfold bind_stateT : soundness.

  Global Instance monad_stateT (S : Type) : Monad (StateT S M) :=
  {
    bindM := @bind_stateT S;
  }. all: solve_monad. Defined.
End Monad_StateT.

Section MonadT_StateT.
  Context {M : Type -> Type} `{Monad M}.

  Definition lift_stateT (S : Type) {A : Type} (MA : M A) : StateT S M A :=
    fun st => bindM MA (fun a => pure (a, st)).

  Global Instance monadT_stateT (S : Type) : MonadT (StateT S) :=
  {
    liftT := @lift_stateT S;
  }.
End MonadT_StateT.
