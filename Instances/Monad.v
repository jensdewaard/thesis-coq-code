Require Export Base.
Require Import Coq.Program.Basics.
Require Import Classes.Applicative.
Require Import Classes.Functor.
Require Export Classes.Monad.
Require Import FunctionalExtensionality.
Require Import Language.Statements.
Require Import Types.Maps.

Implicit Type S A B C : Type.
Implicit Type M : Type → Type.

Inductive Maybe A : Type :=
    | Just : A -> Maybe A
    | None : Maybe A.
Arguments Just {_}.
Arguments None {_}.

Section Maybe_Functor.
  Definition fmap_maybe {A B} (f : A → B) ma : Maybe B :=
    match ma with
    | Just a => Just (f a)
    | None => None
    end.
  Arguments fmap_maybe [A B] f ma.
  Hint Unfold fmap_maybe : soundness.

  Lemma fmap_maybe_id {A} : (fmap_maybe (B:=A)) id = id.
  Proof. 
    unfold fmap_maybe. ext. destruct x; reflexivity.
  Qed.

  Lemma fmap_maybe_compose : ∀ {A B C} (f : A → B) (g : B → C),
    fmap_maybe (f ∘ g) = fmap_maybe f ∘ fmap_maybe g.
  Proof. simple_solve. Qed.
  Arguments fmap_maybe_compose [A B C] f g.

  Global Instance functor_maybe : Functor (Maybe) := 
  {
    fmap := fmap_maybe;
    fmap_id := @fmap_maybe_id;
    fmap_compose := fmap_maybe_compose;
  }.
End Maybe_Functor.
Hint Unfold fmap_maybe : soundness.
Hint Rewrite @fmap_maybe_id @fmap_maybe_compose : soundness.

Section Maybe_Applicative.
  Definition app_maybe {A B} 
    (Mf : Maybe (A -> B)) (Ma : Maybe A) : Maybe B :=
    match Mf, Ma with
    | None, _ => None
    | _, None => None
    | Just f, Just x => Just (f x)
    end.
  Arguments app_maybe [A B] Mf Ma.
  Hint Unfold app_maybe : soundness.

  Lemma app_maybe_id : 
    ∀ {A} (f : Maybe A), app_maybe (Just id) f = f.
  Proof. simple_solve. Qed.
  Arguments app_maybe_id [A].

  Lemma app_maybe_homomorphism :
    ∀ {A B} (f : A → B) (x : A), 
    app_maybe (Just f) (Just x) = Just (f x).
  Proof. simple_solve. Qed.
  Arguments app_maybe_homomorphism [A B] f x.

  Lemma app_maybe_interchange :
    ∀ {A B} (u : Maybe (A → B)) (y : A),
    app_maybe u (Just y) = app_maybe (Just (λ f : A → B, f y)) u.
  Proof. simple_solve. Qed.
  Arguments app_maybe_interchange [A B] u y.

  Lemma app_maybe_compose :
    ∀ {A B C} (u : Maybe (B → C)) (v : Maybe (A → B)) (w : Maybe A),
    app_maybe u (app_maybe v w) =
    app_maybe (app_maybe (app_maybe (Just compose) u) v) w.
  Proof. simple_solve. Qed.
  Arguments app_maybe_compose [A B C] u v w.

  Lemma app_maybe_fmap : ∀ {A B} (f : A → B) (x : Maybe A), 
    fmap f x = app_maybe (Just f) x.
  Proof. simple_solve. Qed.
  Arguments app_maybe_fmap [A B] f x.

  Lemma just_inj : ∀ (A : Type) (x y : A), Just x = Just y → x = y.
  Proof.
    intros A x y Heq. inv Heq. reflexivity.
  Qed.

  Global Instance applicative_maybe : Applicative Maybe :=
  {
    pure := @Just;
    pure_inj := just_inj;
    app := app_maybe;
    app_id := app_maybe_id;
    app_homomorphism := app_maybe_homomorphism;
    app_interchange := app_maybe_interchange;
    app_compose := app_maybe_compose;
    app_fmap := app_maybe_fmap;
  }. 
End Maybe_Applicative.
Hint Unfold app_maybe : soundness.
Hint Rewrite @app_maybe_id @app_maybe_homomorphism : soundness.

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

  Lemma bind_maybe_app : ∀ {A B} (mf : Maybe (A → B)) (ma : Maybe A),
    mf <*> ma =
  bind_maybe mf (λ f : A → B, bind_maybe ma (λ a : A, (f ∘ pure) a)).
  Proof. simple_solve. Qed.
  Arguments bind_maybe_app [A B] mf ma.

  Lemma bind_maybe_fmap : ∀ {A B C} (f : A → B) (x : Maybe A) (g : B → Maybe C),
    bind_maybe (f <$> x) g = bind_maybe x (f ∘ g).
  Proof. 
    intros. unfold bind_maybe. unfold compose. destruct x; reflexivity.
  Qed.
  Arguments bind_maybe_fmap [A B C] f x g.

  Lemma bind_maybe_pass : ∀ {A B : Type} (ma : Maybe A) (mb : Maybe B),
    ma >> mb = bind_maybe ma (λ _ : A, mb).
  Proof. simple_solve. Qed.
  Arguments bind_maybe_pass [A B] ma mb.

  Global Instance monad_maybe : Monad Maybe :=
  {
    bindM := bind_maybe;
    bind_id_left := bind_maybe_id_left;
    bind_id_right := bind_maybe_id_right;
    bind_assoc := bind_maybe_assoc;
    bind_app := bind_maybe_app;
    bind_fmap := bind_maybe_fmap;
    bind_pass := bind_maybe_pass;
  }. 
End Maybe_Monad.
Hint Rewrite @bind_maybe_id_left @bind_maybe_id_right : soundness.

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

  Lemma fmap_abstract_maybe_id : ∀ {A}, fmap_abstract_maybe (@id A) = id.
  Proof. simple_solve. Qed.
  Arguments fmap_abstract_maybe_id {A}.

  Lemma fmap_abstract_maybe_compose : ∀ {A B C : Type} (f : A → B) (g : B → C),
  fmap_abstract_maybe (f ∘ g) = fmap_abstract_maybe f ∘ fmap_abstract_maybe g.
  Proof. simple_solve. Qed.
  Arguments fmap_abstract_maybe_compose [A B C] f g.

  Global Instance functor_abstract_maybe : Functor AbstractMaybe :=
  {
    fmap := fmap_abstract_maybe;
    fmap_id := @fmap_abstract_maybe_id;
    fmap_compose := fmap_abstract_maybe_compose;
  }.
End AbstractMaybe_Functor.
Hint Unfold fmap_abstract_maybe : soundness.
Hint Rewrite @fmap_abstract_maybe_id @fmap_abstract_maybe_compose : soundness.

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

  Lemma app_abstract_maybe_id : ∀ {A} (f : AbstractMaybe A),
    app_abstract_maybe (JustA id) f = f.
  Proof. simple_solve. Qed.
  Arguments app_abstract_maybe_id [A].

  Lemma app_abstract_maybe_homomorphism : ∀ {A B} (f : A → B) (x : A),
  app_abstract_maybe (JustA f) (JustA x) = JustA (f x).
  Proof. simple_solve. Qed.
  Arguments app_abstract_maybe_homomorphism [A B] f x.

  Lemma app_abstract_maybe_interchange : ∀ {A B}
    (u : AbstractMaybe (A → B)) (y : A),
    app_abstract_maybe u (JustA y) =
    app_abstract_maybe (JustA (λ f : A → B, f y)) u.
  Proof. simple_solve. Qed.
  Arguments app_abstract_maybe_interchange [A B] u y.

  Lemma app_abstract_maybe_compose : ∀ {A B C} 
    (u : AbstractMaybe (B → C)) (v : AbstractMaybe (A → B)) 
    (w : AbstractMaybe A),
    app_abstract_maybe u (app_abstract_maybe v w) =
    app_abstract_maybe
      (app_abstract_maybe (app_abstract_maybe (JustA compose) u) v) w.
  Proof. simple_solve. Qed.
  Arguments app_abstract_maybe_compose [A B C] u v w.

  Lemma app_abstract_maybe_fmap : ∀ {A B} (f : A → B) 
    (x : AbstractMaybe A),
  fmap f x = app_abstract_maybe (JustA f) x.
  Proof. simple_solve. Qed.
  Arguments app_abstract_maybe_fmap [A B] f x.

  Lemma justA_inj : ∀ (A : Type) (x y : A), JustA x = JustA y → x = y.
  Proof.
    intros A x y Heq. inv Heq. reflexivity.
  Qed.

  Lemma justOrNoneA_inj : ∀ (A : Type) (x y : A),
    JustOrNoneA x = JustOrNoneA y → x = y.
  Proof.
    intros A x y Heq. inv Heq. reflexivity.
  Qed.

  Global Instance applicative_abstract_maybe : Applicative AbstractMaybe :=
  {
    pure := @JustA;
    pure_inj := justA_inj;
    app := app_abstract_maybe;
    app_id := app_abstract_maybe_id;
    app_homomorphism := app_abstract_maybe_homomorphism; 
    app_interchange := app_abstract_maybe_interchange;
    app_compose := app_abstract_maybe_compose;
    app_fmap := app_abstract_maybe_fmap;
  }.
End AbstractMaybe_Applicative.
Hint Resolve @app_abstract_maybe_id @app_abstract_maybe_homomorphism : soundness.

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

  Lemma bind_maybeA_fmap : ∀ {A B C} (f : A → B) 
    (x : AbstractMaybe A) (g : B → AbstractMaybe C),
    bind_maybeA (f <$> x) g = bind_maybeA x (f ∘ g).
  Proof. 
    destruct x; reflexivity.
  Qed.
  Arguments bind_maybeA_fmap [A B C] f x.

  Lemma bind_maybeA_app : ∀ {A B} (mf : AbstractMaybe (A → B)) 
    (ma : AbstractMaybe A),
    app_abstract_maybe mf ma =
    bind_maybeA mf (λ f : A → B, bind_maybeA ma (λ a : A, (f ∘ pure) a)).
  Proof. destruct mf, ma; reflexivity. Qed.
  Arguments bind_maybeA_app [A B] mf ma.

  Lemma bind_maybeA_pass : ∀ {A B} (ma : AbstractMaybe A) 
    (mb : AbstractMaybe B),
    ma >> mb = bind_maybeA ma (λ _ : A, mb).
  Proof. destruct ma, mb; reflexivity. Qed.
  Arguments bind_maybeA_pass [A B] ma mb.

  Global Instance monad_abstract_maybe : Monad AbstractMaybe :=
  {
    bindM := bind_maybeA;
    bind_id_left := bind_maybeA_id_left;
    bind_id_right := bind_maybeA_id_right;
    bind_assoc := bind_maybeA_assoc;
    bind_fmap := bind_maybeA_fmap;
    bind_app := bind_maybeA_app;
    bind_pass := bind_maybeA_pass;
  }. 
End AbstractMaybe_Monad.
Hint Rewrite @bind_maybeA_id_left @bind_maybeA_id_right : soundness.

Definition MaybeT M A: Type := M (Maybe A).

Section MaybeT_Functor.
  Context {M} `{M_monad : Monad M}.

  Definition fmap_maybeT {A B} (f : A -> B)
    (m : MaybeT M A) : MaybeT M B :=  fmap (fmap (M:=Maybe) f) m. 
  Arguments fmap_maybeT [_ _] _ _.
  Hint Unfold fmap_maybeT : soundness.

  Lemma fmap_maybeT_id : ∀ {A}, fmap_maybeT (@id A) = id.
  Proof. simple_solve. Qed.

  Lemma fmap_maybeT_compose : ∀ {A B C} (f : A → B) (g : B → C),
  fmap_maybeT (f ∘ g) = fmap_maybeT f ∘ fmap_maybeT g.
  Proof. 
    intros. unfold fmap_maybeT. ext.
    repeat rewrite fmap_compose. 
    reflexivity.
  Qed.
  Arguments fmap_maybeT_compose [A B C] f g.

  Global Instance functor_maybeT : Functor (MaybeT M) :=
  {
    fmap := fmap_maybeT;
    fmap_id := @fmap_maybeT_id;
    fmap_compose := fmap_maybeT_compose;
  }.
End MaybeT_Functor.
Hint Unfold fmap_maybeT : soundness.
Hint Rewrite @fmap_maybeT_id @fmap_maybeT_compose : soundness.

Section MaybeT_Applicative.
  Context {M} `{M_monad : Monad M}.

  Definition pure_maybeT {A} (x : A) : MaybeT M A :=
    pure (Just x).
  Arguments pure_maybeT [_] _.
  Hint Unfold pure_maybeT : soundness.

  Definition app_maybeT {A B} (Mmf : MaybeT M (A -> B))
    (Mma : MaybeT M A) : MaybeT M B := 
    bindM (M:=M) (A:=(Maybe (A → B))) Mmf (λ mf : Maybe (A → B),
      match mf with
      | Just f =>
          bindM (M:=M) (A:=(Maybe A)) Mma (λ m,
            match m with
            | Just a => pure (M:=M) (Just (f a))
            | None => pure (M:=M) None
            end)
      | None => pure None
      end).
  Arguments app_maybeT [A B] Mmf Mma.
  Hint Unfold app_maybeT : soundness.

  Lemma app_maybeT_id : ∀ {A} (f : MaybeT M A),
    app_maybeT (pure_maybeT id) f = f.
  Proof. 
    intros. unfold app_maybeT, pure_maybeT.
    autorewrite with soundness.
    rewrite <- (bind_id_right (M:=M)). 
    f_equal; ext. destruct x; reflexivity.
  Qed.
  Arguments app_maybeT_id [A] f.

  Lemma app_maybeT_homomorphism : ∀ {A B} (f : A → B) (x : A),
  app_maybeT (pure_maybeT f) (pure_maybeT x) = pure_maybeT (f x).
  Proof. solve_monad. Qed.
  Arguments app_maybeT_homomorphism [A B] f x.

  Lemma app_maybeT_interchange : ∀ {A B} (u : MaybeT M (A → B)) (y : A),
  app_maybeT u (pure_maybeT y) = app_maybeT (pure_maybeT (λ f : A → B, f y)) u.
  Proof. 
    intros. unfold app_maybeT, pure_maybeT.
    autorewrite with soundness. f_equal. ext. 
    destruct x; autorewrite with soundness; reflexivity.
  Qed.
  Arguments app_maybeT_interchange [A B] u y.

  Lemma app_maybeT_compose : ∀ {A B C} (u : MaybeT M (B → C)) 
    (v : MaybeT M (A → B))  (w : MaybeT M A),
    app_maybeT u (app_maybeT v w) =
    app_maybeT (app_maybeT (app_maybeT (pure_maybeT compose) u) v) w.
  Proof. 
    intros. unfold app_maybeT, pure_maybeT. rewrite bind_id_left.
    repeat rewrite bind_assoc. f_equal; ext. destruct x. rewrite bind_id_left.
    repeat rewrite bind_assoc. f_equal; ext. destruct x. rewrite bind_id_left.
    repeat rewrite bind_assoc. f_equal; ext. destruct x. rewrite bind_id_left.
    reflexivity. rewrite bind_id_left. reflexivity. repeat rewrite bind_id_left.
    reflexivity. repeat rewrite bind_id_left. reflexivity.
  Qed.
  Arguments app_maybeT_compose [A B C] u v w.

  Lemma fmap_app_maybeT : ∀ {A B} (f : A → B) (x : MaybeT M A),
  fmap_maybeT f x = app_maybeT (pure_maybeT f) x.
  Proof. 
    intros. unfold fmap_maybeT, app_maybeT, pure_maybeT.
    rewrite bind_id_left. simpl. unfold fmap_maybe.
    rewrite fmap_bind_pure. f_equal. ext. destruct x0; reflexivity.
  Qed.
  Arguments fmap_app_maybeT [A B] f x.

  Lemma pure_maybeT_inj : ∀ (A : Type) (x y : A),
    pure_maybeT x = pure_maybeT y → x = y.
  Proof.
    intros. apply just_inj, pure_inj. easy.
  Qed.

  Global Instance applicative_maybeT : Applicative (MaybeT M) :=
  {
    pure := pure_maybeT;
    pure_inj := pure_maybeT_inj;
    app := app_maybeT;
    app_id := app_maybeT_id;
    app_homomorphism := app_maybeT_homomorphism;
    app_interchange := app_maybeT_interchange;
    app_compose := app_maybeT_compose;
    app_fmap := fmap_app_maybeT;
  }. 
End MaybeT_Applicative.
Hint Unfold pure_maybeT app_maybeT : soundness.
Hint Rewrite @app_maybeT_id @app_maybeT_homomorphism : soundness.
Definition NoneT {M A} `{M_monad : Monad M} : MaybeT M A := pure None.
Hint Unfold NoneT : soundness.
Definition JustT {M A} `{M_monad : Monad M} (a : A) : MaybeT M A := pure (Just a).
Hint Unfold JustT : soundness.

Section maybeT_laws.
  Context {M} `{M_monad : Monad M}.
  Context {A}.

  Lemma justT_eq_noneT_false : ∀ x : A, JustT x ≠ NoneT.
  Proof.
    unfold not. intros. 
    absurd (Just x = None). easy. 
    apply pure_inj. easy. 
  Qed.

  Lemma justT_inj : ∀ x y: A, JustT x = JustT y → x = y.
  Proof.
    intros. apply just_inj, pure_inj. assumption.
  Qed.
End maybeT_laws.

Section MaybeT_Monad.
  Context {M} `{M_monad : Monad M}.

  Definition bind_maybeT {A B} (x : MaybeT M A)
    (f : A -> MaybeT M B) : MaybeT M B :=
    @bindM M _ _ _ (Maybe A) (Maybe B) x (λ v,
      match v with
      | None => NoneT
      | Just a => f a
      end
    ).
  Arguments bind_maybeT [A B] x f.
  Hint Unfold bind_maybeT : soundness.

  Lemma bind_maybeT_id_left : ∀ {A B} (f : A → MaybeT M B) (a : A), 
    bind_maybeT (pure a) f = f a.
  Proof. 
    intros. unfold bind_maybeT. unfold pure. simpl. unfold pure_maybeT.
    rewrite bind_id_left. reflexivity.
  Qed.
  Arguments bind_maybeT_id_left [A B] f a.

  Lemma bind_maybeT_id_right : ∀ {A} (MA : MaybeT M A),
    bind_maybeT MA pure = MA.
  Proof. 
    intros. unfold bind_maybeT. 
    replace (MA) with (bindM (M:=M) MA pure) at 2.
    f_equal. ext; destruct x; reflexivity.
    rewrite <- (bind_id_right (M:=M)). f_equal. 
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

  Lemma bind_maybeT_app : ∀ {A B} (mf : MaybeT M (A → B)) 
    (ma : MaybeT M A),
    mf <*> ma = 
    bind_maybeT mf (λ f : A → B, bind_maybeT ma (λ a : A, (f ∘ pure) a)).
  Proof. simple_solve. Qed.
  Arguments bind_maybeT_app [A B] mf ma.

  Lemma bind_maybeT_fmap : ∀ {A B C} (f : A → B) 
    (x : MaybeT M A) (g : B → MaybeT M C),
    bind_maybeT (fmap f x) g = bind_maybeT x (f ∘ g).
  Proof. 
    intros. unfold bind_maybeT. unfold fmap; simpl. unfold fmap_maybeT.
    rewrite bind_fmap. f_equal. ext. unfold compose. 
    destruct x0; reflexivity.
  Qed.
  Arguments bind_maybeT_fmap [A B C] f x g.

  Lemma bind_maybeT_pass : ∀ {A B} (ma : MaybeT M A) (mb : MaybeT M B),
    ma >> mb = bind_maybeT ma (λ _ : A, mb).
  Proof. 
    intros. unfold bind_maybeT. simpl.
    unfold app_maybeT, fmap_maybeT. autorewrite with soundness.
    f_equal. ext. unfold compose. autorewrite with soundness.
    destruct x; simpl. rewrite <- bind_id_right. f_equal.
    ext. destruct x; autorewrite with soundness. unfold const.
    autorewrite with soundness. all:reflexivity.
  Qed.
  Arguments bind_maybeT_pass [A B] ma mb.

  Global Instance monad_maybeT : Monad (MaybeT M) :=
  {
    bindM := bind_maybeT;
    bind_id_left := bind_maybeT_id_left;
    bind_id_right := bind_maybeT_id_right;
    bind_assoc := bind_maybeT_assoc;
    bind_app := bind_maybeT_app;
    bind_fmap := bind_maybeT_fmap;
    bind_pass := bind_maybeT_pass;
  }. 
End MaybeT_Monad.
Hint Unfold bind_maybeT : soundness.
Hint Rewrite @bind_maybeT_id_left 
             @bind_maybeT_id_right 
             @bind_maybeT_app @bind_maybeT_fmap : soundness.

Section MaybeT_MonadT.
  Context {M} `{M_monad : Monad M}.
  
  Definition lift_maybeT {A} (Ma : M A) : MaybeT M A :=
    bindM (M:=M) Ma (λ a, JustT a).
  Arguments lift_maybeT [_] _.
  Hint Unfold lift_maybeT : soundness.
  Hint Rewrite @fmap_bind @bind_fmap : soundness.

  Lemma lift_maybeT_pure : ∀ (A : Type) (x : A),
    lift_maybeT (pure x) = pure x.
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
    liftT := lift_maybeT;
    lift_pure := lift_maybeT_pure;
    lift_bind := lift_maybeT_bind;
  }. 
End MaybeT_MonadT.

Definition MaybeAT M A : Type := M (AbstractMaybe A).

Section MaybeAT_Functor.
  Context {M} `{M_functor : Functor M}.

  Definition fmap_maybeAT {A B} 
    (f : A -> B) (Ma : MaybeAT M A) : MaybeAT M B :=
    fmap (fmap_abstract_maybe f) Ma.
  Arguments fmap_maybeAT [A B] f Ma.
  Hint Unfold fmap_maybeAT : soundness.

  Lemma fmap_maybeAT_id : ∀ A, fmap_maybeAT (@id A) = id.
  Proof.
    unfold fmap_maybeAT. intros. ext. autorewrite with soundness.
    reflexivity.
  Qed.

  Lemma fmap_maybeAT_compose : ∀ (A B C : Type) (f : A → B) (g : B → C),
    fmap_maybeAT (f ∘ g) = fmap_maybeAT f ∘ fmap_maybeAT g.
  Proof.
    intros. unfold fmap_maybeAT. ext. autorewrite with soundness. reflexivity.
  Qed.

  Global Instance functor_maybeAT : Functor (MaybeAT M) :=
  {
    fmap := fmap_maybeAT;
    fmap_id := fmap_maybeAT_id;
    fmap_compose := fmap_maybeAT_compose;
  }. 
End MaybeAT_Functor.
Hint Unfold fmap_maybeAT : soundness.

Section MaybeAT_Applicative.
  Context {M} `{M_monad : Monad M}.

  Definition pure_maybeAT {A} (x : A) : MaybeAT M A :=
    pure (JustA x).
  Arguments pure_maybeAT [A] x.
  Hint Unfold pure_maybeAT : soundness.

  Definition app_maybeAT {A B} (Mmf : MaybeAT M (A -> B))
    (Mma : MaybeAT M A) : MaybeAT M B :=
    @bindM M _ _ _ _ _ Mmf 
      (λ mf : AbstractMaybe (A -> B),
      match mf with 
      | JustA f => @bindM M _ _ _ _ _ Mma 
          (λ ma : AbstractMaybe A,
          match ma with
          | JustOrNoneA a => pure (JustOrNoneA (f a))
          | JustA a => pure (JustA (f a))
          | NoneA => pure NoneA
          end)
      | JustOrNoneA f => @bindM M _ _ _ _ _ Mma (λ ma : AbstractMaybe A,
          match ma with
          | JustA a | JustOrNoneA a => pure (JustOrNoneA (f a))
          | NoneA => pure NoneA
          end)
      | NoneA => pure NoneA
      end).
  Arguments app_maybeAT [A B] Mmf Mma.
  Hint Unfold app_maybeAT : soundness.

  Lemma app_maybeAT_id : ∀ {A} (f : MaybeAT M A), 
    app_maybeAT (pure_maybeAT id) f = f.
  Proof. 
    intros. unfold app_maybeAT, pure_maybeAT. autorewrite with soundness.
    rewrite <- (bind_id_right (M:=M)). f_equal; ext. 
    destruct_all (AbstractMaybe A); reflexivity.
  Qed.
  Arguments app_maybeAT_id [A] f.

  Lemma app_maybeAT_homomorphism : ∀ {A B} (f : A → B) (x : A),
    app_maybeAT (pure_maybeAT f) (pure_maybeAT x) = pure_maybeAT (f x).
  Proof. 
    intros. unfold app_maybeAT, pure_maybeAT. autorewrite with soundness.
    reflexivity.
  Qed.
  Arguments app_maybeAT_homomorphism [A B] f x.

  Lemma app_maybeAT_interchange : ∀ {A B} (u : MaybeAT M (A → B)) (y : A),
    app_maybeAT u (pure_maybeAT y) = 
    app_maybeAT (pure_maybeAT (λ f : A → B, f y)) u.
  Proof. 
    intros. unfold app_maybeAT, pure_maybeAT. autorewrite with soundness.
    f_equal. ext. destruct x; autorewrite with soundness; reflexivity.
  Qed.
  Arguments app_maybeAT_interchange [A B] u y.

  Lemma app_maybeAT_compose : ∀ {A B C}
    (u : MaybeAT M (B → C)) (v : MaybeAT M (A → B)) (w : MaybeAT M A),
    app_maybeAT u (app_maybeAT v w) =
    app_maybeAT (app_maybeAT (app_maybeAT (pure_maybeAT compose) u) v) w.
  Proof. 
    intros; unfold app_maybeAT, pure_maybeAT; rewrite bind_id_left;
    repeat rewrite bind_assoc; f_equal; ext; destruct x; 
    repeat rewrite bind_id_left; try reflexivity;
    repeat rewrite bind_assoc; f_equal; ext; destruct x;
    repeat rewrite bind_id_left; try reflexivity;
    repeat rewrite bind_assoc; f_equal; ext; destruct x;
    repeat rewrite bind_id_left; reflexivity.
  Qed.
  Hint Unfold fmap_maybeAT : soundness.
  Arguments app_maybeAT_compose [A B C] u v w.

  Lemma app_maybeAT_fmap : ∀ {A B} (f : A → B) (x : MaybeAT M A),
    f <$> x = app_maybeAT (pure_maybeAT f) x.
  Proof.
    intros. unfold app_maybeAT, pure_maybeAT. rewrite bind_id_left.
    unfold fmap; simpl. unfold fmap_maybeAT.
    unfold fmap_abstract_maybe. rewrite fmap_bind_pure.
    f_equal; ext. unfold compose. destruct x0; reflexivity.
  Qed.
  Arguments app_maybeAT_fmap [A B] f x.

  Lemma pure_maybeAT_inj : ∀ (A : Type) (x y : A),
    pure_maybeAT x = pure_maybeAT y → x = y.
  Proof.
    intros. apply justA_inj, pure_inj; auto.
  Qed.

  Global Instance applicative_maybeAT : Applicative (MaybeAT M) :=
  {
    pure := pure_maybeAT;
    pure_inj := pure_maybeAT_inj;
    app := app_maybeAT;
    app_id := app_maybeAT_id;
    app_homomorphism := app_maybeAT_homomorphism;
    app_interchange := app_maybeAT_interchange;
    app_compose := app_maybeAT_compose;
    app_fmap := app_maybeAT_fmap;
  }. 
End MaybeAT_Applicative.
Hint Unfold pure_maybeAT app_maybeAT : soundness.

Definition NoneAT {M A} `{M_monad : Monad M} : MaybeAT M A := pure NoneA.
Hint Unfold NoneAT : soundness.
Definition JustAT {M A} `{M_monad : Monad M} (a : A) : MaybeAT M A := pure (JustA a).
Hint Unfold JustAT : soundness.
Definition JustOrNoneAT {M A} `{M_monad : Monad M} (a : A) : MaybeAT M A := 
  pure (JustOrNoneA a).
Hint Unfold JustOrNoneAT : soundness.

Section MaybeAT_laws.
  Context {M : Type → Type} `{M_monad : Monad M}.
  Context {A}.

  Lemma noneAT_neq_justAT : ∀ (a : A), NoneAT ≠ JustAT a.
  Proof.
    intros. unfold not; intro. absurd (NoneA = JustA a). easy.
    apply pure_inj; easy.
  Qed.

  Lemma noneAT_neq_justornoneAT : ∀ (a : A), NoneAT ≠ JustOrNoneAT a.
  Proof.
    intros. unfold not. intros. absurd (NoneA = JustOrNoneA a). easy.
    apply pure_inj; easy.
  Qed.

  Lemma justAT_neq_justornoneAT : ∀ (a a' : A), 
    JustAT a ≠ JustOrNoneAT a'.
  Proof.
    intros. unfold not. intros. absurd (JustA a = JustOrNoneA a'). easy.
    apply pure_inj. easy.
  Qed.

  Lemma justAT_inj : ∀ (x y : A), JustAT x = JustAT y → x = y.
  Proof.
    intros. apply justA_inj, pure_inj; easy.
  Qed.

  Lemma justOrNoneAT_inj : ∀ (x y : A),
    JustOrNoneAT x = JustOrNoneAT y → x = y.
  Proof.
    intros. apply justOrNoneA_inj, pure_inj. easy.
  Qed.
End MaybeAT_laws.

Section MaybeAT_Monad.
  Context {M} `{M_monad : Monad M}.

  Definition bind_maybeAT {A B} 
    (Mma : MaybeAT M A)
    (f : A -> MaybeAT M B) : MaybeAT M B :=
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
  Hint Unfold bind_maybeAT : soundness.

  Lemma bind_maybeAT_id_left : ∀ {A B} (f : A → MaybeAT M B) (a : A), 
    bind_maybeAT (pure_maybeAT a) f = f a.
  Proof. 
    unfold pure; simpl. intros. unfold bind_maybeAT, pure_maybeAT. 
    rewrite bind_id_left. reflexivity.
  Qed.
  Arguments bind_maybeAT_id_left [A B] f a.

  Lemma bind_maybeAT_id_right : ∀ {A} (MA : MaybeAT M A), 
    bind_maybeAT MA pure_maybeAT = MA.
  Proof. 
    unfold bind_maybeAT. intros. rewrite <- (bind_id_right (M:=M)).
    f_equal; extensionality x. destruct x; unfold pure_maybeAT. reflexivity.
    autorewrite with soundness. reflexivity. reflexivity.
  Qed.
  Arguments bind_maybeAT_id_right [A] MA.

  Lemma bind_maybeAT_assoc : ∀ {A B C} (MA : MaybeAT M A) 
    (f : A → MaybeAT M B) (g : B → MaybeAT M C),
    bind_maybeAT (bind_maybeAT MA f) g =
    bind_maybeAT MA (λ a : A, bind_maybeAT (f a) g).
  Proof. 
    intros. unfold bind_maybeAT. autorewrite with soundness.
    f_equal; ext. destruct x. reflexivity.
    autorewrite with soundness. f_equal; ext.
    destruct x; autorewrite with soundness. 1, 3: reflexivity.
    f_equal; ext. destruct x. autorewrite with soundness.
    reflexivity. autorewrite with soundness. reflexivity.
    autorewrite with soundness. reflexivity.
    autorewrite with soundness. reflexivity.
  Qed.
  Arguments bind_maybeAT_assoc [A B C] MA f g.

  Lemma bind_maybeAT_app : ∀ {A B} (mf : MaybeAT M (A → B)) 
    (ma : MaybeAT M A), app_maybeAT mf ma =
    bind_maybeAT mf (λ f : A → B, bind_maybeAT ma (λ a : A, (f ∘ pure_maybeAT) a)).
  Proof.
    intros. unfold bind_maybeAT, app_maybeAT. autorewrite with soundness. 
    f_equal; ext. destruct x; autorewrite with soundness. 
    f_equal; ext. destruct x. unfold pure_maybeAT.
    unfold compose. reflexivity. unfold pure_maybeAT, compose.
    autorewrite with soundness. reflexivity. reflexivity.
    f_equal; ext. destruct x. unfold compose, pure_maybeAT.
    autorewrite with soundness. reflexivity. unfold compose, pure_maybeAT.
    autorewrite with soundness. reflexivity. autorewrite with soundness.
    reflexivity. reflexivity.
  Qed.
  Arguments bind_maybeAT_app [A B] mf ma.

  Lemma bind_maybeAT_fmap : ∀ {A B C} (f : A → B) (x : MaybeAT M A) 
    (g : B → MaybeAT M C), bind_maybeAT (f <$> x) g = bind_maybeAT x (f ∘ g).
  Proof.
    intros. unfold fmap; simpl; unfold fmap_maybeAT, bind_maybeAT.
    autorewrite with soundness. f_equal; ext. destruct x0;
    unfold compose; autorewrite with soundness; reflexivity.
  Qed.
  Arguments bind_maybeAT_fmap [A B C] f x g.

  Lemma bind_maybeAT_pass : ∀ {A B} (ma : MaybeAT M A) 
    (mb : MaybeAT M B), ma >> mb = bind_maybeAT ma (λ _ : A, mb).
  Proof.
    intros. unfold app; simpl; unfold app_maybeAT, bind_maybeAT, fmap_maybeAT.
    unfold fmap_abstract_maybe. autorewrite with soundness.
    f_equal; ext. unfold compose. 
    autorewrite with soundness.
    destruct x; autorewrite with soundness. rewrite <- bind_id_right.
    f_equal; ext. destruct x; unfold const; autorewrite with soundness;
    reflexivity. reflexivity. reflexivity.
  Qed.
  Arguments bind_maybeAT_pass [A B] ma mb.

  Global Instance monad_maybeAT 
  : Monad (MaybeAT M) :=
  {
    bindM := @bind_maybeAT;
    bind_id_left := bind_maybeAT_id_left;
    bind_id_right := bind_maybeAT_id_right;
    bind_assoc := bind_maybeAT_assoc;
    bind_app := bind_maybeAT_app;
    bind_fmap := bind_maybeAT_fmap;
    bind_pass := bind_maybeAT_pass;
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
    lift_maybeAT (pure x) = pure x.
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
    liftT := lift_maybeAT;
    lift_pure := lift_maybeAT_pure;
    lift_bind := lift_maybeAT_bind;
  }. 
    
End MaybeAT_MonadT.

Definition State (S A : Type) := S -> (A * S).

Section State_Functor.

  Definition fmap_state {S A B} 
    (f : A -> B) (Fa : State S A) : State S B := 
    fun st => let (x, s) := Fa st in (f x, s).
  Arguments fmap_state [S A B] f Fa.
  Hint Unfold fmap_state : soundness.

  Lemma fmap_state_id {S} : ∀ A, fmap_state (S:=S) (@id A) = id.
  Proof. simple_solve. Qed. 

  Lemma fmap_state_compose {S} : ∀ (A B C : Type) (f : A → B) (g : B → C),
    fmap_state (S:=S) (f ∘ g) = fmap_state (S:=S) f ∘ fmap_state (S:=S) g.
  Proof. solve_monad. Qed.

  Global Instance functor_state {S} : Functor (State S) :=
  {
    fmap := @fmap_state S;
    fmap_id := @fmap_state_id S;
    fmap_compose := @fmap_state_compose S;
  }. 

End State_Functor.
Hint Unfold fmap_state : soundness.

Section State_Applicative.
  Context {S : Type}. 

  Definition pure_state {A} (a : A) : State S A :=
    fun st => (a, st).
  Arguments pure_state [A] a.

  Definition app_state {A B} 
    (Mf : State S (A -> B)) (Ma : State S A) : State S B :=
    fun st => let (f, st') := Mf st in 
              let (a, st'') := Ma st' in (f a, st'').
  Arguments app_state [A B] Mf Ma.
  Hint Unfold pure_state app_state : soundness.

  Definition pure_state_inj : ∀ (A : Type) (x y : A),
    @pure_state A x = @pure_state A y → x = y.
  Proof.
    unfold pure_state. intros A x y [= Hfun_eq].
    eapply equal_f in Hfun_eq.
    inversion Hfun_eq. reflexivity. Unshelve.
  Admitted.

  Lemma app_state_id : ∀ (A : Type) (x : State S A),
    app_state (B:=A) (pure_state (@id A)) x = x.
  Proof. simple_solve. Qed.
  
  Lemma app_state_homomorphism : ∀ (A B : Type) (f : A → B) (x : A),
    app_state (pure_state f) (pure_state x) = pure_state (f x).
  Proof. simple_solve. Qed.

  Lemma app_state_interchange : ∀ (A B : Type) (u : State S (A → B)) (y : A),
  app_state u (pure_state y) = 
  app_state (pure_state (λ f : A → B, f y)) u.
  Proof. simple_solve. Qed.

  Lemma app_state_compose : ∀ (A B C : Type) (u : State S (B → C)) 
    (v : State S (A → B)) (w : State S A),
    app_state u (app_state v w) =
    app_state (app_state (app_state (pure_state compose) u) v) w.
  Proof. simple_solve. Qed.

  Lemma app_state_fmap : ∀ (A B : Type) (f : A → B) (x : State S A),
    fmap_state f x = app_state (pure_state f) x.
  Proof. simple_solve. Qed.

  Global Instance applicative_state : Applicative (State S) :=
  {
    pure := pure_state;
    pure_inj := pure_state_inj;
    app := app_state;
    app_id := app_state_id;
    app_homomorphism := app_state_homomorphism;
    app_interchange := app_state_interchange;
    app_compose := app_state_compose;
    app_fmap := app_state_fmap;
  }. 
End State_Applicative.
Hint Unfold app_state : soundness.

Section State_Monad.
  Context {S : Type}.
  Definition bind_state {A B} 
    (p : State S A) (k : A -> State S B) : State S B :=
    fun st => match (p st) with
              | (x, st') => k x st'
              end.
  Arguments bind_state [A B] p k.
  Hint Unfold bind_state : soundness.

  Lemma bind_state_id_left : ∀ (A B : Type) (f : A → State S B) (a : A),
    bind_state (pure a) f = f a.
  Proof. simple_solve. Qed.

  Lemma bind_state_id_right : ∀ (A : Type) (MA : State S A),
    bind_state MA pure = MA.
  Proof. simple_solve. Qed.

  Lemma bind_state_assoc : ∀ (A B C : Type) (MA : State S A) 
    (f : A → State S B) (g : B → State S C),
    bind_state (bind_state MA f) g =
    bind_state MA (λ a : A, bind_state (f a) g).
  Proof. simple_solve. Qed.
  
  Lemma bind_state_app : ∀ (A B : Type) (mf : State S (A → B)) (ma : State S A),
    app_state mf ma = 
    bind_state mf (λ f : A → B, bind_state ma (λ a : A, (f ∘ pure) a)).
  Proof. solve_monad. Qed.

  Lemma bind_state_fmap : ∀ (A B C : Type) (f : A → B) (x : State S A) 
    (g : B → State S C),
    bind_state (fmap_state f x) g = bind_state x (f ∘ g).
  Proof. solve_monad. Qed.

  Lemma bind_state_pass : ∀ (A B : Type) (ma : State S A) (mb : State S B),
    ma >> mb = bind_state ma (λ _ : A, mb).
  Proof. simple_solve. Qed.

  Global Instance monad_state : Monad (State S) :=
  {
    bindM := bind_state;
    bind_id_left := bind_state_id_left;
    bind_id_right := bind_state_id_right;
    bind_assoc := bind_state_assoc;
    bind_app := bind_state_app;
    bind_fmap := bind_state_fmap;
    bind_pass := bind_state_pass;
  }. 
End State_Monad.
Hint Unfold bind_state : soundness.

Definition StateT S M A : Type := S → M (A*S)%type.

Section Functor_StateT.
  Context {M} `{M_monad : Monad M}.

  Definition fmap_stateT {S A B} (f : A -> B) (m : StateT S M A)
    : StateT S M B :=
    fun s : S => bindM (m s) 
      (fun x => let (a, s') := x : (A*S)%type in pure (f a, s')).
  Arguments fmap_stateT [S A B] f m.
  Hint Unfold fmap_stateT : soundness.

  Lemma fmap_stateT_id {S} : ∀ A, fmap_stateT (S:=S) (id (A:=A)) = id.
  Proof.
    unfold fmap_stateT. intros. ext. ext. autorewrite with soundness.
    rewrite <- bind_id_right. f_equal; ext. destruct x1.
    reflexivity.
  Qed.

  Lemma fmap_stateT_compose {S} : ∀ {A B C : Type} (f : A → B) (g : B → C),
  fmap_stateT (S:=S) (f ∘ g) = fmap_stateT f ∘ fmap_stateT g.
  Proof.
    intros. unfold fmap_stateT. unfold compose.
    ext. ext. autorewrite with soundness. f_equal; ext.
    destruct x1. autorewrite with soundness. reflexivity.
  Qed.
  Arguments fmap_stateT_compose [S A B C] f g.

  Global Instance functor_stateT S : Functor (StateT S M) :=
  {
    fmap := @fmap_stateT S;
    fmap_id := @fmap_stateT_id S;
    fmap_compose := @fmap_stateT_compose S;
  }. 
End Functor_StateT.
Hint Unfold fmap_stateT : soundness.

Section Applicative_StateT.
  Context {M} `{M_monad : Monad M}.
  Context {S : Type}.

  Definition pure_stateT {A} (x : A) : StateT S M A :=
    fun s => pure (x, s).
  Arguments pure_stateT [A] x.

  Definition app_stateT {A B}
    (sf : StateT S M (A -> B)) (sa : StateT S M A) : StateT S M B :=
    fun st : S =>
    bindM (sf st) (fun '(f, stf) =>
      bindM (sa stf) (fun '(a, sta) =>
        pure (f a, sta))).
  Arguments app_stateT [A B] sf sa.
  Hint Unfold pure_stateT app_stateT : soundness.

  Lemma app_stateT_id : ∀ (A : Type) (x : StateT S M A), 
    app_stateT (pure_stateT (id (A:=A))) x = x.
  Proof.
    intros. unfold app_stateT, pure_stateT.
    ext. autorewrite with soundness. rewrite <- bind_id_right.
    f_equal. ext. destruct x1. reflexivity.
  Qed.
  Arguments app_stateT_id [A] x.

  Lemma app_stateT_homomorphism : ∀ (A B : Type) (f : A → B) (x : A),
  app_stateT (pure_stateT f) (pure_stateT x) = pure_stateT (f x).
  Proof.
    intros. unfold app_stateT, pure_stateT. ext. autorewrite with soundness.
    reflexivity.
  Qed.
  Arguments app_stateT_homomorphism [A B] f x.

  Lemma app_stateT_interchange : ∀ (A B : Type) 
    (u : StateT S M (A → B)) (y : A),
  app_stateT u (pure_stateT y) = app_stateT (pure_stateT (λ f : A → B, f y)) u.
  Proof.
    intros. autounfold with soundness. ext. autorewrite with soundness.
    f_equal; ext. destruct x0. autorewrite with soundness. reflexivity.
  Qed.
  Arguments app_stateT_interchange [A B] u y.

  Lemma app_stateT_compose : ∀ (A B C : Type) (u : StateT S M (B → C)) 
    (v : StateT S M (A → B)) (w : StateT S M A),
  app_stateT u (app_stateT v w) =
  app_stateT (app_stateT (app_stateT (pure_stateT compose) u) v) w.
  Proof.
    intros. autounfold with soundness. ext. autorewrite with soundness.
    f_equal; ext. destruct x0. autorewrite with soundness.
    f_equal; ext. destruct x0. autorewrite with soundness.
    f_equal; ext. destruct x0. autorewrite with soundness. unfold compose.
    reflexivity.
  Qed.
  Arguments app_stateT_compose [A B C] u v w.

  Lemma app_stateT_fmap : ∀ (A B : Type) (f : A → B) (x : StateT S M A),
    fmap f x = app_stateT (pure_stateT f) x.
  Proof.
    simple_solve.
  Qed.

  Lemma pure_stateT_inj : ∀ (A : Type) (x y : A),
    pure_stateT x = pure_stateT y → x = y.
  Proof. 
    intros A x y Hfun_eq. unfold pure_stateT in Hfun_eq.
    eapply equal_f in Hfun_eq. apply pure_inj in Hfun_eq.
    inversion Hfun_eq. reflexivity.
  Admitted.

  Global Instance applicative_stateT : Applicative (StateT S M) :=
  {
    pure := pure_stateT;
    pure_inj := pure_stateT_inj;
    app := app_stateT;
    app_id := app_stateT_id;
    app_homomorphism := app_stateT_homomorphism;
    app_interchange := app_stateT_interchange;
    app_compose := app_stateT_compose;
    app_fmap := app_stateT_fmap;
  }. 
End Applicative_StateT.
Hint Unfold pure_stateT app_stateT : soundness.

Section Monad_StateT.
  Context {M} `{M_monad : Monad M}.
  Context {S : Type}.

  Definition bind_stateT {A B} (MA : StateT S M A) 
    (f : A -> StateT S M B) : StateT S M B :=
    fun st => bindM (MA st) 
      (fun p : (A*S)%type => let (a,st') := p in f a st').
  Arguments bind_stateT [A B] MA f.
  Hint Unfold bind_stateT : soundness.

  Lemma bind_stateT_id_left : ∀ (A B : Type) (f : A → StateT S M B) (a : A), 
    bind_stateT (pure_stateT a) f = f a.
  Proof.
    autounfold with soundness. intros. ext. 
    rewrite bind_id_left. reflexivity.
  Qed.
  Arguments bind_stateT_id_left [A B] f a.

  Lemma bind_stateT_id_right : ∀ (A : Type) (MA : StateT S M A), 
    bind_stateT MA pure_stateT = MA.
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
  
  Lemma bind_stateT_app : ∀ (A B : Type) (mf : StateT S M (A → B)) 
    (ma : StateT S M A), 
    app_stateT mf ma =
  bind_stateT mf (λ f : A → B,  bind_stateT ma (λ a : A, (f ∘ pure_stateT) a)).
  Proof.
    autounfold with soundness. intros.
    ext. f_equal.
  Qed.
  Arguments bind_stateT_app [A B] mf ma.

  Lemma bind_stateT_fmap :  ∀ (A B C : Type) (f : A → B) (x : StateT S M A) 
    (g : B → StateT S M C),
    bind_stateT (fmap_stateT f x) g = bind_stateT x (f ∘ g).
  Proof.
    autounfold with soundness. intros. ext. autorewrite with soundness.
    f_equal; ext. destruct x1. autorewrite with soundness.
    reflexivity.
  Qed.
  Arguments bind_stateT_fmap [A B C] f x g.

  Lemma bind_stateT_pass : ∀ (A B : Type) (ma : StateT S M A) 
    (mb : StateT S M B),
  ma >> mb = bind_stateT ma (λ _ : A, mb).
  Proof.
    intros. simpl. autounfold with soundness. 
    ext. autorewrite with soundness. f_equal.
    ext. destruct x0. autorewrite with soundness. rewrite <- bind_id_right.
    f_equal. ext. destruct x0. unfold const. reflexivity.
  Qed.
  Arguments bind_stateT_pass [A B] ma mb.

  Global Instance monad_stateT : Monad (StateT S M) :=
  {
    bindM := bind_stateT;
    bind_id_left := bind_stateT_id_left;
    bind_id_right := bind_stateT_id_right;
    bind_assoc := bind_stateT_assoc;
    bind_app := bind_stateT_app;
    bind_fmap := bind_stateT_fmap;
    bind_pass := bind_stateT_pass;
  }. 
End Monad_StateT.
Hint Unfold bind_stateT : soundness.

Section MonadT_StateT.
  Context {M} `{M_monad :Monad M}.
  Context {S : Type}.

  Definition lift_stateT {A} (MA : M A) : StateT S M A :=
    fun st => bindM MA (fun a => pure (a, st)).
  Arguments lift_stateT [A] MA.
  Hint Unfold lift_stateT : soundness.
  
  Lemma lift_stateT_pure : ∀ (A : Type) (x : A), 
    lift_stateT (pure x) = pure_stateT x.
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
    lift_pure := lift_stateT_pure;
    lift_bind := lift_stateT_bind;
  }. 
End MonadT_StateT.
