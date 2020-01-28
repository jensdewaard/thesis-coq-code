Require Import Classes.Applicative.
Require Import Classes.Monad.MonadExcept.
Require Import Classes.Monad.MonadFail.
Require Import Classes.Joinable.
Require Import Classes.Monad.
Require Import Classes.Functor.
Require Import Classes.PreorderedSet.
Require Import Instances.Joinable.
Require Import Instances.Monad.
Require Import Types.Stores.

Implicit Type A : Type.
Implicit Type M : Type → Type.

Section fail_maybe.
  Lemma none_left : ∀ {A B} (f : A → Maybe B), bind_maybe (@None A) f = None.
  Proof.
    reflexivity.
  Qed.
      
  Global Instance fail_maybe : MonadFail Maybe :=
  {
    fail := @None;
    fail_left := @none_left;
  }.
End fail_maybe.

Section except_maybe.
  Definition catch_maybe {A} (x y : Maybe A) : Maybe A :=
    match x with
    | None => y
    | _ => x
    end.
  Hint Unfold catch_maybe : soundness.

  Lemma catch_maybe_throw_left : ∀ {A} (x : Maybe A),
    catch_maybe None x = x.
  Proof. simple_solve. Qed.

  Lemma catch_maybe_throw_right : ∀ {A} (x : Maybe A),
    catch_maybe x None = x.
  Proof. simple_solve. Qed.

  Lemma catch_maybe_assoc  : ∀ {A : Type} (x y z : Maybe A),
    catch_maybe x (catch_maybe y z) = catch_maybe (catch_maybe x y) z.
  Proof.
    intros. destruct_all (Maybe A); reflexivity.
  Qed.

  Lemma catch_maybe_pure : ∀ {A : Type} (x : Maybe A) (a : A),
    catch_maybe (pure a) x = pure a.
  Proof.
    reflexivity. 
  Qed.

  Global Instance except_maybe : ∀ A, MonadExcept Maybe A :=
  {
    catch := catch_maybe;
    catch_left := catch_maybe_throw_left;
    catch_right := catch_maybe_throw_right;
    catch_assoc := catch_maybe_assoc;
    catch_pure := catch_maybe_pure;
  }.
End except_maybe.

Section fail_abstract_maybe.
  Lemma noneA_left : ∀ (A B : Type) (f : A → AbstractMaybe B), 
     (@NoneA A) >>= f = NoneA.
  Proof.
    simple_solve.
  Qed.

  Global Instance fail_abstract_maybe : MonadFail AbstractMaybe :=
  {
    fail := @NoneA;
    fail_left := noneA_left;
  }.
End fail_abstract_maybe.

Section except_abstract_maybe.
  Context {A} `{A_joinable : Joinable A}.
  Definition catch_abstract_maybe (x y : AbstractMaybe A) : AbstractMaybe A :=
    match x with
    | NoneA => y
    | JustA a => x 
    | JustOrNoneA a => join_op x y
    end.

  Lemma catch_abstract_maybe_throw_left : ∀ (x : AbstractMaybe A),
    catch_abstract_maybe NoneA x = x.
  Proof. reflexivity. Qed.

  Lemma catch_abstract_maybe_throw_right : ∀ (x : AbstractMaybe A),
    catch_abstract_maybe x NoneA = x.
  Proof.
    intros. destruct x; simpl. 2: unfold join_op; simpl. 
  Admitted.

  Lemma catch_abstract_maybe_pure : ∀ (x : AbstractMaybe A) (a : A),
    catch_abstract_maybe (pure a) x = pure a.
  Proof.
    reflexivity. 
  Qed.

  Lemma catch_abstract_maybe_assoc : ∀ (x y z : AbstractMaybe A),
    catch_abstract_maybe x (catch_abstract_maybe y z) =
    catch_abstract_maybe (catch_abstract_maybe x y) z.
  Proof.
    intros. destruct x as [a1|a1|] eqn:Hx; 
    destruct y as [a2|a2|] eqn:Hy; 
    destruct z as [a3|a3|] eqn:Hz; simpl; try reflexivity.
    - unfold join_op; simpl. admit.
    - unfold join_op; simpl. admit.
    - unfold join_op; simpl. admit.
    - unfold join_op; simpl. rewrite join_assoc. reflexivity.
  Admitted.

  Global Instance fail_maybeA : MonadExcept AbstractMaybe A :=
  {
    catch := catch_abstract_maybe;
    catch_left := catch_abstract_maybe_throw_left;
    catch_right := catch_abstract_maybe_throw_right;
    catch_pure := catch_abstract_maybe_pure;
    catch_assoc := catch_abstract_maybe_assoc;
  }.
End except_abstract_maybe.

Section fail_maybeT.
  Context {M} `{M_monad : Monad M}.

  Definition fail_maybeT {A} : MaybeT M A := pure None.

  Lemma fail_maybeT_left : ∀ (A B : Type) (m : A → MaybeT M B), 
    bind_maybeT fail_maybeT m = fail_maybeT.
  Proof.
    intros. unfold bind_maybeT, fail_maybeT, NoneT. autorewrite with soundness.
    reflexivity.
  Qed.

  Global Instance monad_fail_maybeT : MonadFail (MaybeT M) :=
  {
    fail := @fail_maybeT;
    fail_left := @fail_maybeT_left;
  }.
End fail_maybeT.

Section except_maybeT.
  Context {M} `{M_monad : Monad M}.

  Definition catch_maybeT {A} (mx my : MaybeT M A) : MaybeT M A :=
    @bindM M _ _ _ _ _ mx (fun x : Maybe A =>
      match x with
      | None => my
      | Just a => pure (Just a)
      end).
  Hint Unfold catch_maybeT : soundness.

  Lemma catch_maybeT_throw_left : ∀ {A : Type} (x : MaybeT M A), 
    catch_maybeT fail_maybeT x = x.
  Proof.
    intros. unfold catch_maybeT, fail_maybeT.
    autorewrite with soundness. reflexivity.
  Qed.

  Lemma catch_maybeT_throw_right : ∀ {A : Type} (x : MaybeT M A), 
    catch_maybeT x fail_maybeT = x.
  Proof.
    unfold catch_maybeT, fail_maybeT. intros.
    replace x with (bindM (M:=M) x pure) at 2.
    f_equal; ext; destruct x0; reflexivity.
    rewrite <- (bind_id_right (M:=M)). f_equal.
  Qed.

  Lemma catch_maybeT_assoc : ∀ {A : Type} (x y z : MaybeT M A),
    catch_maybeT x (catch_maybeT y z) = catch_maybeT (catch_maybeT x y) z.
  Proof.
    intros. unfold catch_maybeT. autorewrite with soundness. f_equal. 
    extensionality m. destruct m; autorewrite with soundness. reflexivity.
    f_equal.
  Qed.

  Lemma catch_maybeT_pure : ∀ {A : Type} (x : MaybeT M A) (a : A),
    catch_maybeT (pure a) x = pure a.
  Proof.
    unfold catch_maybeT. intros. unfold pure; simpl; unfold pure_maybeT. 
    rewrite bind_id_left. reflexivity.
  Qed.

  Global Instance except_maybeT {A} : MonadExcept (MaybeT M) A :=
  {
    catch := catch_maybeT;
    catch_left := catch_maybeT_throw_left;
    catch_right := catch_maybeT_throw_right;
    catch_assoc := catch_maybeT_assoc;
    catch_pure := catch_maybeT_pure;
  }. 
End except_maybeT.

Section fail_maybeAT.
  Context {M : Type → Type} `{M_monad : Monad M}.

  Definition fail_maybeAT {A} : MaybeAT M A := pure NoneA.

  Lemma fail_maybeAT_left : ∀ (A B : Type) (m : A → MaybeAT M B), 
    bind_maybeAT (A:=A) (B:=B) fail_maybeAT m = fail_maybeAT (A:=B).
  Proof. 
    unfold bind_maybeAT, fail_maybeAT; simpl. intros. 
    autorewrite with soundness. reflexivity.
  Qed.

  Global Instance monad_fail_maybeAT : MonadFail (MaybeAT M) :=
  {
     fail := @fail_maybeAT;
     fail_left := @fail_maybeAT_left;
  }.
End fail_maybeAT.

Section except_maybeAT.
  Context {M : Type -> Type} `{M_monad : Monad M}.

  Definition catch_maybeAT {A}
    (mx my : MaybeAT M A) : MaybeAT M A :=
    bindM (M:=M) mx (fun x : AbstractMaybe A =>
      match x with
      | JustA a => pure (JustA a)
      | JustOrNoneA a => pure (JustOrNoneA a) (* should be a join_op *)
      | NoneA => my
      end).

  Lemma catch_maybeAT_throw_left : ∀ {A} (x : MaybeAT M A),
    catch_maybeAT fail_maybeAT x = x.
  Proof. 
    intros. unfold catch_maybeAT, fail_maybeAT. autorewrite with soundness.
    reflexivity.
  Qed.

  Lemma catch_maybeAT_throw_right : ∀ {A} (x : MaybeAT M A),
    catch_maybeAT x fail_maybeAT = x.
  Proof. 
    intros. unfold catch_maybeAT, fail_maybeAT. rewrite <- (bind_id_right (M:=M)).
    f_equal; extensionality m. destruct m; reflexivity.
  Qed.

  Lemma catch_maybeAT_assoc : ∀ {A} (x y z : MaybeAT M A),
    catch_maybeAT x (catch_maybeAT y z) = catch_maybeAT (catch_maybeAT x y) z.
  Proof.
    intros. unfold catch_maybeAT. rewrite bind_assoc. f_equal. 
    extensionality m. destruct m. 1-2: rewrite bind_id_left; reflexivity.
    f_equal.
  Qed.

  Lemma catch_maybeAT_pure : ∀ {A} (x : MaybeAT M A) (a : A),
    catch_maybeAT (pure a) x = pure a.
  Proof.
    unfold catch_maybeAT. intros. unfold pure; simpl; unfold pure_maybeAT. 
    rewrite bind_id_left. reflexivity.
  Qed.

  Global Instance except_maybeAT {A} : MonadExcept (MaybeAT M) A :=
    {
      catch := catch_maybeAT;
      catch_left := catch_maybeAT_throw_left;
      catch_right := catch_maybeAT_throw_right;
      catch_assoc := catch_maybeAT_assoc;
      catch_pure := catch_maybeAT_pure;
    }. 
End except_maybeAT.

Section fail_stateT.
  Context {M : Type -> Type} `{M_fail : MonadFail M}.
  Context {S : Type}.

  Definition fail_stateT {A} : StateT S M A := lift_stateT fail.

  Lemma fail_stateT_left : ∀ (A B : Type) (s : A → StateT S M B),
    fail_stateT (A:=A) >>= s = fail_stateT.
  Proof.
    intros. unfold fail_stateT, lift_stateT. ext. 
    autorewrite with soundness. unfold app_stateT, fmap_stateT. 
    unfold bindM; simpl; unfold bind_stateT. 
    autorewrite with soundness. reflexivity.
  Qed.

  Global Instance monad_fail_stateT : MonadFail (StateT S M) :=
  {
    fail := @fail_stateT;
    fail_left := fail_stateT_left;
  }.
End fail_stateT.

Section except_stateT.
  Context {M : Type → Type} `{M_fail : MonadFail M} 
    `{M_except : ∀ A, MonadExcept M A}.
  Context {S : Type}.

  Definition catch_stateT {A} (a b : StateT S M A) : StateT S M A := 
    fun s => catch (a s) (b s).
  Hint Unfold fail_stateT catch_stateT : soundness.

  Lemma catch_stateT_throw_left : ∀ {A} (x : StateT S M A),
    catch_stateT fail_stateT x = x.
  Proof. 
    intros. unfold catch_stateT, fail_stateT, lift_stateT.
    ext. autorewrite with soundness. reflexivity.
  Qed.

  Lemma catch_stateT_throw_right : ∀ {A} (x : StateT S M A),
    catch_stateT x fail_stateT = x.
  Proof. 
    intros. unfold catch_stateT, fail_stateT, lift_stateT.
    ext. autorewrite with soundness. reflexivity.
  Qed.

  Lemma catch_stateT_assoc : ∀ {A} (x y z: StateT S M A),
    catch_stateT x (catch_stateT y z) = catch_stateT (catch_stateT x y) z.
  Proof.
    intros. unfold catch_stateT. ext. rewrite catch_assoc. reflexivity.
  Qed.

  Lemma catch_stateT_pure : ∀ {A} (x : StateT S M A) (a : A),
    catch_stateT (pure a) x = pure a.
  Proof.
    intros. unfold catch_stateT. ext. unfold pure. simpl. unfold pure_stateT.
    rewrite catch_pure. reflexivity.
  Qed.

  Instance except_stateT {A} : MonadExcept (StateT S M) A :=
  {
    catch := catch_stateT;
    catch_left := catch_stateT_throw_left;
    catch_right := catch_stateT_throw_right;
    catch_assoc := catch_stateT_assoc;
    catch_pure := catch_stateT_pure;
  }. 
End except_stateT.
