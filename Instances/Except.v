Require Import Classes.Monad.MonadExcept.
Require Import Classes.Monad.MonadFail.
Require Import Classes.Joinable.
Require Import Classes.Monad.
Require Import Classes.PreorderedSet.
Require Import Instances.Joinable.
Require Import Instances.Monad.
Require Import Types.Stores.
Require Import Types.Maybe.
Require Import Types.State.

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

  Lemma catch_maybe_return : ∀ {A : Type} (x : Maybe A) (a : A),
    catch_maybe (returnM a) x = returnM a.
  Proof.
    reflexivity. 
  Qed.

  Global Instance except_maybe : ∀ A, MonadExcept Maybe A :=
  {
    catch_left := catch_maybe_throw_left;
    catch_right := catch_maybe_throw_right;
    catch_return := catch_maybe_return;
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
    intros. destruct x; simpl; unfold join_op; simpl; reflexivity.
  Qed.

  Lemma catch_abstract_maybe_return : ∀ (x : AbstractMaybe A) (a : A),
    catch_abstract_maybe (returnM a) x = returnM a.
  Proof.
    reflexivity. 
  Qed.

  Global Instance fail_maybeA : MonadExcept AbstractMaybe A :=
  {
    catch_left := catch_abstract_maybe_throw_left;
    catch_right := catch_abstract_maybe_throw_right;
    catch_return := catch_abstract_maybe_return;
  }.
End except_abstract_maybe.

Section fail_maybeT.
  Context {M} `{M_monad : Monad M}.

  Definition fail_maybeT {A} : MaybeT M A := returnM None.

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
    bindM (M:=M) mx (fun x : Maybe A =>
      match x with
      | None => my
      | Just a => returnM (Just a)
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
    replace x with (bindM (M:=M) x returnM) at 2.
    f_equal; ext; destruct x0; reflexivity.
    rewrite <- (bind_id_right (M:=M)). f_equal.
  Qed.

  Lemma catch_maybeT_return : ∀ {A : Type} (x : MaybeT M A) (a : A),
    catch_maybeT (returnM a) x = returnM a.
  Proof.
    unfold catch_maybeT. intros. unfold returnM; simpl; unfold JustT. 
    rewrite bind_id_left. reflexivity.
  Qed.

  Global Instance except_maybeT {A} : MonadExcept (MaybeT M) A :=
  {
    catch_left := catch_maybeT_throw_left;
    catch_right := catch_maybeT_throw_right;
    catch_return := catch_maybeT_return;
  }. 
End except_maybeT.

Section fail_maybeAT.
  Context {M : Type → Type} `{M_monad : Monad M}.

  Definition fail_maybeAT {A} : MaybeAT M A := returnM NoneA.

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
      | JustA a => returnM (JustA a)
      | JustOrNoneA a => returnM (JustOrNoneA a) (* should be a join_op *)
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

  Lemma catch_maybeAT_return : ∀ {A} (x : MaybeAT M A) (a : A),
    catch_maybeAT (returnM a) x = returnM a.
  Proof.
    unfold catch_maybeAT. intros. unfold returnM; simpl; unfold JustAT. 
    rewrite bind_id_left. reflexivity.
  Qed.

  Global Instance except_maybeAT {A} : MonadExcept (MaybeAT M) A :=
    {
      catch_left := catch_maybeAT_throw_left;
      catch_right := catch_maybeAT_throw_right;
      catch_return := catch_maybeAT_return;
    }. 
End except_maybeAT.

Section fail_stateT.
  Context {M : Type -> Type} `{M_fail : MonadFail M}.
  Context {S : Type} `{!Inhabited S}.

  Definition fail_stateT {A} : StateT S M A := lift_stateT fail.

  Lemma fail_stateT_left : ∀ (A B : Type) (s : A → StateT S M B),
    fail_stateT (A:=A) >>= s = fail_stateT.
  Proof.
    intros. unfold fail_stateT, lift_stateT. ext. 
    autorewrite with soundness. 
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
  Context {S : Type} `{!Inhabited S}.

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

  Lemma catch_stateT_return : ∀ {A} (x : StateT S M A) (a : A),
    catch_stateT (returnM a) x = returnM a.
  Proof.
    intros. unfold catch_stateT. ext. unfold returnM. simpl. unfold return_stateT.
    rewrite catch_return. reflexivity.
  Qed.

  Instance except_stateT {A} : MonadExcept (StateT S M) A :=
  {
    catch_left := catch_stateT_throw_left;
    catch_right := catch_stateT_throw_right;
    catch_return := catch_stateT_return;
  }. 
End except_stateT.
