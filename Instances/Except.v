Require Import Classes.Monad.MonadExcept.
Require Import Classes.Monad.MonadFail.
Require Import Classes.Joinable.
Require Import Classes.Monad.
Require Import Classes.PreorderedSet.
Require Import Instances.Joinable.
Require Import Instances.Monad.
Require Import Types.Stores.
Require Import Types.State.

Implicit Type A : Type.
Implicit Type M : Type → Type.

Section fail_option.
  Lemma none_left : ∀ {A B} (f : A → option B), bind_option (@None A) f = None.
  Proof.
    reflexivity.
  Qed.
      
  Global Instance fail_option : MonadFail option :=
  {
    fail := @None;
    fail_left := @none_left;
  }.
End fail_option.

Section except_option.
  Definition catch_option {A} (x y : option A) : option A :=
    match x with
    | None => y
    | _ => x
    end.
  Hint Unfold catch_option : soundness.

  Lemma catch_option_throw_left : ∀ {A} (x : option A),
    catch_option None x = x.
  Proof. simple_solve. Qed.

  Lemma catch_option_throw_right : ∀ {A} (x : option A),
    catch_option x None = x.
  Proof. simple_solve. Qed.

  Lemma catch_option_return : ∀ {A : Type} (x : option A) (a : A),
    catch_option (returnM a) x = returnM a.
  Proof.
    reflexivity. 
  Qed.

  Global Instance except_option : ∀ A, MonadExcept option A :=
  {
    catch_left := catch_option_throw_left;
    catch_right := catch_option_throw_right;
    catch_return := catch_option_return;
  }.
End except_option.

Section fail_optionA.
  Lemma noneA_left : ∀ (A B : Type) (f : A → optionA B), 
     (@NoneA A) >>= f = NoneA.
  Proof.
    simple_solve.
  Qed.

  Global Instance fail_optionA : MonadFail optionA :=
  {
    fail := @NoneA;
    fail_left := noneA_left;
  }.
End fail_optionA.

Section except_optionA.
  Context {A} `{A_joinable : Joinable A A}.
  Definition catch_optionA (x y : optionA A) : optionA A :=
    match x with
    | NoneA => y
    | SomeA a => x
    | SomeOrNoneA a => x ⊔ y
    end.

  Lemma catch_optionA_throw_left : ∀ (x : optionA A),
    catch_optionA NoneA x = x.
  Proof. reflexivity. Qed.

  Lemma catch_optionA_throw_right : ∀ (x : optionA A),
    catch_optionA x NoneA = x.
  Proof.
    intros. destruct x; simpl; reflexivity. 
  Qed.

  Lemma catch_optionA_return : ∀ (x : optionA A) (a : A),
    catch_optionA (returnM a) x = returnM a.
  Proof.
    reflexivity. 
  Qed.

  Global Instance except_optionA : MonadExcept optionA A :=
  {
    catch_left := catch_optionA_throw_left;
    catch_right := catch_optionA_throw_right;
    catch_return := catch_optionA_return;
  }.
End except_optionA.

Section fail_optionT.
  Context {M} `{M_monad : Monad M}.

  Definition fail_optionT {A} : optionT M A := returnM None.

  Lemma fail_optionT_left : ∀ (A B : Type) (m : A → optionT M B), 
    bind_optionT fail_optionT m = fail_optionT.
  Proof.
    intros. unfold bind_optionT, fail_optionT. autorewrite with soundness.
    reflexivity.
  Qed.

  Global Instance monad_fail_optionT : MonadFail (optionT M) :=
  {
    fail := @fail_optionT;
    fail_left := @fail_optionT_left;
  }.
End fail_optionT.

Section except_optionT.
  Context {M} `{M_monad : Monad M}.

  Definition catch_optionT {A} (mx my : optionT M A) : optionT M A :=
    bindM (M:=M) mx (fun x : option A =>
      match x with
      | None => my
      | Some a => returnM (Some a)
      end).
  Hint Unfold catch_optionT : soundness.

  Lemma catch_optionT_throw_left : ∀ {A : Type} (x : optionT M A), 
    catch_optionT fail_optionT x = x.
  Proof.
    intros. unfold catch_optionT, fail_optionT.
    autorewrite with soundness. reflexivity.
  Qed.

  Lemma catch_optionT_throw_right : ∀ {A : Type} (x : optionT M A), 
    catch_optionT x fail_optionT = x.
  Proof.
    unfold catch_optionT, fail_optionT. intros.
    replace x with (bindM (M:=M) x returnM) at 2.
    f_equal; ext; destruct x0; reflexivity.
    rewrite <- (bind_id_right (M:=M)). f_equal.
  Qed.

  Lemma catch_optionT_return : ∀ {A : Type} (x : optionT M A) (a : A),
    catch_optionT (returnM a) x = returnM a.
  Proof.
    unfold catch_optionT. intros. unfold returnM; simpl.
    rewrite bind_id_left. reflexivity.
  Qed.

  Global Instance except_optionT {A} : MonadExcept (optionT M) A :=
  {
    catch_left := catch_optionT_throw_left;
    catch_right := catch_optionT_throw_right;
    catch_return := catch_optionT_return;
  }. 
End except_optionT.

Section fail_optionAT.
  Context {M : Type → Type} `{M_monad : Monad M}.

  Definition fail_optionAT {A} : optionAT M A := returnM NoneA.

  Lemma fail_optionAT_left : ∀ (A B : Type) (m : A → optionAT M B), 
    bind_optionAT (A:=A) (B:=B) fail_optionAT m = fail_optionAT (A:=B).
  Proof. 
    unfold bind_optionAT, fail_optionAT; simpl. intros. 
    autorewrite with soundness. reflexivity.
  Qed.

  Global Instance monad_fail_optionAT : MonadFail (optionAT M) :=
  {
     fail := @fail_optionAT;
     fail_left := @fail_optionAT_left;
  }.
End fail_optionAT.

Section except_optionAT.
  Context {M : Type -> Type} `{M_monad : Monad M}.

  Definition catch_optionAT {A}
    (mx my : optionAT M A) : optionAT M A :=
    bindM (M:=M) mx (fun x : optionA A =>
      match x with
      | SomeA a => returnM (SomeA a)
      | SomeOrNoneA a => returnM (SomeOrNoneA a) (* should be a join_op *)
      | NoneA => my
      end).

  Lemma catch_optionAT_throw_left : ∀ {A} (x : optionAT M A),
    catch_optionAT fail_optionAT x = x.
  Proof. 
    intros. unfold catch_optionAT, fail_optionAT. autorewrite with soundness.
    reflexivity.
  Qed.

  Lemma catch_optionAT_throw_right : ∀ {A} (x : optionAT M A),
    catch_optionAT x fail_optionAT = x.
  Proof. 
    intros. unfold catch_optionAT, fail_optionAT. rewrite <- (bind_id_right (M:=M)).
    f_equal; extensionality m. destruct m; reflexivity.
  Qed.

  Lemma catch_optionAT_return : ∀ {A} (x : optionAT M A) (a : A),
    catch_optionAT (returnM a) x = returnM a.
  Proof.
    unfold catch_optionAT. intros. unfold returnM; simpl.
    rewrite bind_id_left. reflexivity.
  Qed.

  Global Instance except_optionAT {A} : MonadExcept (optionAT M) A :=
    {
      catch_left := catch_optionAT_throw_left;
      catch_right := catch_optionAT_throw_right;
      catch_return := catch_optionAT_return;
    }. 
End except_optionAT.

Section fail_stateT.
  Context {M : Type -> Type} `{M_fail : MonadFail M}.
  Context {S : Type}.

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
