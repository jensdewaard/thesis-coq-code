Require Import Classes.Monad.MonadExcept.
Require Import Classes.Monad.MonadFail.
Require Import Classes.Monad.MonadJoin.
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
  Lemma none_left : ∀ A B (f : A → option B), bind_option (@None A) f = None.
  Proof.
    reflexivity.
  Qed.
      
  Global Instance fail_option : MonadFail option :=
  {
    fail := @None;
    fail_left := none_left;
  }.
End fail_option.

Section except_option.
  Definition catch_option {A} {JA : Joinable A A} (x y : option A) : option A :=
    match x with
    | None => y
    | _ => x
    end.
  Hint Unfold catch_option : monads.

  Lemma catch_option_throw_left : ∀ (A : Type) (JA : Joinable A A) (x : option A),
    catch_option None x = x.
  Proof. simple_solve. Qed.

  Lemma catch_option_throw_right : ∀ A (JA : Joinable A A) (x : option A),
    catch_option x None = x.
  Proof. simple_solve. Qed.

  Lemma catch_option_return : ∀ A (JA : Joinable A A) (x : option A) (a : A),
    catch_option (returnM a) x = returnM a.
  Proof.
    reflexivity. 
  Qed.

  Global Instance except_option : MonadExcept option :=
  {
    throw_left := none_left;
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
  Definition catch_optionA {A : Type} {JA : Joinable A A} (x y : optionA A) : optionA A :=
    match x with
    | NoneA => y
    | SomeA a => x
    | SomeOrNoneA a => x ⊔ y
    end.

  Lemma catch_optionA_throw_left : ∀ A {JA : Joinable A A} (x : optionA A),
    catch_optionA NoneA x = x.
  Proof. reflexivity. Qed.

  Lemma catch_optionA_throw_right : ∀ A {JA : Joinable A A} (x : optionA A),
    catch_optionA x NoneA = x.
  Proof.
    intros. destruct x; simpl; reflexivity. 
  Qed.

  Lemma catch_optionA_return : ∀ A {JA : Joinable A A} (x : optionA A) (a : A),
    catch_optionA (returnM a) x = returnM a.
  Proof.
    reflexivity. 
  Qed.

  Global Instance except_optionA : MonadExcept optionA :=
  {
    throw_left := noneA_left;
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
    intros. unfold bind_optionT, fail_optionT. autorewrite with monads.
    reflexivity.
  Qed.

  Global Instance monad_fail_optionT : MonadFail (optionT M) :=
  {
    fail := @fail_optionT;
    fail_left := @fail_optionT_left;
  }.
End fail_optionT.

Section except_optionT.
  Context M {MM : Monad M}.

  Definition catch_optionT {A} {JA : Joinable A A} (mx my : optionT M A) : 
    optionT M A :=
    bindM (M:=M) mx (fun x : option A =>
      match x with
      | None => my
      | Some a => returnM (Some a)
      end).
  Hint Unfold catch_optionT : monads.

  Lemma catch_optionT_throw_left : ∀ (A : Type) {JA : Joinable A A} 
    (x : optionT M A), 
    catch_optionT fail_optionT x = x.
  Proof.
    intros. unfold catch_optionT, fail_optionT.
    autorewrite with monads. reflexivity.
  Qed.

  Lemma catch_optionT_throw_right : ∀ (A : Type) {JA : Joinable A A} 
  (x : optionT M A), 
    catch_optionT x fail_optionT = x.
  Proof.
    unfold catch_optionT, fail_optionT. intros.
    replace x with (bindM (M:=M) x returnM) at 2.
    f_equal; ext; destruct x0; reflexivity.
    rewrite <- (bind_id_right (M:=M)). f_equal.
  Qed.

  Lemma catch_optionT_return : ∀ (A : Type) {JA : Joinable A A} 
  (x : optionT M A) (a : A),
    catch_optionT (returnM a) x = returnM a.
  Proof.
    unfold catch_optionT. intros. unfold returnM; simpl.
    rewrite bind_id_left. reflexivity.
  Qed.

  Global Instance except_optionT : MonadExcept (optionT M) :=
  {
    throw_left := @fail_optionT_left M _;
    catch_left := catch_optionT_throw_left;
    catch_right := catch_optionT_throw_right;
    catch_return := catch_optionT_return;
  }. 
End except_optionT.
Hint Resolve except_optionT : soundness.

Section fail_optionAT.
  Context {M : Type → Type} `{M_monad : Monad M}.

  Definition fail_optionAT {A} : optionAT M A := returnM NoneA.

  Lemma fail_optionAT_left : ∀ (A B : Type) (m : A → optionAT M B), 
    bind_optionAT (A:=A) (B:=B) fail_optionAT m = fail_optionAT (A:=B).
  Proof. 
    unfold bind_optionAT, fail_optionAT; simpl. intros. 
    autorewrite with monads. reflexivity.
  Qed.

  Global Instance monad_fail_optionAT : MonadFail (optionAT M) :=
  {
     fail := @fail_optionAT;
     fail_left := @fail_optionAT_left;
  }.
End fail_optionAT.

Section except_optionAT.
  Context {M : Type -> Type} {MM : Monad M}.
  Context {MJ : MonadJoin M}.

  Definition catch_optionAT {A} {JA : Joinable A A}
    (mx my : optionAT M A) : optionAT M A :=
    bindM (M:=M) mx (fun x : optionA A =>
      match x with
      | SomeA a => returnM (SomeA a)
      | SomeOrNoneA a => 
          returnM (SomeOrNoneA a) <⊔> my 
      | NoneA => my
      end).

  Lemma catch_optionAT_throw_left : ∀ A {JA : Joinable A A} 
    (x : optionAT M A),
    catch_optionAT fail_optionAT x = x.
  Proof. 
    intros. unfold catch_optionAT, fail_optionAT. autorewrite with monads.
    reflexivity.
  Qed.

  Lemma catch_optionAT_throw_right : ∀ A {JA : Joinable A A}
  (x : optionAT M A),
    catch_optionAT x fail_optionAT = x.
  Proof. 
    intros. unfold catch_optionAT, fail_optionAT. rewrite <- (bind_id_right (M:=M)).
    f_equal; extensionality m. destruct m; try reflexivity.
    rewrite mjoin_return. reflexivity.
  Qed.

  Lemma catch_optionAT_return : ∀ A {JA : Joinable A A} (x : optionAT M A) (a : A),
    catch_optionAT (returnM a) x = returnM a.
  Proof.
    unfold catch_optionAT. intros. unfold returnM; simpl.
    rewrite bind_id_left. reflexivity.
  Qed.

  Global Instance except_optionAT : MonadExcept (optionAT M) :=
    {
      throw_left := @fail_optionAT_left M _;
      catch_left := catch_optionAT_throw_left;
      catch_right := catch_optionAT_throw_right;
      catch_return := catch_optionAT_return;
    }. 
End except_optionAT.
Hint Resolve except_optionAT : soundness.

Section fail_stateT.
  Context {M : Type -> Type} `{M_fail : MonadFail M}.
  Context {S : Type}.

  Definition fail_stateT {A} : StateT S M A := lift_stateT fail.

  Lemma fail_stateT_left : ∀ (A B : Type) (s : A → StateT S M B),
    fail_stateT (A:=A) >>= s = fail_stateT.
  Proof.
    intros. unfold fail_stateT, lift_stateT. ext. 
    autorewrite with monads. 
    unfold bindM; simpl; unfold bind_stateT. 
    autorewrite with monads. reflexivity.
  Qed.

  Global Instance monad_fail_stateT : MonadFail (StateT S M) :=
  {
    fail := @fail_stateT;
    fail_left := fail_stateT_left;
  }.
End fail_stateT.

Section except_stateT.
  Context {M : Type → Type} {MM : Monad M} {ME : MonadExcept M}.
  Context {S : Type} {JS : Joinable S S}.

  Definition throw_stateT {A} : StateT S M A := lift_stateT throw.

  Lemma throw_stateT_left : ∀ (A B : Type) (f : A → StateT S M B),
    throw_stateT >>= f = throw_stateT.
  Proof.
    intros. unfold throw_stateT. unfold lift_stateT. ext. autorewrite with
      monads. unfold bindM; simpl. unfold bind_stateT. autorewrite with monads.
    reflexivity.
  Qed.

  Definition catch_stateT {A} {JA : Joinable A A} (a b : StateT S M A) : 
      StateT S M A := 
    fun s => catch (a s) (b s).
  Hint Unfold throw_stateT catch_stateT lift_stateT : monads.

  Lemma catch_stateT_throw_left : ∀ A {JA : Joinable A A} (x : StateT S M A),
    catch_stateT throw_stateT x = x.
  Proof. 
    intros. autounfold with monads. ext. autorewrite with monads. reflexivity.
  Qed.

  Lemma catch_stateT_throw_right : ∀ A {JA : Joinable A A} (x : StateT S M A),
    catch_stateT x throw_stateT = x.
  Proof. 
    intros. autounfold with monads.
    ext. autorewrite with monads. reflexivity.
  Qed.

  Lemma catch_stateT_return : ∀ A {JA : Joinable A A} (x : StateT S M A) (a : A),
    catch_stateT (returnM a) x = returnM a.
  Proof.
    intros. ext. autounfold with monads. unfold returnM; simpl. 
    unfold return_stateT. autorewrite with monads. reflexivity.
  Qed.

  Instance except_stateT : MonadExcept (StateT S M) :=
  {
    throw_left := throw_stateT_left;
    catch_left := catch_stateT_throw_left;
    catch_right := catch_stateT_throw_right;
    catch_return := catch_stateT_return;
  }. 
End except_stateT.
Hint Resolve except_stateT : soundness.
