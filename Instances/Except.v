Require Import Classes.Monad.MonadExcept.
Require Import Classes.Monad.MonadFail.
Require Import Classes.Monad.MonadJoin.
Require Import Classes.Joinable.
Require Import Classes.Galois.
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

Instance fail_option_sound : MonadFail_sound option option.
Proof.
  intros A A' GA m'. constructor.
Qed.
Hint Resolve fail_option_sound : soundness.

Section except_option.
  Definition catch_option {A} {JA : Joinable A A} {JAI : JoinableIdem JA}
    (x y : option A) : option A :=
    match x with
    | None => y
    | _ => x
    end.
  Hint Unfold catch_option : monads.

  Lemma catch_option_throw_left : ∀ (A : Type) (JA : Joinable A A) 
    {JAI : JoinableIdem JA} (x : option A),
    catch_option None x = x.
  Proof. simple_solve. Qed.

  Lemma catch_option_throw_right : ∀ A (JA : Joinable A A) 
    {JAI : JoinableIdem JA} (x : option A),
    catch_option x None = x.
  Proof. simple_solve. Qed.

  Lemma catch_option_return : ∀ A (JA : Joinable A A) 
    {JAI : JoinableIdem JA} (x : option A) (a : A),
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

  Global Instance throw_option_sound : throw_op_sound option option.
  Proof.
    intro. intros. constructor.
  Qed.
End except_option.

Section except_optionA.
  Definition throw_optionA {A} := @NoneA A.

  Lemma throw_optionA_left A B : ∀ (f : A → optionA B),
    throw_optionA >>= f = throw_optionA.
  Proof.
    intros f. constructor.
  Qed.
  
  Definition catch_optionA {A : Type} {JA : Joinable A A} 
    {JAI : JoinableIdem JA} (x y : optionA A) : optionA A :=
    match x with
    | NoneA => y
    | SomeA a => x
    | SomeOrNoneA a => x ⊔ y
    end.

  Lemma catch_optionA_throw_left : ∀ A {JA : Joinable A A} 
    {JAI : JoinableIdem JA} (x : optionA A),
    catch_optionA NoneA x = x.
  Proof. reflexivity. Qed.

  Lemma catch_optionA_throw_right : ∀ A {JA : Joinable A A}
  {JAI : JoinableIdem JA} (x : optionA A),
    catch_optionA x NoneA = x.
  Proof.
    intros. destruct x; simpl; reflexivity. 
  Qed.

  Lemma catch_optionA_return : ∀ A {JA : Joinable A A}
  {JAI : JoinableIdem JA} (x : optionA A) (a : A),
    catch_optionA (returnM a) x = returnM a.
  Proof.
    reflexivity. 
  Qed.

  Global Instance except_optionA : MonadExcept optionA :=
  {
    throw_left := throw_optionA_left;
    catch_left := catch_optionA_throw_left;
    catch_right := catch_optionA_throw_right;
    catch_return := catch_optionA_return;
  }.

  Global Instance catch_optionA_sound : catch_op_sound optionA option.
  Proof.
    intros A JA JAI A' JA' JAI' GA JAS p1 p2 p1' p2' Hp1 Hp2. destruct p1, p1'; cbv. 
    - constructor. inversion Hp1; subst. assumption.
    - inversion Hp1.
    - inversion Hp1.
    - assumption.
    - destruct p2; constructor; try apply JAS; inversion Hp1; subst.
      + left. assumption.
      + assumption.
      + left. assumption.
    - destruct p2, p2'; constructor; try apply JAS; inversion Hp2; subst.
      + right; assumption.
      + right; assumption.
  Qed.

  Global Instance throw_optionA_sound : throw_op_sound optionA option.
  Proof. constructor. Qed.
End except_optionA.

Section fail_optionT.
  Context M {MM : Monad M} {MF : MonadFail M}.

  Definition fail_optionT {A} : optionT M A := liftT fail.

  Lemma fail_optionT_left : ∀ (A B : Type) (m : A → optionT M B),
    fail_optionT >>= m = fail_optionT.
  Proof.
    intros A B m. unfold fail_optionT. unfold liftT; simpl.
    unfold lift_optionT; simpl. repeat rewrite fail_left.
    unfold bindM; simpl. unfold bind_optionT. rewrite fail_left.
    reflexivity.
  Qed.

  Global Instance monadfail_optionT : MonadFail (optionT M) := {
    fail_left := fail_optionT_left;
  }.
End fail_optionT.

Instance fail_optionT_sound {M M'} {MM : Monad M} {MM' : Monad M'}
  {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')}
  {MF : MonadFail M} {MF' : MonadFail M'} : 
  MonadFail_sound M M' → 
  MonadFail_sound (optionT M) (optionT M').
Proof.
  intros MS A A' GA m'. unfold fail; simpl. unfold fail_optionT. 
  unfold liftT; simpl. unfold lift_optionT. rewrite fail_left.
  unfold γ. apply fail_sound.
Qed.
Hint Resolve fail_optionT_sound : soundness.

Section except_optionT.
  Context M {MM : Monad M}.

  Definition throw_optionT {A} : optionT M A := returnM None.

  Lemma throw_optionT_left : ∀ (A B : Type) (m : A → optionT M B), 
    throw_optionT >>= m = throw_optionT.
  Proof.
    intros. unfold bind_optionT, throw_optionT. unfold bindM; simpl. 
    unfold bind_optionT.
    autorewrite with monads.
    reflexivity.
  Qed.

  Definition catch_optionT {A} {JA : Joinable A A}
  {JAI : JoinableIdem JA} (mx my : optionT M A) : 
    optionT M A :=
    bindM (M:=M) mx (fun x : option A =>
      match x with
      | None => my
      | Some a => returnM (Some a)
      end).
  Hint Unfold catch_optionT : monads.

  Lemma catch_optionT_throw_left : ∀ (A : Type) {JA : Joinable A A} 
  {JAI : JoinableIdem JA} (x : optionT M A), 
    catch_optionT throw_optionT x = x.
  Proof.
    intros. unfold catch_optionT, throw_optionT.
    autorewrite with monads. reflexivity.
  Qed.

  Lemma catch_optionT_throw_right : ∀ (A : Type) {JA : Joinable A A} 
  {JAI : JoinableIdem JA} (x : optionT M A), 
    catch_optionT x throw_optionT = x.
  Proof.
    unfold catch_optionT, throw_optionT. intros.
    replace x with (bindM (M:=M) x returnM) at 2.
    f_equal; ext; destruct x0; reflexivity.
    rewrite <- (bind_id_right (M:=M)). f_equal.
  Qed.

  Lemma catch_optionT_return : ∀ (A : Type) {JA : Joinable A A} 
  {JAI : JoinableIdem JA} (x : optionT M A) (a : A),
    catch_optionT (returnM a) x = returnM a.
  Proof.
    unfold catch_optionT. intros. unfold returnM; simpl.
    rewrite bind_id_left. reflexivity.
  Qed.

  Global Instance except_optionT : MonadExcept (optionT M) :=
  {
    throw_left := throw_optionT_left;
    catch_left := catch_optionT_throw_left;
    catch_right := catch_optionT_throw_right;
    catch_return := catch_optionT_return;
  }. 
End except_optionT.
Hint Resolve except_optionT : soundness.

Section fail_optionAT.
  Context M {MM : Monad M} {MF : MonadFail M}.
  
  Definition fail_optionAT {A} : optionAT M A := liftT fail.

  Lemma fail_optionAT_left : ∀ (A B : Type) (f : A → optionAT M B),
    fail_optionAT >>= f = fail_optionAT.
  Proof.
    intros A B f. unfold fail_optionAT, bindM; simpl. unfold bind_optionAT,
    lift_optionAT. repeat rewrite fail_left. reflexivity.
  Qed.

  Global Instance monadfail_optionAT : MonadFail (optionAT M) :=
  {
    fail_left := fail_optionAT_left;
  }.
End fail_optionAT.

Instance monadfail_optionAT_sound {M M'} {MM : Monad M} {MM' : Monad M'}
  {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')}
  {MF : MonadFail M} {MF' : MonadFail M'} : 
    MonadFail_sound M M' →
    MonadFail_sound (optionAT M) (optionT M').
Proof.
  intros MS A A' GA m'. unfold fail; simpl. unfold fail_optionAT. simpl.
  unfold lift_optionAT. rewrite fail_left. unfold γ. apply fail_sound.
Qed.
Hint Resolve monadfail_optionAT_sound : soundness.

Section except_optionAT.
  Definition throw_optionAT {M} {MM : Monad M} 
    {MJ : MonadJoin M} {A} : optionAT M A := returnM NoneA.

  Lemma throw_optionAT_left {M} {MM : Monad M}
    {MJ : MonadJoin M} : ∀ (A B : Type) (m : A → optionAT M B), 
    bind_optionAT (A:=A) (B:=B) throw_optionAT m = throw_optionAT (A:=B).
  Proof. 
    unfold bind_optionAT, throw_optionAT; simpl. intros. 
    autorewrite with monads. reflexivity.
  Qed.

  Definition catch_optionAT {M} {MM : Monad M}
    {MJ : MonadJoin M} {A} {JA : Joinable A A} {JAI : JoinableIdem JA}
    (mx my : optionAT M A) : optionAT M A :=
    bindM (M:=M) mx (fun x : optionA A =>
      match x with
      | SomeA a => returnM (SomeA a)
      | SomeOrNoneA a => 
          returnM (SomeOrNoneA a) <⊔> my 
      | NoneA => my
      end).

  Lemma catch_optionAT_throw_left {M} {MM : Monad M} {MJ : MonadJoin M} : 
      ∀ A {JA : Joinable A A} {JAI : JoinableIdem JA} (x : optionAT M A),
    catch_optionAT throw_optionAT x = x.
  Proof. 
    intros. unfold catch_optionAT, throw_optionAT. autorewrite with monads.
    reflexivity.
  Qed.

  Lemma catch_optionAT_throw_right {M} {MM : Monad M} {MJ : MonadJoin M}: 
    ∀ A {JA : Joinable A A} {JAI : JoinableIdem JA} (x : optionAT M A),
    catch_optionAT x throw_optionAT = x.
  Proof. 
    intros. unfold catch_optionAT, throw_optionAT. rewrite <- (bind_id_right (M:=M)).
    f_equal; extensionality m. destruct m; try reflexivity.
    rewrite mjoin_return. reflexivity.
  Qed.

  Lemma catch_optionAT_return {M} {MM : Monad M} {MJ : MonadJoin M} : 
    ∀ A {JA : Joinable A A} {JAI : JoinableIdem JA} (x : optionAT M A) (a : A),
    catch_optionAT (returnM a) x = returnM a.
  Proof.
    unfold catch_optionAT. intros. unfold returnM; simpl.
    rewrite bind_id_left. reflexivity.
  Qed.

  Global Instance except_optionAT {M} {MM : Monad M} : 
    MonadJoin M → MonadExcept (optionAT M) :=
    {
      throw_left := throw_optionAT_left;
      catch_left := catch_optionAT_throw_left;
      catch_right := catch_optionAT_throw_right;
      catch_return := catch_optionAT_return;
    }. 

  Global Instance throw_optionAT_sound {M M'} {MM : Monad M} {MM' : Monad M'}
    {MJ : MonadJoin M}
    {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')} :
    return_sound M M' → 
    throw_op_sound (optionAT M) (optionT M').
  Proof.
    intros RS A A' GA. unfold throw; simpl. 
    unfold throw_optionT, throw_optionAT. apply RS. constructor.
  Qed.

  Global Instance catch_optionAT_sound {M M'} {MM : Monad M} {MM' : Monad M'}
    {MJ : MonadJoin M} 
    {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')} :
    return_sound M M' →
    bind_sound M M' →
    MonadJoinSound M M' →
    catch_op_sound (optionAT M) (optionT M').
  Proof.
    intros RS BS MS A JA JAI A' JA' JAI' GA JAS p1 p2 p1' p2' Hp1 Hp2.
    unfold catch; simpl. unfold catch_optionAT, catch_optionT.
    eapply BS. apply Hp1. intros ???. destruct a, a'.
    - apply RS; assumption.
    - inversion H.
    - inversion H.
    - assumption.
    - apply mjoin_sound_left. apply RS. assumption.
    - apply mjoin_sound_right. assumption.
  Qed.
End except_optionAT.
Hint Resolve catch_optionAT_sound throw_optionAT_sound : soundness.
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

Instance monadfail_stateT_sound {M M'} {MM : Monad M} {MM' : Monad M'}
  {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')}
  {S S'} {GS : Galois S S'}
  {MF : MonadFail M} {MF' : MonadFail M'} : 
    MonadFail_sound M M' →
    MonadFail_sound (StateT S M) (StateT S' M').
Proof.
  intros MS A A' GA m'. unfold fail; simpl.
  unfold fail_stateT. unfold lift_stateT. intros st st' Hst.
  rewrite fail_left. apply fail_sound.
Qed.
Hint Resolve monadfail_stateT_sound : soundness.

Section except_stateT.
  Context {M : Type → Type} {MM : Monad M} {ME : MonadExcept M}.
  Context {S : Type} {JS : Joinable S S} {JSI : JoinableIdem JS}.

  Definition throw_stateT {A} : StateT S M A := lift_stateT throw.

  Lemma throw_stateT_left : ∀ (A B : Type) (f : A → StateT S M B),
    throw_stateT >>= f = throw_stateT.
  Proof.
    intros. unfold throw_stateT. unfold lift_stateT. ext. autorewrite with
      monads. unfold bindM; simpl. unfold bind_stateT. autorewrite with monads.
    reflexivity.
  Qed.

  Definition catch_stateT {A} {JA : Joinable A A} {JAI : JoinableIdem JA} 
    (a b : StateT S M A) : 
      StateT S M A := 
    fun s => catch (a s) (b s).
  Hint Unfold throw_stateT catch_stateT lift_stateT : monads.

  Lemma catch_stateT_throw_left : ∀ A {JA : Joinable A A} 
    {JAI : JoinableIdem JA} (x : StateT S M A),
    catch_stateT throw_stateT x = x.
  Proof. 
    intros. autounfold with monads. ext. autorewrite with monads. reflexivity.
  Qed.

  Lemma catch_stateT_throw_right : ∀ A {JA : Joinable A A}
  {JAI : JoinableIdem JA} (x : StateT S M A),
    catch_stateT x throw_stateT = x.
  Proof. 
    intros. autounfold with monads.
    ext. autorewrite with monads. reflexivity.
  Qed.

  Lemma catch_stateT_return : ∀ A {JA : Joinable A A}
  {JAI : JoinableIdem JA} (x : StateT S M A) (a : A),
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
