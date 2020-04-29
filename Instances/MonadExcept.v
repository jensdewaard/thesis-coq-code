Require Import Classes.Monad.MonadExcept.
Require Import Classes.Monad.MonadJoin.
Require Import Classes.Joinable.
Require Import Classes.Galois.
Require Import Classes.Monad.
Require Import Classes.PreorderedSet.
Require Import Instances.Joinable.
Require Import Types.Stores.
Require Import Types.State.
Require Import Types.Option.

Implicit Type A : Type.
Implicit Type M : Type → Type.

Section except_option.
  Definition catch_option {A} {JA : Joinable A A} {JAI : JoinableIdem JA}
    (x y : option A) : option A :=
    match x with
    | None => y
    | _ => x
    end.
  Hint Unfold catch_option : monads.

  Lemma throw_option_left : ∀ A B (f : A → option B),
    None >>= f = None.
  Proof. easy. Qed.

  Lemma catch_option_throw_left : ∀ (A : Type) (JA : Joinable A A) 
    {JAI : JoinableIdem JA} (x : option A),
    catch_option None x = x.
  Proof. easy. Qed.

  Lemma catch_option_throw_right : ∀ A (JA : Joinable A A) 
    {JAI : JoinableIdem JA} (x : option A),
    catch_option x None = x.
  Proof. 
    intros; unfold catch_option. 
    destruct x; reflexivity.
  Qed.

  Lemma catch_option_return : ∀ A (JA : Joinable A A) 
    {JAI : JoinableIdem JA} (x : option A) (a : A),
    catch_option (returnM a) x = returnM a.
  Proof. easy. Qed.

  Global Instance except_option : MonadExcept option :=
  {
    throw_left := throw_option_left;
    catch_left := catch_option_throw_left;
    catch_right := catch_option_throw_right;
    catch_return := catch_option_return;
  }.

  Global Instance throw_option_sound : throw_op_sound option option.
  Proof. constructor. Qed.
End except_option.

Section except_optionA.
  Definition throw_optionA {A} := @NoneA A.

  Lemma throw_optionA_left A B : ∀ (f : A → optionA B),
    throw_optionA >>= f = throw_optionA.
  Proof. constructor. Qed.
  
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
  Proof. easy. Qed.

  Lemma catch_optionA_throw_right : ∀ A {JA : Joinable A A}
  {JAI : JoinableIdem JA} (x : optionA A),
    catch_optionA x NoneA = x.
  Proof.
    intros; unfold catch_optionA.
    destruct x; easy.
  Qed.

  Lemma catch_optionA_return : ∀ A {JA : Joinable A A}
  {JAI : JoinableIdem JA} (x : optionA A) (a : A),
    catch_optionA (returnM a) x = returnM a.
  Proof. easy. Qed.

  Global Instance except_optionA : MonadExcept optionA :=
  {
    throw_left := throw_optionA_left;
    catch_left := catch_optionA_throw_left;
    catch_right := catch_optionA_throw_right;
    catch_return := catch_optionA_return;
  }.

  Global Instance catch_optionA_sound : catch_op_sound optionA option.
  Proof.
    intros A JA JAI A' JA' JAI' GA JAS p1 p2 p1' p2' Hp1 Hp2. 
    unfold catch; simpl; unfold catch_optionA, catch_option.
    destruct p1, p1'; simpl.
    - constructor; inversion Hp1; subst; assumption.
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

Section except_optionT.
  Context M `{MM : Monad M}.

  Definition throw_optionT {A} : optionT M A := returnM None.

  Lemma throw_optionT_left : ∀ (A B : Type) (m : A → optionT M B), 
    throw_optionT >>= m = throw_optionT.
  Proof.
    intros; unfold throw_optionT. 
    unfold bindM; simpl; unfold bind_op_optionT, bind_optionT.
    rewrite bind_id_left; reflexivity.
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
    intros; unfold catch_optionT, throw_optionT.
    rewrite bind_id_left; reflexivity.
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
    catch_optionT (return_optionT a) x = return_optionT a.
  Proof.
    intros. unfold catch_optionT, return_optionT.
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

Section except_stateT.
  Context {M : Type → Type} `{MM : Monad M} {ME : MonadExcept M}.
  Context {S : Type} {JS : Joinable S S} {JSI : JoinableIdem JS}.

  Definition throw_stateT {A} : StateT S M A := 
    λ st, throw >>= λ a, returnM (a, st).

  Lemma throw_stateT_left : ∀ (A B : Type) (f : A → StateT S M B),
    throw_stateT >>= f = throw_stateT.
  Proof.
    intros; unfold throw_stateT; extensionality s.
    unfold bindM at 1; simpl; unfold bind_op_stateT, bind_stateT. 
    repeat rewrite throw_left; reflexivity.
  Qed.

  Definition catch_stateT {A} {JA : Joinable A A} {JAI : JoinableIdem JA} 
    (a b : StateT S M A) : 
      StateT S M A := 
    fun s => catch (a s) (b s).
  Hint Unfold throw_stateT catch_stateT : monads.

  Lemma catch_stateT_throw_left : ∀ A {JA : Joinable A A} 
    {JAI : JoinableIdem JA} (m : StateT S M A),
    catch_stateT throw_stateT m = m.
  Proof. 
    intros; unfold catch_stateT, throw_stateT; extensionality s.
    rewrite throw_left, catch_left; reflexivity.
  Qed.

  Lemma catch_stateT_throw_right : ∀ A {JA : Joinable A A}
  {JAI : JoinableIdem JA} (m : StateT S M A),
    catch_stateT m throw_stateT = m.
  Proof. 
    intros; unfold catch_stateT, throw_stateT; extensionality s.
    rewrite throw_left, catch_right; reflexivity.
  Qed.

  Lemma catch_stateT_return : ∀ A {JA : Joinable A A}
  {JAI : JoinableIdem JA} (x : StateT S M A) (a : A),
    catch_stateT (return_stateT a) x = return_stateT a.
  Proof.
    intros. unfold catch_stateT, return_stateT; extensionality s.
    rewrite catch_return; reflexivity.
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

Section except_optionAT.
  Context {S : Type} {JS : Joinable S S} {JI : JoinableIdem JS}.
  Context {M : Type → Type} `{MM : Monad M} {MJ : MonadJoin M}.

  Definition throw_optionAT {A} : optionAT (StateT S M) A := 
    returnM NoneA.

  Lemma throw_optionAT_left : ∀ (A B : Type) 
    (m : A → optionAT (StateT S M) B), 
    bind_optionAT_stateT (A:=A) (B:=B) throw_optionAT m = throw_optionAT (A:=B).
  Proof. 
    intros; unfold bind_optionAT_stateT, throw_optionAT; extensionality s. 
    unfold returnM; unfold return_op_stateT, return_stateT.
    rewrite bind_id_left; reflexivity.
  Qed.

  Definition catch_optionAT {A} {JA : Joinable A A} {JAI : JoinableIdem JA}
    (mx my : optionAT (StateT S M) A) : optionAT (StateT S M) A :=
    bindM (M:=(StateT S M)) mx (fun x : optionA A =>
      match x with
      | SomeA a => returnM (SomeA a)
      | SomeOrNoneA a => 
          returnM (SomeOrNoneA a) <⊔> my 
      | NoneA => my
      end).

  Lemma catch_optionAT_throw_left :
      ∀ A {JA : Joinable A A} {JAI : JoinableIdem JA} 
      (x : optionAT (StateT S M) A),
    catch_optionAT throw_optionAT x = x.
  Proof. 
    intros; unfold catch_optionAT, throw_optionAT. 
    rewrite bind_id_left; reflexivity.
  Qed.

  Lemma catch_optionAT_throw_right :
    ∀ A {JA : Joinable A A} {JAI : JoinableIdem JA} 
    (m : optionAT (StateT S M) A),
    catch_optionAT m throw_optionAT = m.
  Proof. 
    intros; unfold catch_optionAT, throw_optionAT. 
    rewrite <- (bind_id_right (M:=(StateT S M))). 
    f_equal; extensionality x.
    destruct x; try reflexivity.
    rewrite mjoin_return; easy.
  Qed.

  Lemma catch_optionAT_return :
    ∀ A {JA : Joinable A A} {JAI : JoinableIdem JA} 
    (m : optionAT (StateT S M) A) (a : A),
    catch_optionAT (return_optionAT_stateT a) m = return_optionAT_stateT a.
  Proof.
    intros; unfold catch_optionAT, return_optionAT_stateT; extensionality s.
    unfold bindM; simpl; unfold bind_op_stateT, bind_stateT. 
    rewrite bind_id_left; reflexivity.
  Qed.

  Global Instance except_optionAT : MonadExcept (optionAT (StateT S M)) :=
    {
      throw_left := throw_optionAT_left;
      catch_left := catch_optionAT_throw_left;
      catch_right := catch_optionAT_throw_right;
      catch_return := catch_optionAT_return;
    }. 
End except_optionAT.

Instance throw_optionAT_sound {S S' : Type} {GS : Galois S S'} 
  {JS : Joinable S S} {JI : JoinableIdem JS} 
  {M M' : Type → Type} `{MM : Monad M} `{MM' : Monad M'} {MJ : MonadJoin M} 
  {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')} : 
  return_sound M M' →
  throw_op_sound (optionAT (StateT S M)) (optionT (StateT S' M')).
Proof.
  intros RS A A' GA; unfold throw; simpl; unfold throw_optionAT, throw_optionT.
  intros s s' Hs. 
  unfold returnM, return_op_stateT, return_stateT.
  apply returnM_sound.
  constructor; simpl; constructor + assumption.
Qed.

Instance catch_optionAT_sound {S S' : Type} {GS : Galois S S'} 
  {JS : Joinable S S} {JSS : JoinableSound JS} {JI : JoinableIdem JS} 
  {M M' : Type → Type} `{MM : Monad M} `{MM' : Monad M'} {MJ : MonadJoin M}
  {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')} 
  {MJS : MonadJoinSound M M'} :
  return_sound M M' →
  bind_sound M M' →
  catch_op_sound (optionAT (StateT S M)) (optionT (StateT S' M')).
Proof.
  intros RS BS A JA JAI A' JA' JAI' GA JAS p1 p2 p1' p2' Hp1 Hp2.
  unfold catch; simpl; unfold catch_optionAT, catch_optionT.
  unfold bindM; simpl; unfold bind_op_stateT, bind_stateT.
  intros s s' Hs.
  apply Hp1 in Hs.
  apply bindM_sound; try assumption.
  intros p3 p3' Hp3.
  destruct p3 as [o3 s3], p3' as [o3' s3']; destruct o3, o3'.
    + apply returnM_sound. assumption.
    + inversion Hp3; subst; simpl in *; inversion H.
    + inversion Hp3; subst; simpl in *; inversion H.
    + inversion Hp3; subst; simpl in *; apply Hp2 in H0; assumption.
    + unfold mjoin_stateT. unfold returnM; simpl; unfold return_op_stateT,
        return_stateT.
      apply mjoin_sound_left, returnM_sound; assumption.
    + unfold mjoin_stateT; apply mjoin_sound_right.
      inversion Hp3; subst; simpl in *. apply Hp2 in H0.
      assumption.
Qed.
Hint Resolve catch_optionAT_sound throw_optionAT_sound : soundness.
Hint Resolve except_optionAT : soundness.

