Require Import Classes.Monad.MonadExcept.
Require Import Classes.Monad.MonadFail.
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
    throw_left := none_left;
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

Section fail_optionT.
  Context M `{MM : Monad M}.

  Definition fail_optionT {A} : optionT M A := returnM None.

  Lemma fail_optionT_left : ∀ (A B : Type) (m : A → optionT M B),
    fail_optionT >>= m = fail_optionT.
  Proof.
    intros A B m. unfold fail_optionT. 
    unfold bindM; simpl. unfold bind_op_optionT, bind_optionT. 
    rewrite bind_id_left; reflexivity.
  Qed.

  Global Instance monadfail_optionT : MonadFail (optionT M) := {
    fail_left := fail_optionT_left;
  }.
End fail_optionT.

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

Section fail_stateT.
  Context {M : Type -> Type} `{MM : Monad M} {MF : MonadFail M}.
  Context {S : Type}.

  Definition fail_stateT {A} : StateT S M A := 
    λ st, fail >>= λ a, returnM (a, st). 

  Lemma fail_stateT_left : ∀ (A B : Type) (f : A → StateT S M B),
    fail_stateT (A:=A) >>= f = fail_stateT.
  Proof.
    intros; unfold fail_stateT; extensionality s.
    rewrite fail_left. 
    unfold bindM at 1; simpl; unfold bind_op_stateT, bind_stateT. 
    repeat rewrite fail_left; reflexivity.
  Qed.

  Global Instance monad_fail_stateT : MonadFail (StateT S M) :=
  {
    fail := @fail_stateT;
    fail_left := fail_stateT_left;
  }.
End fail_stateT.

Instance monadfail_stateT_sound {M M'} 
  `{MM : Monad M} `{MM' : Monad M'}
  {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')}
  {S S'} {GS : Galois S S'}
  {MF : MonadFail M} {MF' : MonadFail M'} : 
    MonadFail_sound M M' →
    MonadFail_sound (StateT S M) (StateT S' M').
Proof.
  intros MS A A' GA m'. unfold fail; simpl.
  unfold fail_stateT. intros st st' Hst.
  rewrite fail_left. apply fail_sound.
Qed.
Hint Resolve monadfail_stateT_sound : soundness.

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

Section fail_optionAT.
  Context {S : Type} {JS : Joinable S S} {JI : JoinableIdem JS}.

  Definition fail_optionAT {A} : optionAT (StateT S option) A := 
    fail >>= λ a, returnM (SomeA a).

  Lemma fail_optionAT_left : ∀ (A B : Type) (f : A → optionAT (StateT S option) B),
    fail_optionAT >>= f = fail_optionAT.
  Proof.
    intros A B f. unfold fail_optionAT. repeat rewrite fail_left.
    easy.
  Qed.

  Global Instance monadfail_optionAT : MonadFail (optionAT (StateT S option)) :=
  {
    fail_left := fail_optionAT_left;
  }.
End fail_optionAT.

Instance monadfail_optionAT_sound {S S'} {JS : Joinable S S} {JI : JoinableIdem
  JS} {GS : Galois S S'} :
    MonadFail_sound (optionAT (StateT S option)) (optionT (StateT S' option)).
Proof.
  intros A A' GA m'. 
  unfold fail; simpl; unfold fail_optionAT. 
  rewrite fail_left. 
  unfold fail; simpl; unfold fail_stateT.
  intros s s' Hs. 
  rewrite fail_left.
  constructor.
Qed.
Hint Resolve monadfail_optionAT_sound : soundness.

Section except_optionAT.
  Context {S : Type} {JS : Joinable S S} {JI : JoinableIdem JS}.

  Definition throw_optionAT {A} : optionAT (StateT S option) A := 
    returnM NoneA.

  Lemma throw_optionAT_left : ∀ (A B : Type) 
    (m : A → optionAT (StateT S option) B), 
    bind_optionAT_stateT (A:=A) (B:=B) throw_optionAT m = throw_optionAT (A:=B).
  Proof. 
    intros; unfold bind_optionAT_stateT, throw_optionAT; extensionality s. 
    reflexivity.
  Qed.

  Definition catch_optionAT {A} {JA : Joinable A A} {JAI : JoinableIdem JA}
    (mx my : optionAT (StateT S option) A) : optionAT (StateT S option) A :=
    bindM (M:=(StateT S option)) mx (fun x : optionA A =>
      match x with
      | SomeA a => returnM (SomeA a)
      | SomeOrNoneA a => 
          returnM (SomeOrNoneA a) <⊔> my 
      | NoneA => my
      end).

  Lemma catch_optionAT_throw_left :
      ∀ A {JA : Joinable A A} {JAI : JoinableIdem JA} 
      (x : optionAT (StateT S option) A),
    catch_optionAT throw_optionAT x = x.
  Proof. 
    intros; unfold catch_optionAT, throw_optionAT. 
    rewrite bind_id_left; reflexivity.
  Qed.

  Lemma catch_optionAT_throw_right :
    ∀ A {JA : Joinable A A} {JAI : JoinableIdem JA} (m : optionAT (StateT S option) A),
    catch_optionAT m throw_optionAT = m.
  Proof. 
    intros; unfold catch_optionAT, throw_optionAT. 
    rewrite <- (bind_id_right (M:=(StateT S option))). 
    f_equal; extensionality x.
    destruct x; try reflexivity.
    unfold "<⊔>"; simpl; unfold mjoin_stateT. extensionality s.
    unfold "<⊔>"; simpl; cbn. 
    unfold "⊔", pair_joinable; simpl. 
    rewrite JI; reflexivity.
  Qed.

  Lemma catch_optionAT_return :
    ∀ A {JA : Joinable A A} {JAI : JoinableIdem JA} 
    (m : optionAT (StateT S option) A) (a : A),
    catch_optionAT (return_optionAT_stateT a) m = return_optionAT_stateT a.
  Proof.
    intros; unfold catch_optionAT, return_optionAT_stateT; extensionality s.
    unfold bindM; simpl. reflexivity.
  Qed.

  Global Instance except_optionAT : MonadExcept (optionAT (StateT S option)) :=
    {
      throw_left := throw_optionAT_left;
      catch_left := catch_optionAT_throw_left;
      catch_right := catch_optionAT_throw_right;
      catch_return := catch_optionAT_return;
    }. 
End except_optionAT.

Instance throw_optionAT_sound {S S' : Type} {GS : Galois S S'} 
  {JS : Joinable S S} {JI : JoinableIdem JS} : 
  throw_op_sound (optionAT (StateT S option)) (optionT (StateT S' option)).
Proof.
  intros A A' GA; unfold throw; simpl; unfold throw_optionAT, return_stateT.
  intros s s' Hs. 
  apply returnM_sound.
  constructor; simpl; constructor + assumption.
Qed.

Instance catch_optionAT_sound {S S' : Type} {GS : Galois S S'} 
  {JS : Joinable S S} {JSS : JoinableSound JS} {JI : JoinableIdem JS} :
  catch_op_sound (optionAT (StateT S option)) (optionT (StateT S' option)).
Proof.
  intros A JA JAI A' JA' JAI' GA JAS p1 p2 p1' p2' Hp1 Hp2.
  unfold catch; simpl. unfold catch_optionAT, catch_optionT.
  unfold bindM; simpl; unfold bind_op_stateT, bind_stateT.
  intros s s' Hs.
  unfold bindM; simpl; unfold bind_op_option, bind_option.
  apply Hp1 in Hs.
  destruct (p1 s), (p1' s').
  - destruct p, p0. destruct o, o0.
    + apply Hs.
    + inversion Hs; subst.
      inversion H1; subst; simpl in *.
      inversion H.
    + inversion Hs; subst.
      inversion H1; subst; simpl in *.
      inversion H.
    + inversion Hs; subst.
      inversion H1; subst; simpl in *.
      apply Hp2 in H0. assumption.
    + unfold mjoin_stateT. unfold returnM; simpl.
      inversion Hs; subst.
      inversion H1; subst; simpl in *.
      apply Hp2 in H0.
      destruct (p2 s0).
      * constructor. destruct p; simpl. unfold "⊔", pair_joinable; simpl.
        destruct o.
        -- constructor; simpl; apply join_sound.
          ++ left. assumption.
          ++ left. inversion H1; simpl in *. assumption.
        -- constructor; simpl in *; apply join_sound.
          ++ left. assumption.
          ++ left. inversion H1; simpl in *; subst. assumption.
        -- constructor; simpl in *; apply join_sound.
          ++ left. assumption.
          ++ left. inversion H1; subst; simpl in *. assumption.
      * constructor.
    + unfold mjoin_stateT. unfold returnM; simpl.
      inversion Hs; subst; clear Hs.
      inversion H1; subst; simpl in *; clear H1.
      apply Hp2 in H0. destruct (p2 s0), (p2' s1).
      * constructor. destruct p, p0. apply join_sound. right.
        inversion H0; subst. assumption.
      * inversion H0.
      * constructor.
      * constructor.
  - inversion Hs.
  - constructor.
  - constructor.
Qed.
Hint Resolve catch_optionAT_sound throw_optionAT_sound : soundness.
Hint Resolve except_optionAT : soundness.

