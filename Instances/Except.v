Require Import Classes.Applicative.
Require Import Classes.Except.
Require Import Classes.Joinable.
Require Import Classes.Monad.
Require Import Classes.PreorderedSet.
Require Import Instances.Joinable.
Require Import Instances.Monad.
Require Import Types.Result.
Require Import Types.State.
Require Import Types.Stores.

Implicit Type A : Type.
Implicit Type M : Type → Type.

Section except_maybe.
  Definition trycatch_maybe {A} (x y : Maybe A) : Maybe A :=
    match x with
    | None => y
    | _ => x
    end.
  Hint Unfold trycatch_maybe : soundness.

  Lemma trycatch_maybe_throw_left : ∀ A (x : Maybe A),
    trycatch_maybe None x = x.
  Proof. simple_solve. Qed.

  Lemma trycatch_maybe_throw_right : ∀ A (x : Maybe A),
    trycatch_maybe x None = x.
  Proof. simple_solve. Qed.

  Instance except_maybe : Except Maybe :=
  {
    throw := @None;
    trycatch := @trycatch_maybe;
    trycatch_throw_left := trycatch_maybe_throw_left;
    trycatch_throw_right := trycatch_maybe_throw_right;
  }.
End except_maybe.

Section except_maybeT.
  Context {M} {inst : Monad M}.

  Definition throw_maybeT {A} : MaybeT M A :=
    pure (F:=M) (@None A).
  Hint Unfold throw_maybeT : soundness.

  Definition trycatch_maybeT {A} (mx my : MaybeT M A) : MaybeT M A :=
    @bindM M _ _ _ mx (fun x : Maybe A =>
      match x with
      | None => my
      | Just a => pure (Just a)
      end).
  Hint Unfold trycatch_maybeT : soundness.
  Arguments trycatch_maybeT [_].

  Lemma trycatch_maybeT_throw_left : ∀ (A : Type) (x : MaybeT M A), 
    trycatch_maybeT throw_maybeT x = x.
  Proof.
    autounfold with soundness. intros.
    autorewrite with soundness. reflexivity.
  Qed.

  Lemma trycatch_maybeT_throw_right : ∀ (A : Type) (x : MaybeT M A), 
    trycatch_maybeT x throw_maybeT = x.
  Proof.
    autounfold with soundness. intros.
    replace x with (bindM (M:=M) x pure) at 2.
    f_equal; ext; destruct x0; reflexivity.
    rewrite <- (bind_id_right (M:=M)). f_equal.
  Qed.

  Instance except_maybeT : Except (MaybeT M) :=
  {
    throw := @throw_maybeT;
    trycatch := trycatch_maybeT;
    trycatch_throw_left := @trycatch_maybeT_throw_left;
    trycatch_throw_right := @trycatch_maybeT_throw_right;
  }. 

End except_maybeT.
Section except_maybeAT.
  Context {M : Type -> Type} `{inst : Monad M}.

  Definition throw_maybeAT {A : Type} : MaybeAT M A := pure (@NoneA A).

  Definition trycatch_maybeAT {A}
    (mx my : MaybeAT M A) : MaybeAT M A :=
    @bindM _ inst _ _ mx (fun x : AbstractMaybe A =>
      match x with
      | JustA a => pure (JustA a)
      | JustOrNoneA a => pure (JustOrNoneA a) (* should be a join_op *)
      | NoneA => my
      end).
  Arguments trycatch_maybeAT [_].
  Hint Unfold throw_maybeAT trycatch_maybeAT : soundness.

  Lemma trycatch_maybeAT_throw_left : ∀ A (x : MaybeAT M A),
    trycatch_maybeAT throw_maybeAT x = x.
  Proof. simple_solve. Qed.
  
  Lemma trycatch_maybeAT_throw_right : ∀ A (x : MaybeAT M A),
    trycatch_maybeAT x throw_maybeAT = x.
  Proof. 
    intros. unfold trycatch_maybeAT. rewrite <- (@bind_id_right M inst).
    f_equal; ext. destruct x0; reflexivity.
  Qed.

  Instance except_maybeAT : Except (MaybeAT M) :=
    {
      throw := @throw_maybeAT;
      trycatch := trycatch_maybeAT;
      trycatch_throw_left := trycatch_maybeAT_throw_left;
      trycatch_throw_right := trycatch_maybeAT_throw_right;
    }. 
End except_maybeAT.

Section except_stateT.
  Context {M : Type -> Type} `{inst_m : Monad M} 
    `{inst_e : @Except M inst_m}.
  Context {S : Type}.

  Definition throw_stateT {A} : StateT S M A := fun _ => throw.

  Definition trycatch_stateT {A} (a b : StateT S M A) : StateT S M A := 
    fun s => trycatch (a s) (b s).
  Hint Unfold throw_stateT trycatch_stateT : soundness.

  Lemma trycatch_stateT_throw_left : ∀ A (x : StateT S M A),
    trycatch_stateT throw_stateT x = x.
  Proof. simple_solve. Qed.

  Lemma trycatch_stateT_throw_right : ∀ A (x : StateT S M A),
    trycatch_stateT x throw_stateT = x.
  Proof. simple_solve. Qed.

  Instance except_stateT : Except (StateT S M) :=
  {
    throw := @throw_stateT;
    trycatch := @trycatch_stateT;
    trycatch_throw_left := trycatch_stateT_throw_left;
    trycatch_throw_right := trycatch_stateT_throw_right;
  }. 
End except_stateT.

Global Instance except_abstract_state : Except AbstractState.
Proof. apply except_maybeAT. Defined.

Require Import Classes.Except.
Instance except_conc : Except ConcreteState. 
Proof. apply except_maybeT. Defined.
