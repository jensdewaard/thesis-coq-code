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
  Instance except_maybe : Except Maybe :=
  {
    throw := @None;
    trycatch := @trycatch_maybe;
  }. all: solve_monad. Defined.
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
    rewrite <- (bind_id_right (M:=M)). f_equal.
    ext. destruct x0; reflexivity.
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

  Instance except_maybeAT : Except (MaybeAT M) :=
    {
      throw := @throw_maybeAT;
      trycatch := trycatch_maybeAT;
    }. 1,3: solve_monad.
      intros. unfold trycatch_maybeAT. 
      rewrite <- (@bind_id_right M inst). f_equal. simple_solve.
    Defined.
End except_maybeAT.

Section except_stateT.
  Context {M : Type -> Type} `{inst_m : Monad M} 
    `{inst_e : @Except M inst_m}.

  Definition throw_stateT {S} A : StateT S M A := fun _ => throw.

  Definition trycatch_stateT {S A} (a b : StateT S M A) : StateT S M A := 
    fun s => trycatch (a s) (b s).
  Hint Unfold throw_stateT trycatch_stateT : soundness.

  Instance except_stateT (S : Type) : Except (StateT S M) :=
  {
    throw := @throw_stateT S;
    trycatch := @trycatch_stateT S;
  }. all: solve_monad. 
  Qed.
End except_stateT.

Global Instance except_abstract_state : Except AbstractState.
Proof. apply except_maybeAT. Defined.

Require Import Classes.Except.
Instance except_conc : Except ConcreteState. 
Proof. apply except_maybeT. Defined.
