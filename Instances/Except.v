Require Import Classes.Except.
Require Import Classes.Joinable.
Require Import Instances.Joinable.
Require Import Types.Stores.
Require Import Types.Result.
Require Import Types.State.
Require Import Instances.Monad.
Require Import Classes.Monad.
Require Import Classes.Applicative.

Section except_maybe.
  Definition trycatch_maybe {A : Type} (x y : Maybe A) : Maybe A :=
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
  Context {M : Type -> Type} `{Applicative M} {inst : Monad M}.

  Definition throw_maybeT (A : Type) : MaybeT M A :=
    @pure M _ H0 _ (@None A).
  Hint Unfold throw_maybeT : soundness.

  Definition trycatch_maybeT {A} (mx my : MaybeT M A) : MaybeT M A :=
    @bindM M _ _ inst _ _ mx (fun x : Maybe A =>
      match x with
      | None => my
      | Just a => pure (Just a)
      end).
  Hint Unfold trycatch_maybeT : soundness.
  Arguments trycatch_maybeT [_].

  Instance except_maybeT : Except (MaybeT M) :=
  {
    throw := throw_maybeT;
    trycatch := trycatch_maybeT;
  }. all: solve_monad. Defined.

End except_maybeT.
Require Import Classes.PreorderedSet.
Section except_maybeAT.
  Context {M : Type -> Type} `{inst : Monad M}.

  Definition throw_maybeAT (A : Type) : MaybeAT M A := pure (@NoneA A).

  Definition trycatch_maybeAT {A}
    (mx my : MaybeAT M A) : MaybeAT M A :=
    @bindM M _ _ inst _ _ mx (fun x : AbstractMaybe A =>
      match x with
      | JustA a => pure (JustA a)
      | JustOrNoneA a => pure (JustOrNoneA a) (* should be a join_op *)
      | NoneA => my
      end).
  Arguments trycatch_maybeAT [_].
  Hint Unfold throw_maybeAT trycatch_maybeAT : soundness.

  Instance except_maybeAT : Except (MaybeAT M) :=
    {
      throw := throw_maybeAT;
      trycatch := trycatch_maybeAT;
    }. 
    Admitted.
End except_maybeAT.

Section except_stateT.
  Context {M : Type -> Type} `{inst_m : Monad M} 
    `{inst_e : @Except M _ _ inst_m}.

  Definition throw_stateT {S} A : StateT S M A := liftT throw.

  Definition trycatch_stateT {S A} (a b : StateT S M A) : StateT S M A := 
    fun s => trycatch (a s) (b s).
  Hint Unfold throw_stateT trycatch_stateT : soundness.

  Instance except_stateT (S : Type) : Except (StateT S M) :=
  {
    throw := @throw_stateT S;
    trycatch := @trycatch_stateT S;
  }. 
  Admitted.
End except_stateT.

Global Instance except_abstract_state : Except AbstractState.
Proof. apply except_maybeAT. Defined.
