Require Import Classes.Monad.
Require Import Language.Statements.
Require Import Types.Maps.

Section Maybe.
  Inductive Maybe (A : Type) : Type :=
    | Just : A -> Maybe A
    | None : Maybe A.
  Arguments Just {_}.
  Arguments None {_}.
  Check Just.

  Definition return_maybe {A : Type} (a : A) : Maybe A :=
    Just a.
  Arguments return_maybe [_].

  Definition bind_maybe {A B : Type} 
    (m : Maybe A) (k : A -> Maybe B) : Maybe B :=
    match m with
    | None => None
    | Just a => k a
    end.
  Arguments bind_maybe [_ _].

  Global Instance monad_maybe : Monad Maybe :=
  {
    returnM := return_maybe;
    bindM := bind_maybe;
  }.

End Maybe.

Section AbstractMaybe.
  Inductive AbstractMaybe (A : Type) : Type :=
    | JustA : A -> AbstractMaybe A
    | JustOrNoneA : A -> AbstractMaybe A
    | NoneA : AbstractMaybe A.
  Arguments JustA {_}.
  Arguments JustOrNoneA {_}.
  Arguments NoneA {_}.

  Definition return_maybeA {A : Type} (a : A) : AbstractMaybe A :=
    JustA a.
  Arguments return_maybeA [_].

  Definition bind_maybeA {A B : Type}
    (m : AbstractMaybe A) (k : A -> AbstractMaybe B) : AbstractMaybe B :=
    match m with
    | NoneA => NoneA
    | JustA a => k a
    | JustOrNoneA a => match (k a) with
                       | NoneA => NoneA
                       | JustA b => JustOrNoneA b
                       | JustOrNoneA b => JustOrNoneA b
                       end
    end.
  Arguments bind_maybeA [_].

  Global Instance monad_abstract_maybe : Monad AbstractMaybe :=
  {
    returnM := return_maybeA;
    bindM := bind_maybeA;
  }.
End AbstractMaybe.

Section State.

  Definition state (S A : Type) := S -> (A * S).
  Definition return_state {S A : Type} (a : A) : state S A :=
    fun st => (a, st).
  Arguments return_state {_} [_].

(*Definition bind_state {A B : Type} (m : State A) (f : A -> State B) 
    : State B :=
  fun st => match m st with
            | returnR x st' => f x st'
            | crashed => crashed 
            | exception st' => exception st'
            end.*)
  Definition bind_state {S A B : Type} 
    (p : state S A) (k : A -> state S B) : state S B :=
    fun st => match (p st) with
              | (x, st') => k x st'
              end.
  Arguments bind_state {_} [_ _].

  Global Instance monad_state : forall s, Monad (state s) :=
  {
    returnM := return_state;
    bindM := bind_state;
  }.
End State.


  
