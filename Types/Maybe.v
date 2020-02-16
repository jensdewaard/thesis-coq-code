Require Import Utf8.
Require Import Classes.Monad.

Inductive Maybe (A : Type) : Type :=
    | Just : A -> Maybe A
    | None : Maybe A.
Arguments Just {_}.
Arguments None {_}.

Inductive AbstractMaybe (A : Type) : Type :=
  | JustA : A -> AbstractMaybe A
  | JustOrNoneA : A -> AbstractMaybe A
  | NoneA : AbstractMaybe A.
Arguments JustA {_}.
Arguments JustOrNoneA {_}.
Arguments NoneA {_}.

Definition MaybeT (M : Type → Type) (A : Type) : Type := M (Maybe A).
Section maybeT_laws.
  Context {M} `{M_monad : Monad M}.
  Definition NoneT {A} : MaybeT M A := returnM None.
  Definition JustT {A} (a : A) : MaybeT M A := returnM (Just a).

  Lemma justT_inj : ∀ A (x y : A),
    JustT x = JustT y → x = y.
  Proof.
    intros A x y H. 
    apply (returnM_inj (A:=Maybe A)) in H. inv H. reflexivity.
  Qed.
End maybeT_laws.

Definition MaybeAT (M : Type → Type) (A : Type) : Type := M (AbstractMaybe A).

Section maybeAT_laws.
  Context {M} `{M_monad : Monad M}.

  Definition NoneAT {A} : MaybeAT M A := returnM NoneA.
  Definition JustAT {A} (a : A) : MaybeAT M A := 
    returnM (JustA a).
  Definition JustOrNoneAT {A} (a : A) : MaybeAT M A := 
    returnM (JustOrNoneA a).

  Lemma justAT_inj : ∀ A (x y : A),
    JustAT x = JustAT y → x = y.
  Proof.
    intros A x y H. 
    apply (returnM_inj (A:=AbstractMaybe A)) in H. inv H. reflexivity.
  Qed.
End maybeAT_laws.
