Require Export Base.
Require Export Instances.Galois.
Require Import Classes.Galois.
Require Import Classes.IsBool.
Require Import Classes.IsBool.
Require Import Classes.IsNat.
Require Import Classes.Joinable.
Require Import Classes.Monad.
Require Import Classes.Monad.MonadFail.
Require Import Classes.PreorderedSet.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Even.
Require Import Coq.Arith.PeanoNat.
Require Import GenericInterpreter.
Require Import Instances.Joinable.
Require Import Instances.MonadExcept.
Require Import Instances.MonadFail.
Require Import Instances.Preorder.
Require Import Instances.Store.
Require Import Language.Statements.
Require Import Psatz.
Require Import Types.AbstractBool.
Require Import Types.Interval.
Require Import Types.Maps.
Require Import Types.Option.
Require Import Types.Parity.
Require Import Types.State.
Require Import Types.Stores.
Require Import Types.Subtype.

(* Soundness of unit *)
Lemma gamma_unit_sound :
  γ tt tt.
Proof. constructor.  Qed.
Hint Resolve gamma_unit_sound : soundness.

(* Soundness of functions *)
Lemma gamma_fun_apply {A A' B B'} `{Galois A A', Galois B B'}
    (f : A -> B) (f' : A' -> B') x x' :
  γ f f' -> γ x x' -> γ (f x) (f' x').
Proof. 
  eauto with soundness.
Qed.
Hint Extern 3 (γ (?f ?x) (?g ?y)) => apply gamma_fun_apply : soundness.

(* Soundness of interpreters *)

Definition avalue := (parity+abstr_bool)%type.

Definition ConcreteState := optionT (StateT (store cvalue) option).

Definition AbstractState := optionAT (StateT (store (avalue+⊤)) option).

Theorem eval_expr_sound : ∀ (e : expr), 
  γ 
    (shared_eval_expr (M:=AbstractState) (valType:=avalue+⊤) e)
    (shared_eval_expr (M:=ConcreteState) (valType:=cvalue) e).
Proof.
  eapply shared_eval_expr_sound; typeclasses eauto + eauto with soundness.
Qed.
Hint Resolve eval_expr_sound : soundness.

Theorem sound_interpreter: ∀ c, 
  γ (shared_ceval (M:=AbstractState) (valType:=avalue+⊤)
    (boolType:=(abstr_bool+⊤)) (natType:=(parity+⊤)) c) 
    (shared_ceval (M:=ConcreteState) (valType:=cvalue)
    (boolType:=bool) (natType:=nat) c).
Proof.
  eapply shared_ceval_sound; typeclasses eauto + eauto with soundness.
Qed.

