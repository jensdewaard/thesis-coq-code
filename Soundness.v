Require Export Base.
Require Export Instances.Galois.
Require Import Classes.Galois.
Require Import Classes.Joinable.
Require Import Classes.Monad.
Require Import Classes.Monad.MonadFail.
Require Import Classes.PreorderedSet.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Even.
Require Import Coq.Arith.PeanoNat.
Require Import Instances.MonadExcept.
Require Import Instances.MonadFail.
Require Import Instances.Joinable.
Require Import Instances.Preorder.
Require Import Instances.Store.
Require Import Language.Statements.
Require Import Psatz.
Require Import SharedInterpreter.
Require Import Types.AbstractBool.
Require Import Types.Interval.
Require Import Types.Maps.
Require Import Types.Parity.
Require Import Types.State.
Require Import Types.Stores.
Require Import Classes.IsBool.
Require Import Types.Subtype.
Require Import Classes.IsNat.
Require Import Types.Option.

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

Definition avalue := ((parity+⊤)+(abstr_bool+⊤))%type.

Definition ConcreteState := optionT (StateT (store cvalue) option).

Definition AbstractState := optionAT (StateT (store (avalue+⊤)) option).

(*** Refactor these lemmas ***)
Lemma joinable_values_idem : @JoinableIdem (avalue +⊤)
  (@top_joinable_l avalue avalue
     (@sum_joinable (parity +⊤) (abstr_bool +⊤) (parity +⊤) 
        (abstr_bool +⊤) (@top_joinable_l parity parity parity_joinable)
        (@top_joinable_l abstr_bool abstr_bool abstr_bool_joinable))).
Proof.
  intros a. destruct a. constructor. destruct a.
  - destruct t. constructor. destruct p; constructor.
  - destruct t. constructor. destruct a; constructor.
Qed.
Hint Resolve joinable_values_idem : soundness.

Lemma subtype_trans_r_sound' : SubType_sound 
    (subtype_trans_r (parity +⊤) (subtype_top_r abstr_bool))
  (subtype_r nat bool).
Proof. split.
  - intros s s' Hs. simpl. unfold compose. destruct s, s'.
    + constructor. reflexivity.
    + inversion Hs. inversion H.
    + inversion Hs. inversion H.
    + constructor. reflexivity.
  - intros s s' Hs. destruct s, s'; try constructor; try inversion Hs.
    + destruct t. constructor. constructor. apply Hs.
Qed.
Hint Resolve subtype_trans_r_sound' : soundness.

Lemma subtype_trans_l_sound' : SubType_sound
  (subtype_trans_l parity (parity +⊤) (abstr_bool +⊤) (subtype_top_r parity))
  (subtype_l nat bool).
Proof. split.
  - intros s s' Hs. apply Hs.
  - intros s s' Hs. destruct s, s'; try constructor.
    + destruct t; constructor. apply Hs.
    + inversion Hs.
Qed.
Hint Resolve subtype_trans_l_sound' : soundness.

(* TODO abstract the above *)

Theorem eval_expr_sound : ∀ (e : expr), 
  γ 
    (shared_eval_expr (M:=AbstractState) (valType:=avalue+⊤) e)
    (shared_eval_expr (M:=ConcreteState) (valType:=cvalue) e).
Proof.
  eapply shared_eval_expr_sound; eauto 10 with soundness.
  - apply except_optionT. apply monad_stateT.
  - apply bind_optionAT_stateT_sound.
  - apply someAT_stateT_sound.
Qed.
Hint Resolve eval_expr_sound : soundness.

Require Import Classes.IsBool.
Theorem sound_interpreter: ∀ c, 
  γ (shared_ceval (M:=AbstractState) (valType:=avalue+⊤)
    (boolType:=(abstr_bool+⊤)) (natType:=(parity+⊤)) c) 
    (shared_ceval (M:=ConcreteState) (valType:=cvalue)
    (boolType:=bool) (natType:=nat) c).
Proof.
  eapply shared_ceval_sound; eauto 10 with soundness. 
  - apply catch_optionAT_sound.
  - apply bind_optionAT_stateT_sound.
  - apply someAT_stateT_sound.
  - apply if_top_sound. eauto 10 with soundness. 
    apply if_ab_op_sound. 
Qed.

