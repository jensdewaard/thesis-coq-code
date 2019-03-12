Require Import Maps.
Require Import Parity.

Definition store := total_map nat.
Definition abstract_store := total_map parity.

Definition sound_store (ast : abstract_store) (st : store) : Prop := 
  forall x, gamma_par (ast x) (st x).

Definition abstract_store_top : abstract_store :=
  fun _ => par_top.
Definition abstract_store_bottom : abstract_store :=
  fun _ => par_bottom.
Definition abstract_store_join
    (ast1 ast2 : abstract_store) : abstract_store :=
  fun x => parity_join (ast1 x) (ast2 x).

Lemma t_update_sound : forall ast st x p n,
  sound_store ast st ->
  gamma_par p n ->
  sound_store (t_update ast x p) (t_update st x n).
Proof. 
  intros. unfold sound_store.  intros. unfold t_update. 
  destruct (beq_string x x0). 
  - assumption.
  - unfold sound_store in H. apply H.
Qed.

Require Import Coq.Logic.FunctionalExtensionality.
Lemma abstract_store_join_comm : forall ast1 ast2,
  abstract_store_join ast1 ast2 = abstract_store_join ast2 ast1.
Proof. 
  intros. unfold abstract_store_join. apply functional_extensionality.
  intros. apply parity_join_comm. Qed.

Lemma abstract_store_join_sound_left : forall ast1 ast2 st,
  sound_store ast1 st ->
  sound_store (abstract_store_join ast1 ast2) st.
Proof. 
  unfold sound_store. intros. unfold abstract_store_join. apply
  parity_join_sound_left. apply H.
Qed.

Corollary abstract_store_join_sound_right : forall ast1 ast2 st,
  sound_store ast2 st ->
  sound_store (abstract_store_join ast1 ast2) st.
Proof. 
  unfold sound_store. intros. unfold abstract_store_join. apply
  parity_join_sound_right. apply H.
Qed.

Lemma abstract_store_join_assoc : forall ast1 ast2 ast3,
  abstract_store_join ast1 (abstract_store_join ast2 ast3) =
  abstract_store_join (abstract_store_join ast1 ast2) ast3.
Proof. 
  intros. unfold abstract_store_join. apply functional_extensionality.
  intros. rewrite <- parity_join_assoc. reflexivity.
Qed.

Lemma abstract_store_join_idem : forall ast,
  abstract_store_join ast ast = ast.
Proof. 
  intros. unfold abstract_store_join. apply functional_extensionality.
  intros. rewrite parity_join_idem. reflexivity.
Qed.



