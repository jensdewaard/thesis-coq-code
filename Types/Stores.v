Require Export Base.
Require Import Types.Maps Language.Statements Classes.Joinable Classes.Galois.
Require Import Language.Statements.

Definition store (A : Type) := total_map A.

Definition store_update {A : Type} (s : store A) (x : string) (v : A) :
  store A := t_update s x v.

Definition abstract_store := store (avalue_par+⊤).
Definition concrete_store := store cvalue.

Definition gamma_store {A A' B B'} `{Galois A A', Galois B B'} 
  (st : store A) (st' : store A') : Prop := ∀ x : string, γ (st x) (st' x).

Instance galois_store {A A'} `{Galois A A'} : Galois (store A) (store A') :=
  gamma_store.

Definition store_join {A B} `{Joinable A B} (st1 st2 : store A) : store B :=
  λ x, (st1 x) ⊔ (st2 x).

Instance store_joinable {A B} `{Joinable A B} : Joinable (store A) (store B).
Proof.
  split with store_join. intros x y. unfold store_join. ext. rewrite join_comm.
  reflexivity.
Defined.

Instance store_join_sound {A A' B} {JA : Joinable A B} {GA : Galois A A'}
  {GB :Galois B A'} {JS: JoinableSound A B A'} :
  JoinableSound (store A) (store B) (store A').
Proof.
  intros x y z Hgamma. unfold "⊔"; simpl. unfold store_join. intros s. 
  apply JS. cbv in Hgamma. destruct Hgamma.
  - left; apply H.
  - right. apply H.
Qed.

Lemma store_update_sound {A A'} `{Galois A A'} :
  ∀ (st : store A) (st' : store A') x p n,
  γ st st' →
  γ p n →
  γ (store_update st x p) (store_update st' x n).
Proof.
  unfold store_update, t_update. intros. unfold γ, galois_store, gamma_store. 
  intros x'. destruct (beq_string x x'); eauto with soundness.
Qed.

