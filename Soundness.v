Require Export Base.
Require Import Omega.
Require Export Instances.Galois.
Require Import Classes.Functor.
Require Import Classes.Applicative.
Require Import Classes.Galois.
Require Import Classes.IsBool.
Require Import Classes.IsNat.
Require Import Classes.Joinable.
Require Import Classes.Monad.
Require Import Classes.PreorderedSet.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Even.
Require Import Coq.Arith.PeanoNat.
Require Import Instances.Except.
Require Import Instances.IsBool.AbstractBoolean.
Require Import Instances.IsBool.Boolean.
Require Import Instances.IsNat.Interval.
Require Import Instances.IsNat.Nat.
Require Import Instances.IsNat.Parity.
Require Import Instances.Joinable.
Require Import Instances.Monad.
Require Import Instances.Preorder.
Require Import Instances.Store.
Require Import Language.Statements.
Require Import SharedInterpreter.
Require Import Types.AbstractBool.
Require Import Types.Maps.
Require Import Types.Parity.
Require Import Types.Interval.
Require Import Types.Stores.

Hint Extern 0 (gamma _ _) => progress gamma_destruct : soundness.

Axiom gamma_pure_none : ∀ {M M' : Type → Type} `{Monad M, Monad M'} {A A' :
  Type}  `{Galois (M A) (M' (Maybe A'))} (c : M A), gamma (pure (F:=M') None) c.
Axiom gamma_pure_noneA : ∀ {M M' : Type → Type} `{Monad M, Monad M'} {A A' :
  Type}  `{Galois (M A) (M' (AbstractMaybe A'))} (c : M A), 
  gamma (pure (F:=M') NoneA) c.
Hint Resolve gamma_pure_none gamma_pure_noneA : soundness.

(* Soundness of unit *)
Lemma gamma_unit_sound :
  gamma tt tt.
Proof. constructor.  Qed.
Hint Resolve gamma_unit_sound : soundness.

(* Soundness of functions *)
Lemma gamma_fun_apply {A A' B B'} `{Galois A A', Galois B B'}
    (f : A -> B) (f' : A' -> B') x x' :
  gamma f' f -> gamma x' x ->
  gamma (f' x') (f x).
Proof. 
  eauto with soundness.
Qed.
Hint Extern 3 (gamma (?f ?x) (?g ?y)) => apply gamma_fun_apply : soundness.

Lemma gamma_fun_applied {A A' B B'} `{Galois A A', Galois B B'}
    (f : A -> B) (f' : A' -> B') :
      (forall x x', gamma x' x -> gamma (f' x') (f x)) ->
        gamma f' f.
Proof. 
  eauto with soundness.
Qed.
(*Hint Resolve gamma_fun_applied : soundness.*)

(* Soundness of monadic operations *)
Lemma fmap_maybe_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
  gamma (fmap_maybe (A:=A') (B:=B')) 
        (fmap_maybe (A:=A) (B:=B)).
Proof.
  eauto 10 with soundness.
Qed.
Hint Resolve fmap_maybe_sound : soundness.

Lemma pure_maybe_sound : ∀ (A A' : Type) `{Galois A A'},
  gamma (pure (F:=Maybe) (A:=A')) pure.
Proof.
  eauto with soundness.
Qed.
Hint Resolve pure_maybe_sound : soundness.

Lemma bind_maybe_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
  gamma (bindM (M:=Maybe) (A:=A') (B:=B')) 
        bindM.
Proof.
  unfold bindM; simpl.
  repeat constructor. intros.
  destruct a', a; eauto with soundness.
Qed.
Hint Resolve bind_maybe_sound : soundness.

Lemma app_maybe_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
  gamma (app (F:=Maybe) (A:=A') (B:=B')) app.
Proof. 
  repeat constructor.
  intros. destruct a, a', a0, a'0; eauto with soundness.
Qed.
Hint Resolve fmap_maybe_sound pure_maybe_sound app_maybe_sound 
  bind_maybe_sound : soundness.

Lemma fmap_abstract_maybe_sound (A A' B B' : Type) `{Galois A A', Galois B B'} : 
  gamma (fmap (F:=AbstractMaybe) (A:=A') (B:=B')) fmap.
Proof.
  repeat constructor. intros. destruct a0, a'0; eauto with soundness.
Qed.
Hint Resolve fmap_maybe_sound : soundness.

Lemma pure_abstract_maybe_sound (A A' : Type) `{Galois A A'} :
  gamma (pure (F:=AbstractMaybe)) pure.
Proof.
  eauto with soundness.
Qed.

Lemma app_abstract_maybe_sound (A A' B B' : Type) `{Galois A A', Galois B B'} :
  gamma (app (F:=AbstractMaybe) (A:=A') (B:=B')) app.
Proof.
  constructor; intros mf mf' Hmf. constructor; intros ma ma' Hma. 
  destruct ma, ma'; inv Hmf; inv Hma; eauto with soundness.
Qed.

Lemma bind_abstract_maybe_sound (A A' B B' : Type) `{Galois A A', Galois B B'} :
  gamma (bindM (M:=AbstractMaybe) (A:=A') (B:=B')) bindM.
Proof.
  unfold bindM; simpl.
  constructor; intros ma ma' Hma. constructor; intros mf mf' Hmf.
  destruct ma, ma' as [|a'|]; simpl; eauto with soundness.
  inversion Hma as [?|?|?|?? Ha ];subst.
  inversion Hmf as [?? Hf]; subst.
  apply Hf in Ha. all: destruct (mf' a'); eauto with soundness.
Qed.
Hint Resolve fmap_abstract_maybe_sound
             pure_abstract_maybe_sound
             app_abstract_maybe_sound
             bind_abstract_maybe_sound : soundness.

Lemma fmap_state_sound {S S' : Type} `{Galois S S'} : ∀ (A A' B B' : Type)
  `{Galois A A', Galois B B'}, 
  gamma (Galois:=GFun) 
  (A':=((A' → B') → State S' A' → State S' B'))
        (fmap_state (A:=A') (B:=B') (S:=S'))
        fmap_state.
Proof.
  unfold fmap_state. intros. constructor; intros f f' Hf.
  constructor; intros st st' Hst. constructor; intros s s' Hs.
  inversion Hst as [? ? Hgamma]; subst.
  apply Hgamma in Hs.
  destruct (st' s') as [a' s2']. destruct (st s) as [a s2].
  constructor; eauto with soundness.
Qed.

Lemma pure_state_sound {S S' : Type} `{Galois S S'} : ∀ (A A' : Type) 
  `{Galois A A'},
  gamma 
    (pure_state (A:=A') (S:=S')) 
    pure_state.
Proof.
  eauto with soundness. 
Qed.

Lemma app_state_sound {S S'} `{Galois S S'} : ∀ (A A' B B' : Type)
  `{Galois A A', Galois B B'},
  gamma
    (app_state (S:=S') (A:=A') (B:=B'))
    app_state.
Proof. 
  unfold app_state. intros. constructor; intros f f' Hf.
  constructor; intros st st' Hst. constructor; intros s s' Hs.
  inversion Hst as [?? Hgamma_s]; subst; clear Hst.
  inversion Hf as [?? Hgamma_f]; subst; clear Hf.
  apply Hgamma_f in Hs. destruct (f' s') as [f2' s2'], (f s) as [f2 s2]. 
  inversion Hs as [? ? Hf2 Hs2]; subst; simpl in *; clear Hs.
  apply Hgamma_s in Hs2.
  destruct (st' s2'), (st s2). 
  constructor; eauto with soundness.
Qed.

Lemma bind_state_sound {S S'} `{Galois S S'} : ∀ (A A' B B' : Type)
  `{Galois A A', Galois B B'},
  gamma
    (bind_state (S:=S') (A:=A') (B:=B'))
    bind_state.
Proof. 
  unfold bind_state. constructor; intros st st' Hst.
  constructor; intros f f' Hf. constructor; intros s s' Hs.
  inversion Hst as [?? Hgamma_st]; subst; clear Hst.
  apply Hgamma_st in Hs. destruct (st' s'), (st s).
  inversion Hs as [?? Ha Hs']; subst; clear Hs; simpl in *.
  repeat apply gamma_fun_apply; assumption.
Qed.
Hint Resolve fmap_state_sound pure_state_sound app_state_sound 
             bind_state_sound : soundness.

Section stateT.
  Context {M M' : Type → Type} `{Monad M, Monad M'}.
  Context {M_preorder : ∀ T', PreorderedSet T' → PreorderedSet (M' T')}.
  Context {M_galois : ∀ (T T' : Type) {HT : PreorderedSet T'}, 
      Galois T T' → Galois (M T) (M' T')}.
  Context {S S' : Type} `{Galois S S'}.

  Section fmap.
    Context {bind_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
      gamma (bindM (A:=A') (B:=B') (M:=M')) (bindM (M:=M) (A:=A) (B:=B))}.
    Context {pure_sound : ∀ (A A' : Type) `{Galois A A'},
      gamma (pure (A:=A') (F:=M')) pure}.

    Lemma fmap_stateT_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
      gamma (fmap_stateT (A:=A') (B:=B') (S:=S') (M:=M')) 
            (fmap_stateT (A:=A) (B:=B) (S:=S) (M:=M)).
    Proof.
      intros. unfold fmap_stateT. constructor. intros. constructor.
      intros. constructor. intros. repeat eapply gamma_fun_apply; eauto with
        soundness.
        constructor; intros. destruct a2, a'2. 
        repeat eapply gamma_fun_apply; eauto with soundness.
    Qed.
  End fmap.

  Section pure.
    Context {pure_sound : ∀ (A A' : Type) `{Galois A A'},
      gamma (pure (A:=A') (F:=M')) pure}.

    Lemma pure_stateT_sound : ∀ (A A' : Type) `{Galois A A'},
      gamma (pure_stateT (A:=A') (S:=S') (M:=M')) pure_stateT.
    Proof.
      intros. unfold pure_stateT. repeat constructor. intros. repeat eapply
      gamma_fun_apply; eauto with soundness.
    Qed.
  End pure.

  Section app.
    Context {bind_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
      gamma (bindM (A:=A') (B:=B') (M:=M')) bindM}.
    Context {pure_sound : ∀ (A A' : Type) `{Galois A A'},
      gamma (pure (A:=A') (F:=M')) pure}.
    
    Lemma app_stateT_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
      gamma (app_stateT (A:=A') (B:=B') (S:=S') (M:=M')) app_stateT.
    Proof.
      intros. unfold app_stateT. repeat constructor; intros.
      repeat eapply gamma_fun_apply; eauto with soundness.
      constructor; intros. destruct a'2, a2. repeat eapply gamma_fun_apply; eauto
      with soundness. constructor; intros. destruct a'2, a2. repeat eapply
      gamma_fun_apply; eauto with soundness.
    Qed.
  End app.

  Section bind.
    Context {bind_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
      gamma (bindM (A:=A') (B:=B') (M:=M')) bindM}.

    Lemma bind_stateT_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
      gamma (bind_stateT (A:=A') (B:=B') (S:=S') (M:=M')) bind_stateT.
    Proof.
      intros. unfold bind_stateT. repeat constructor; intros. repeat eapply
      gamma_fun_apply; eauto with soundness. constructor; intros.
      destruct a'2, a2. repeat eapply gamma_fun_apply; eauto with soundness.
    Qed.
  End bind.
End stateT.

Section maybeT.
  Context {M M' : Type → Type} `{Monad M, Monad M'}.
  Context {M_preorder : ∀ T', PreorderedSet T' → PreorderedSet (M' T')}.
  Context {M_galois : ∀ A A' (A_pre: PreorderedSet A'), 
    Galois A A' → Galois (M A) (M' A')}.

  Section fmap.
    Context {fmap_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
      gamma (fmap (F:=M') (A:=A') (B:=B')) (fmap (A:=A) (B:=B) (F:=M))}.

    Lemma fmap_maybeT_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
      gamma (fmap_maybeT (A:=A') (B:=B') (M:=M')) 
            fmap_maybeT.
    Proof.
      intros. unfold fmap_maybeT. repeat constructor. intros.
      repeat eapply gamma_fun_apply; eauto with soundness.
    Qed.
  End fmap.

  Section pure.
    Context {pure_sound : ∀ (A A' : Type) `{Galois A A'},
      gamma (pure (A:=A') (F:=M')) pure}.

    Lemma pure_maybeT_sound : ∀ (A A' : Type) `{Galois A A'},
      gamma (pure_maybeT (A:=A') (M:=M')) pure_maybeT.
    Proof. 
      intros. unfold pure_maybeT. constructor. intros. repeat eapply
      gamma_fun_apply; eauto with soundness. 
    Qed.
  End pure.

  Section app.
    Context {bind_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
      gamma (bindM (A:=A') (B:=B') (M:=M')) bindM}.
    Context {pure_sound : ∀ (A A' : Type) `{Galois A A'},
      gamma (pure (A:=A') (F:=M')) pure}.

    Lemma app_maybeT_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
      gamma (app_maybeT (A:=A') (B:=B') (M:=M')) app_maybeT. 
    Proof.
      intros. unfold app_maybeT. repeat constructor; intros. unfold MaybeT.
      repeat eapply gamma_fun_apply; eauto with soundness. 
      constructor. intros. destruct a'1, a1; eauto with soundness.
      repeat eapply gamma_fun_apply; eauto with soundness.
      constructor; intros. destruct a'1, a1; eauto with soundness.
    Qed.
  End app.

  Section bind.
    Context {bind_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
      gamma (bindM (A:=A') (B:=B') (M:=M')) bindM}.
    Context {pure_sound : ∀ (A A' : Type) `{Galois A A'},
      gamma (pure (A:=A') (F:=M')) pure}.

    Lemma bind_maybeT_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
      gamma (bind_maybeT (A:=A') (B:=B') (M:=M')) bind_maybeT.
    Proof. 
      intros. unfold bind_maybeT. repeat constructor; intros. 
      repeat eapply gamma_fun_apply; eauto with soundness.
      constructor; intros. unfold NoneT. destruct a'1, a1; eauto with soundness.
    Qed.
  End bind.
End maybeT.

Section maybeAT.
  Context {M M' : Type → Type} `{Monad M, Monad M'}.
  Context {M_preorder : ∀ T', PreorderedSet T' → PreorderedSet (M' T')}.
  Context `{M_galois : ∀ A A' (A_pre : PreorderedSet A'), 
    Galois A A' → Galois (M A) (M' A')}.

  Section fmap.
    Context {fmap_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
      gamma (fmap (F:=M') (A:=A') (B:=B')) (fmap (A:=A) (B:=B) (F:=M))}.

    Lemma fmap_maybeAT_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
      gamma (fmap_maybeAT (A:=A') (B:=B') (M:=M')) 
            (fmap_maybeT (A:=A) (B:=B) (M:=M)).
    Proof.
      intros. unfold fmap_maybeAT, fmap_maybeT; repeat constructor; intros.
      repeat eapply gamma_fun_apply; eauto with soundness.
    Qed.
  End fmap.

  Section pure.
    Context {pure_sound : ∀ (A A' : Type) `{Galois A A'},
      gamma (pure (A:=A') (F:=M')) pure}.
    
    Lemma pure_maybeAT_sound : ∀ (A A' : Type) `{Galois A A'},
      gamma (pure_maybeAT (A:=A') (M:=M')) pure_maybeT.
    Proof.
      intros. unfold pure_maybeAT, pure_maybeT; repeat constructor; intros.
      repeat eapply gamma_fun_apply; eauto with soundness.
    Qed.
  End pure.

  Section app.
    Context {app_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
      gamma (app (F:=M') (A:=A') (B:=B')) (app (A:=A) (B:=B) (F:=M))}.
    Context {bind_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
      gamma (bindM (A:=A') (B:=B') (M:=M')) bindM}.
    Context {pure_sound : ∀ (A A' : Type) `{Galois A A'},
      gamma (pure (A:=A') (F:=M')) pure}.

    Lemma app_maybeAT_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
      gamma (app_maybeAT (A:=A') (B:=B') (M:=M')) app_maybeT.
    Proof.
      intros. unfold app_maybeAT, app_maybeT; repeat constructor; intros.
      repeat eapply gamma_fun_apply; eauto with soundness.
      repeat constructor; intros. destruct a'1, a1; eauto with soundness.
      - repeat eapply gamma_fun_apply; eauto with soundness.
        constructor; intros. destruct a'1, a1; 
        repeat eapply gamma_fun_apply; eauto with soundness.
      - repeat eapply gamma_fun_apply; eauto with soundness.
        constructor; intros. destruct a'1, a1;
        repeat eapply gamma_fun_apply; eauto with soundness.
      - admit.
    Admitted.
  End app.

  Section bind.
    Context {bind_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
      gamma (bindM (A:=A') (B:=B') (M:=M')) bindM}.

    Lemma bind_maybeAT_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
      gamma (bind_maybeAT (A:=A') (B:=B') (M:=M')) bind_maybeT.
    Proof.
      intros. unfold bind_maybeAT, bind_maybeT. repeat constructor; intros.
      repeat eapply gamma_fun_apply; eauto with soundness.
      repeat constructor; intros. destruct a'1, a1; eauto with soundness.
      - admit.
      - admit.
    Admitted.
  End bind.

  Section lift.
    Context {fmap_sound : ∀ (A A' B B' : Type) `{Galois A A', Galois B B'},
      gamma (fmap (F:=M') (A:=A') (B:=B')) (fmap (A:=A) (B:=B) (F:=M))}.

    Lemma lift_maybeAT_sound {A A'} `{Galois A A'} :
      gamma (lift_maybeAT (M:=M') (A:=A')) (lift_maybeT (A:=A)).
    Proof.
      unfold lift_maybeAT, lift_maybeT. 
      repeat constructor. intros.
      repeat eapply gamma_fun_apply; eauto with soundness.
    Qed.
    Hint Resolve lift_maybeAT_sound : soundness.
  End lift.

(* Soundness of parity operations *)

Lemma gamma_par_extract_n_n : forall n,
  gamma (extract_par n) n.
Proof.
  intros. autounfold with soundness. 
  destruct (Nat.even n) eqn:Hpar. 
  - rewrite Nat.even_spec in Hpar. eauto with soundness.
  - pose proof Nat.negb_even. 
    constructor.
    rewrite <- Nat.odd_spec. rewrite <- Nat.negb_even, Bool.negb_true_iff.
    assumption.
Qed.
Hint Resolve gamma_par_extract_n_n : soundness.

Lemma parity_plus_sound :
  gamma parity_plus plus.
Proof.
  autounfold with soundness. repeat constructor. intros.
  destruct a', a'0; eauto with soundness.
Qed.
Hint Resolve parity_plus_sound : soundness.

Lemma parity_mult_sound :
  gamma parity_mult mult.
Proof. 
  autounfold with soundness. repeat constructor; intros.
  destruct a', a'0; gamma_destruct; try constructor; eauto with soundness.
Qed.
Hint Resolve parity_mult_sound : soundness.

Hint Rewrite Nat.eqb_eq : soundness.
Lemma parity_eq_sound :
  gamma parity_eq Nat.eqb. 
Proof. 
  repeat constructor. intros. destruct a', a'0; simpl; try constructor.
  2: eauto with soundness. 3-8: eauto with soundness.
  gamma_destruct. assert (a ≠ a0). unfold not. intro; subst.
  apply (Nat.Even_Odd_False a0); auto. rewrite Nat.eqb_neq; auto.
  gamma_destruct. assert (a ≠ a0). unfold not. intro; subst.
  apply (Nat.Even_Odd_False a0); auto. rewrite Nat.eqb_neq; auto.
Qed.
Hint Resolve parity_eq_sound : soundness.

Lemma extract_par_sound : forall n,
  gamma (VParity (extract_par n)) (VNat n).
Proof. 
  intros. unfold extract_par. destruct (Nat.even n) eqn:Hpar; repeat constructor.
  rewrite <- Nat.even_spec; auto.
  rewrite <- Nat.odd_spec. unfold Nat.odd. rewrite Hpar. reflexivity.
Qed.


(* Monadic versions of parity operations *)
Lemma ensure_par_sound : 
  gamma ensure_par ensure_nat.
Proof.
  repeat constructor; intros. destruct a, a'; eauto with soundness.
Qed.
Hint Resolve ensure_par_sound : soundness.

Lemma extract_parM_sound : forall n,
  gamma (extract_parM n) (extract_natM n). 
Proof. 
  intros. unfold extract_parM, extract_natM. simpl. 
  repeat eapply gamma_fun_apply; eauto with soundness. 
  unfold pure; simpl.
  eapply fmap_stateT_sound.
  Unshelve. all: eauto with soundness. 
Qed. 
Hint Resolve extract_parM_sound : soundness.

Lemma pplusM_sound : 
  gamma pplusM plusM.
Proof. 
  repeat constructor. repeat eapply gamma_fun_apply; eauto with soundness.
  eauto with soundness.
Qed.
Hint Resolve pplusM_sound : soundness.

Lemma pmultM_sound :
  gamma pmultM multM.
Proof.
  repeat constructor; eauto with soundness. 
Qed.
Hint Resolve pmultM_sound : soundness.

Lemma peqM_sound :
  gamma peqM eqbM.
Proof.
  repeat constructor; eauto with soundness.
Qed.
Hint Resolve peqM_sound : soundness.

Lemma pleM_sound :
  gamma pleM lebM.
Proof.
  repeat constructor; eauto with soundness.
Qed.
Hint Resolve pleM_sound : soundness.

Lemma build_parity_sound :
  gamma build_parity build_natural.
Proof.
  repeat constructor; eauto with soundness.
Qed.
Hint Resolve build_parity_sound : soundness.

(* Soundness of operations on intervals *)
Lemma iplusM_sound :
  gamma iplusM plusM.
Proof. 
  repeat constructor; eauto with soundness.
  - rewrite interval_min_plus. gamma_destruct. simpl in *. omega.
  - rewrite interval_max_plus. gamma_destruct. simpl in *. omega.
Qed.
Hint Resolve iplusM_sound : soundness.

Lemma imultM_sound :
  gamma imultM multM.
Proof.
  repeat constructor. 3: eauto with soundness.
  - rewrite interval_min_mult. gamma_destruct; simpl in *. 
    apply Coq.Arith.Mult.mult_le_compat; auto.
  - rewrite interval_max_mult. gamma_destruct; simpl in *.
    apply Coq.Arith.Mult.mult_le_compat; auto.
Qed.
Hint Resolve imultM_sound : soundness.

Lemma ileqb_sound :
  gamma ileM lebM.
Proof.
  constructor. intros n i Hin. constructor. intros n0 i0 Hin0.
  repeat constructor; eauto with soundness.
  unfold ileqb. gamma_destruct. simpl in *. 
  destruct (max i <? min i0) eqn:Hcompa, (n <=? n0) eqn:Hcompb; eauto with
    soundness.
  rewrite leb_iff_conv in Hcompb. assert (min i0 <= max i). 
  eapply le_trans. apply H5. eapply le_trans. apply H7.
Admitted.
Hint Resolve ileqb_sound : soundness.

Lemma ieqM_sound : gamma ieqM eqbM.
Proof.
  repeat constructor; eauto with soundness.
  repeat eapply gamma_fun_apply; eauto with soundness. 
Admitted.
Hint Resolve ieqM_sound : soundness.

Lemma build_interval_sound :
  gamma build_interval build_natural.
Proof.
  repeat constructor; simpl; gamma_destruct; eauto with soundness.
Qed.
Hint Resolve build_interval_sound : soundness.

Lemma extract_interval_sound : forall n,
  gamma (extract_interval n) (extract_natM n).
Proof.
  repeat constructor; unfold min, max; simpl; try rewrite Nat.leb_refl; 
    eauto with soundness.
Qed.
Hint Resolve extract_interval_sound : soundness.

Lemma ensure_interval_sound : gamma ensure_interval ensure_nat.
Proof.
  repeat constructor; eauto with soundness.
  intros ???. unfold ensure_interval, ensure_nat.
  destruct a, a'; try contradiction; eauto with soundness.
  repeat eapply gamma_fun_apply; eauto with soundness.
  simpl. 
Admitted.
Hint Resolve ensure_interval_sound : soundness.

(* Soundness of operations on booleans *)

Lemma ab_and_sound :
  gamma and_ab andb.
Proof. 
  repeat constructor; intros. 
  destruct_all bool; destruct_all abstr_bool; eauto with soundness.
Qed.
Hint Resolve ab_and_sound : soundness.

Lemma ab_or_sound :
  gamma or_ab orb.
Proof. 
  repeat constructor; intros.
  destruct_all bool; destruct_all abstr_bool; eauto with soundness.
Qed.
Hint Resolve ab_or_sound : soundness.

Lemma ab_neg_sound :
  gamma neg_ab negb.
Proof. 
  repeat constructor; intros. 
  destruct_all bool; destruct_all abstr_bool; eauto with soundness.
Qed.

Lemma extract_bool_sound : forall x,
  gamma (VAbstrBool (extract_ab x)) (VBool x).
Proof. 
  intros. destruct x; eauto with soundness.
Qed.
Hint Resolve extract_bool_sound : soundness.

(* Monadic operations on abstract booleans *)

Lemma ensure_abool_sound :
  gamma ensure_abool ensure_bool.
Proof. 
  constructor. intros a b Hab. unfold ensure_abool, ensure_bool.
  destruct a, b; eauto with soundness. 
  repeat eapply gamma_fun_apply; eauto with soundness. simpl.
  repeat constructor; intros. unfold lift_maybeAT, lift_maybeT.
  repeat eapply gamma_fun_apply; eauto with soundness. simpl.
  eapply fmap_stateT_sound. Unshelve. all: eauto with soundness.
Qed.
Hint Resolve ensure_abool_sound : soundness.

Lemma neg_abM_sound :
  gamma neg_abM negbM.
Proof.
  repeat constructor; eauto with soundness.
Qed.
Hint Resolve neg_abM_sound : soundness.

Lemma and_abM_sound :
  gamma and_abM andbM.
Proof.
  unfold and_abM, andbM. simpl. constructor; intros. constructor; intros.
  repeat eapply gamma_fun_apply; eauto with soundness.
  eapply fmap_stateT_sound. Unshelve. all: eauto with soundness.
Qed.
Hint Resolve and_abM_sound : soundness.

Lemma extract_abM_sound: forall b,
  gamma (extract_abM b) (extract_boolean b).
Proof. 
  unfold extract_abM, extract_boolean. simpl. intro b.
  repeat eapply gamma_fun_apply; eauto with soundness.
  eapply fmap_stateT_sound. Unshelve. destruct b. all: eauto with soundness.
Qed.
Hint Resolve extract_abM_sound : soundness.

Lemma build_boolean_sound :
  gamma build_abool build_boolean.
Proof.
  repeat constructor; eauto with soundness.
Qed.
Hint Resolve build_boolean_sound : soundness.

(* Soundness of applied functions *)

(* Soundness of operations on stores *)

(*Lemma store_get_sound : forall s,
  gamma (abstract_store_get s) (store_get s).
Proof.
  repeat constructor. inv H0. apply H1. inv H0; assumption.
  inv H; assumption.
Qed.
Hint Resolve store_get_sound : soundness.*)

Lemma t_update_sound : forall (ast : abstract_store) (st : store) x p n,
  gamma ast st ->
  gamma p n ->
  gamma (t_update ast x p) (t_update st x n).
Proof. 
  unfold t_update. repeat constructor; eauto with soundness.
  intros x'. destruct (beq_string x x'); eauto with soundness.
Qed.

(*Lemma store_put_sound : forall s,
  gamma (abstract_store_put s) (store_put s).
Proof. 
  repeat constructor; simpl.
  intros x. unfold t_update. destruct (beq_string s x). assumption.
  inv H1. apply H2. inv H0; assumption.
Qed.
Hint Resolve store_put_sound : soundness.
*)

(* Soundness of states *)
(*
Lemma bind_state_sound_fun {A A' B B'} `{Galois A A', Galois B B'} : 
  forall next next' f f',
  gamma f' f ->
  (forall x x', gamma x' x -> gamma (next' x') (next x)) ->
  gamma (@bind_state_abstract A' B' f' next') (@bind_state A B f next).
Proof. 
  intros. apply bind_state_sound. assumption. 
  assert ((forall x x', gamma x' x -> gamma (next' x') (next x)) -> gamma next'
  next). 
  { intros Hnext ???. apply Hnext. assumption. }
  apply H5. assumption.
Qed.
Hint Resolve bind_state_sound_fun : soundness.
*)

(* Soundness of interpreters *)


Definition ConcreteState := MaybeT (StateT store Maybe).

Definition AbstractState := 
  MaybeAT (StateT abstract_store Maybe).

Lemma extract_build_val_sound : forall v,
  gamma (extract_build_val (M:=AbstractState) (A:=isnat_parity) v) 
        (extract_build_val (M:=ConcreteState) v).
Proof.
  destruct v; repeat constructor; eauto with soundness. destruct b; auto with
    soundness.
Qed.
Hint Resolve extract_build_val_sound : soundness.
Arguments bindM : simpl never.
Theorem eval_expr_sound : forall a,
  gamma (shared_eval_expr (M:=AbstractState) (A:=isnat_parity) a) 
        (shared_eval_expr (M:=ConcreteState) a).
Proof.
  intros. induction a; repeat constructor; simpl; intros.
  - auto using gamma_fun_apply with soundness.
  - debug auto using gamma_fun_apply with soundness. gamma_destruct.
    auto.
  - intros. repeat apply gamma_fun_apply; eauto with soundness.
  - eauto with soundness.
  - simpl. intros. repeat apply gamma_fun_apply; eauto with soundness.
    admit.
    repeat constructor; intros. eapply gamma_fun_apply.
    eapply gamma_fun_apply. apply gamma_fun_apply. admit.
    
    intros. debug auto using gamma_fun_apply with soundness.
    gamma_destruct. 
    apply gamma_fun_apply. 
    apply extract_build_val_sound.
  - gamma_destruct. debug eauto using gamma_fun_apply with soundness.
    Print HintDb soundness.
  - debug eauto using gamma_fun_apply with soundness.
  - debug eauto using gamma_fun_apply with soundness. admit.
  - eauto with soundness. admit.
  - eauto with soundness. admit.
  - eauto with soundness. intros. admit.
  - eauto with soundness. admit.
  - eauto with soundness. 
Admitted.
Hint Resolve eval_expr_sound : soundness.

Lemma sound_if_op : 
  gamma (eval_if_abstract)
  (eval_if).
Proof.
  constructor. intros. constructor. intros. constructor. intros.
  destruct b. 
Admitted.

(*Lemma sound_eval_catch :
  gamma (eval_catch_abstract) (eval_catch).
Proof.
  intros s1' s1 H s2' s2. intros H0 a b H1. 
  unfold gamma in H, H0; simpl in H, H0; unfold gamma_fun in H, H0.
  unfold eval_catch_abstract, eval_catch.
  pose proof H1; apply H in H1.
  destruct (s1' a).
  - destruct (s1 b). 
    + apply H1.
    + apply H1.
    + inversion H1.
  - reflexivity.
  - destruct (s1 b).  
    + inversion H1.
    + inversion H1.
    + apply H0. apply H1.
  - destruct (s1 b).
    + eapply widen. apply join_upper_bound_left.
      apply H1.
    + inversion H1.
    + unfold gamma in H1; simpl in H1.
      eapply widen. apply join_upper_bound_right. unfold gamma; simpl.
      pose proof H1. apply H0 in H1.  apply H1.
Qed.
Hint Resolve sound_eval_catch : soundness.
*)
  (*
Lemma sound_fail : 
  gamma fail_abstract fail.
Proof.
  unfold fail_abstract, fail. intros ???. auto.
Qed.
Hint Resolve sound_fail : soundness.
*)

Theorem sound_interpreter:
  forall c, gamma (shared_ceval 
                    (M:=AbstractState) 
                    (A:=isnat_parity)
                    c) 
                  (shared_ceval (M:=ConcreteState) c).
Proof.
  induction c; simpl. 
  - eauto with soundness.
  - eauto with soundness. admit.
  - eauto with soundness. admit.
  - eauto with soundness. admit.
  - eauto with soundness. admit.
  - eauto with soundness.
Admitted.

