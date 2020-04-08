Require Export Base. 
Require Import Statements.
Require Import Types.Maps.
Require Import Classes.Monad.
Require Import Classes.IsNat.
Require Import Classes.IsBool.
Require Import Classes.Monad.MonadState.
Require Import Classes.Monad.MonadFail.
Require Import Classes.Monad.MonadExcept.
Require Import Classes.Galois.
Require Import Types.Stores.
Require Import Types.Parity.
Require Import Types.AbstractBool.
Require Import Types.Subtype.

Definition ensure_type (subType : Type)
  {M : Type → Type} `{MF : MonadFail M}
  {valType : Type}
  `{SubType subType valType}
  (n : valType) : M subType :=
  match project n with
  | Some x =>  returnM (M:=M) x
  | None => fail
  end.

Lemma ensure_type_sound {M M'} `{MM : Monad M, MM' : Monad M'}
  `{MF : MonadFail M} `{MF' : MonadFail M'}
  {subType subType' : Type} {valType valType' : Type} 
  `{GV: Galois valType valType'}
  `{GS : Galois subType subType'}
  `{GM : ∀ A A', Galois A A' → Galois (M A) (M' A')}
  `{ST : SubType subType valType} `{ST' : SubType subType' valType'}
  {SS : SubType_sound ST ST'} 
  {RS : return_sound M M'} :
    ∀ (n : valType) (n' : valType'),
  γ n n' → 
  γ (ensure_type (M:=M) (valType:=valType) subType n) 
    (ensure_type (M:=M') (valType:=valType') subType' n').
Proof.
  intros n n' Hgamma. unfold ensure_type. destruct SS. 
  apply project_sound in Hgamma. destruct (project n), (project n').
  - apply RS. inversion Hgamma; subst. assumption.
  - inversion Hgamma.
  - admit.
  - admit.
Admitted.

Fixpoint shared_eval_expr 
    {valType boolType natType : Type} {M : Type → Type} {MM : Monad M}
    {MF : MonadFail M} {MS : MonadState (store valType) M}
    {SB : SubType boolType valType}
    {SN : SubType natType valType}
    {PO : plus_op natType natType}
    {MO : mult_op natType natType}
    {EO : eq_op natType boolType}
    {LO : leb_op natType boolType}
    {NO : neg_op boolType boolType}
    {AO : and_op boolType boolType}
    (e : expr) : M valType :=
  match e with
  | EVal v => fail
  | EVar x =>
      s <- get;
      returnM (M:=M) (s x)
  | EPlus e1 e2 => 
      v1 <- shared_eval_expr e1 ;
      v2 <- shared_eval_expr e2 ;
      n1 <- ensure_type natType v1 ;
      n2 <- ensure_type natType v2 ;
      n <- returnM (M:=M) (n1 + n2) ;
      returnM (M:=M) (inject n)
  | EMult e1 e2 => 
      v1 <- shared_eval_expr e1 ;
      v2 <- shared_eval_expr e2 ;
      n1 <- ensure_type natType v1 ;
      n2 <- ensure_type natType v2 ;
      n <- returnM (M:=M) (n1 * n2) ;
      returnM (inject n)
  | EEq e1 e2 =>
      v1 <- shared_eval_expr e1 ;
      v2 <- shared_eval_expr e2 ;
      n1 <- ensure_type natType v1 ;
      n2 <- ensure_type natType v2 ;
      b <- returnM (M:=M) (n1 = n2) ;
      returnM (M:=M) (inject b)
  | ELe e1 e2 =>
      v1 <- shared_eval_expr e1 ;
      v2 <- shared_eval_expr e2 ;
      n1 <- ensure_type natType v1 ;
      n2 <- ensure_type natType v2 ;
      b <- returnM (M:=M) (leb n1 n2);
      returnM (M:=M) (inject b)
  | ENot e1 =>
      v1 <- shared_eval_expr e1 ;
      b1 <- ensure_type boolType v1 ;
      b <- returnM (M:=M) (neg b1);
      returnM (M:=M) (inject b)
  | EAnd e1 e2 =>
      v1 <- shared_eval_expr e1 ;
      v2 <- shared_eval_expr e2 ;
      b1 <- ensure_type boolType v1 ;
      b2 <- ensure_type boolType v2 ;
      b <- returnM (M:=M) (b1 && b2) ;
      returnM (M:=M) (inject b)
  end.

Definition avalue := ((parity+⊤)+(abstr_bool+⊤))%type.

Lemma shared_eval_expr_sound (M M' : Type → Type) {MM : Monad M}
  {MM' : Monad M'} {GM : ∀ A A', Galois A A' → Galois (M A) (M' A')}
  {avalue cvalue} {GV : Galois avalue cvalue}
  {natType natType' boolType boolType' : Type } 
  {GN : Galois natType natType'}
  {GB : Galois boolType boolType'}
  {SB : SubType boolType (avalue+⊤)}
  {SN : SubType natType (avalue+⊤)}
  {SB' : SubType boolType' cvalue}
  {SN' : SubType natType' cvalue}
  {SSB : SubType_sound SB SB'}
  {SSN : SubType_sound SN SN'}
  {MF : MonadFail M} {MF' : MonadFail M'} 
  {MS : MonadState (store (avalue+⊤)) M} {MS' : MonadState (store cvalue) M'}
  {ME : MonadExcept M} {ME' : MonadExcept M'} 
  {PO : plus_op natType natType} {PO' : plus_op natType' natType'}
  {MO : mult_op natType natType} {MO' : mult_op natType' natType'}
  {EO : eq_op natType boolType}  {EO' : eq_op natType' boolType'}
  {LO : leb_op natType boolType} {LO' : leb_op natType' boolType'}
  {NO : neg_op boolType boolType} {NO' : neg_op boolType' boolType'}
  {AO : and_op boolType boolType} {AO' : and_op boolType' boolType'}
  :
  get_state_sound (S:=store (avalue+⊤)) (S':=store cvalue) M M' →
  bind_sound M M' → 
  return_sound M M' → 
  plus_op_sound PO PO' →
  mult_op_sound MO MO' →
  eq_op_sound EO EO' →
  leb_op_sound LO LO' →
  neg_op_sound NO NO' →
  and_op_sound AO AO' → 
  ∀ (e : expr), 
  γ (shared_eval_expr (M:=M) (valType:=avalue+⊤) (natType:=natType) (boolType:=boolType) e) 
    (shared_eval_expr (M:=M') (valType:=cvalue) (natType:=natType') (boolType:=boolType') e).
Proof.
  intros GS BS RS PS.
  induction e.
  - simpl. admit.
  - simpl. apply bindM_sound; eauto with soundness.
    intros f g Hf. auto.
  - simpl. apply bindM_sound. assumption.
    intros ???. apply bindM_sound. assumption.
    intros ???. apply bindM_sound. apply ensure_type_sound. assumption.
    intros ???. apply bindM_sound. apply ensure_type_sound. assumption.
    intros ???. apply bindM_sound. apply returnM_sound. apply plus_sound;
    assumption.
    intros ???. apply returnM_sound. apply inject_sound. assumption.
  - simpl. apply bindM_sound. assumption.
    intros ???. apply bindM_sound. assumption.
    intros ???. apply bindM_sound. apply ensure_type_sound. assumption.
    intros ???. apply bindM_sound. apply ensure_type_sound. assumption.
    intros ???. apply bindM_sound. apply returnM_sound. apply mult_sound;
    assumption.
    intros ???. apply returnM_sound. apply inject_sound. assumption.
  - simpl. apply bindM_sound. assumption.
    intros ???. apply bindM_sound. assumption.
    intros ???. apply bindM_sound. apply ensure_type_sound. assumption.
    intros ???. apply bindM_sound. apply ensure_type_sound. assumption.
    intros ???. apply bindM_sound. apply returnM_sound. apply eq_sound;
    assumption.
    intros ???. apply returnM_sound. apply inject_sound. assumption.
  - simpl. apply bindM_sound. assumption.
    intros ???. apply bindM_sound. assumption.
    intros ???. apply bindM_sound. apply ensure_type_sound. assumption.
    intros ???. apply bindM_sound. apply ensure_type_sound. assumption.
    intros ???. apply bindM_sound. apply returnM_sound. apply leb_sound;
    assumption.
    intros ???. apply returnM_sound. apply inject_sound. assumption.
  - simpl. apply bindM_sound. assumption.
    intros ???. apply bindM_sound. apply ensure_type_sound. assumption.
    intros ???. apply bindM_sound. apply returnM_sound. apply neg_sound;
    assumption.
    intros ???. apply returnM_sound. apply inject_sound. assumption.
  - simpl. apply bindM_sound. assumption. 
    intros ???. apply bindM_sound. assumption.
    intros ???. apply bindM_sound. apply ensure_type_sound. assumption.
    intros ???. apply bindM_sound. apply ensure_type_sound. assumption.
    intros ???. apply bindM_sound. apply returnM_sound. apply and_sound;
    assumption.
    intros ???. apply returnM_sound. apply inject_sound. assumption.
Admitted.

Open Scope com_scope.

Fixpoint shared_ceval 
    {valType boolType natType : Type} 
    {M : Type → Type} 
    `{MM : !Monad M}
    `{MF : !MonadFail M} 
    `{MS : !MonadState (store valType) M}
    `{ME : !MonadExcept M} (c : com) 
    `{SubType boolType valType}
    `{SubType natType valType}
    `{PO : plus_op natType natType}
    `{MO : mult_op natType natType}
    `{EO : eq_op natType boolType}
    `{LO : leb_op natType boolType}
    `{NO : neg_op boolType boolType}
    `{AO : and_op boolType boolType}
    `{IO : if_op boolType (M unit)}
    : M unit :=
  match c with
  | CSkip => returnM (M:=M) tt
  | c1 ;c; c2 =>
      (shared_ceval c1) ;; (shared_ceval c2)
  | x ::= a => 
      v <- shared_eval_expr a ;
      s <- get ;
      put (t_update s x v)
  | CIf b c1 c2 => 
      v <- shared_eval_expr b ;
      b' <- ensure_type boolType v ;
      when b' (shared_ceval c1) (shared_ceval c2)
  | TRY c1 CATCH c2 => 
      catch (shared_ceval c1) (shared_ceval c2)
  | CFail => fail
  end.
