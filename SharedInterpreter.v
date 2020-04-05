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
  {SS : SubType_sound valType valType'} 
  {RS : return_sound M M'} :
    ∀ (n : valType) (n' : valType'),
  γ n n' → 
  γ (ensure_type (M:=M) (valType:=valType) subType n) 
    (ensure_type (M:=M') (valType:=valType') subType' n').
Proof.
  intros n n' Hgamma. unfold ensure_type. destruct SS. 
  apply project_sound with (sub:=subType) (sub':=subType') (ST:=ST) (ST':=ST')
  (GS:=GS) in Hgamma. destruct (project n), (project n').
  - apply RS. inversion Hgamma; subst. assumption.
  - inversion Hgamma.
  - admit.
  - admit.
Admitted.

Fixpoint shared_eval_expr 
    {valType boolType natType : Type} {M : Type → Type} `{MM : !Monad M}
    `{MF : !MonadFail M} `{MS : !MonadState (store valType) M}
    `{SB : SubType boolType valType}
    `{SN : SubType natType valType}
    `{PO : plus_op natType natType}
    `{MO : mult_op natType natType}
    `{EO : eq_op natType boolType}
    `{LO : leb_op natType boolType}
    `{NO : neg_op boolType boolType}
    `{AO : and_op boolType boolType}
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

Open Scope com_scope.

Fixpoint shared_ceval 
    {valType boolType natType : Type} 
    {M : Type → Type} 
    `{MM : !Monad M}
    `{MF : !MonadFail M} 
    `{MS : !MonadState (store valType) M}
    `{ME : !MonadExcept M unit} (c : com) 
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
