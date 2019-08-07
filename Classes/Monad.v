
Class Monad (M : Type -> Type) : Type :=
{
  returnM : forall A, A -> M A;
  bindM : forall A B, M A  -> (A -> M B) -> M B;
}.
Arguments Build_Monad {_ _ _}.
Arguments returnM {_ _ _}.
Arguments bindM {_ _ _ _}.

Notation "x '<<' y ; z" := (bindM y (fun x => z))
  (at level 20, y at level 100, z at level 200, only parsing).

Notation "x ;; z" := (bindM x (fun _ => z))
    (at level 100, z at level 200, only parsing, right associativity).
