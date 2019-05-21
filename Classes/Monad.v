
Class Monad (M : Type -> Type) : Type :=
{
  returnM : forall A, A -> M A;
  bind : forall A B, M A  -> (A -> M B) -> M B;
}.
Arguments Build_Monad {_ _ _}.
Arguments returnM {_ _ _}.
Arguments bind {_ _ _ _}.

Notation "x '<<' y ; z" := (bind y (fun x => z))
  (at level 20, y at level 100, z at level 200, only parsing).

Notation "x ;; z" := (bind x (fun _ => z))
    (at level 100, z at level 200, only parsing, right associativity).
