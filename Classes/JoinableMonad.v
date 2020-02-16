Require Import Classes.Monad.
Require Import Classes.PreorderedSet.
Require Import Classes.Joinable.

Class JoinableMonad (M : Type → Type) 
  `{Monad M} 
  {M_preorder : ∀ T, PreorderedSet (M T)}
  {M_joinable : ∀ T, Joinable (M T)}
    : Type :=
{
  join_return : ∀ {A : Type} `{Joinable A} (x y : A), 
    join_op (returnM x) (returnM y) = returnM (join_op x y);
}.
