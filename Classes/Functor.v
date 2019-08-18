Class Functor (F : Type -> Type) (A B : Type) : Type := {
  fmap : (A -> B) -> F A -> F B;
}.
