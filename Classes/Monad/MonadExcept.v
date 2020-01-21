Require Export Base.
Require Import Classes.Applicative.
Require Import Classes.Monad.
Require Import Classes.Monad.MonadFail.

Implicit Type M : Type → Type.
Implicit Type A : Type.

Class MonadExcept M `{MonadFail M} := {
  catch : forall {A}, M A -> M A -> M A;
  catch_left : forall {A} (x : M A), catch fail x = x;
  catch_right : forall {A} (x : M A), catch x fail = x;
  catch_assoc : ∀ {A} (x y z: M A),
    catch x (catch y z) = catch (catch x y) z;
  catch_pure : ∀ {A} (x : M A) (a : A),
    catch (pure a) x = pure a;
}.
Arguments catch : simpl never.

Hint Rewrite @catch_left @catch_right @catch_pure : soundness.
