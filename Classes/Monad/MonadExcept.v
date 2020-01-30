Require Export Base.
Require Import Classes.Monad.
Require Import Classes.Monad.MonadFail.

Implicit Type M : Type → Type.
Implicit Type A : Type.

Class MonadExcept M `{M_fail : MonadFail M} A := {
  catch : M A -> M A -> M A;
  catch_left : ∀ (x : M A), catch fail x = x;
  catch_right : ∀ (x : M A), catch x fail = x;
  catch_assoc : ∀ (x y z: M A),
    catch x (catch y z) = catch (catch x y) z;
  catch_return : ∀ (x : M A) (a : A),
    catch (returnM a) x = returnM a;
}.
Arguments catch : simpl never.
Hint Rewrite @catch_left @catch_right @catch_return : soundness.
