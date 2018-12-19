Inductive parity : Type :=
  | par_even : parity
  | par_odd : parity
  | par_top : parity
  | par_bottom : parity.

Inductive cexp : Type :=
  | CNum : nat -> cexp
  | CVar : cexp
  | CPlus : cexp -> cexp -> cexp
  | CMult : cexp -> cexp -> cexp
.


(* Find some way to define eval and abstract_eval on the same 
   set of commands; but how then to incorporate that they will
   have to work with different values (x and x^)?

   Or have separate expressions like currently implemented, but
   how to estabilish "equivelance" between APlus and CPlus? *)

Fixpoint eval (e : cexp) (x : nat) : nat := 
  match e with
  | CNum n => n
  | CVar => x
  | CPlus e1 e2 => eval e1 x + eval e2 x
  | CMult e1 e2 => eval e1 x * eval e2 x
  end.

Fixpoint extract (n : nat) : parity :=
  match n with 
  | 0 => par_even
  | S 0 => par_odd
  | S (S n) => extract n
  end.

Fixpoint abstract_eval (e : cexp) (p : parity) : parity :=
  match e with 
  | CNum n => extract n
  | CVar => p
  | CPlus p1 p2 => match (abstract_eval p1 p) with
                   | par_even => abstract_eval p2 p
                   | par_odd => match (abstract_eval p2 p) with
                                | par_even => par_odd
                                | par_odd => par_even
                                | par_top => par_top
                                | par_bottom => par_bottom
                                end
                   | par_top => par_top
                   | par_bottom => par_bottom
                   end
  | CMult p1 p2 => match (abstract_eval p1 p) with
                   | par_even => abstract_eval p2 p
                   | par_odd => match (abstract_eval p2 p) with
                                | par_even =>  par_even
                                | par_odd => par_odd
                                | par_top => par_top
                                | par_bottom => par_bottom
                                end
                   | par_top => par_top
                   | par_bottom => par_bottom
                   end
  end.

(* Taken from the standard library *)
Inductive even : nat -> Prop :=
  | even_O : even 0
  | even_S : forall n, odd n -> even (S n)
with odd : nat -> Prop :=
    odd_S : forall n, even n -> odd (S n).

Inductive isNumber : nat -> Prop :=
  | nIsNumber : forall n, isNumber n.

Inductive noNumber : nat -> Prop :=.

Definition gamma (p : parity) : (nat -> Prop) :=
  match p with
  | par_even => even
  | par_odd => odd
  | par_top => isNumber
  | par_bottom => noNumber
  end.

Inductive gammaR : parity -> (nat -> Prop) -> Prop :=
  | peven : gammaR par_even even
  | podd  : gammaR par_odd odd
  | ptop  : gammaR par_top isNumber
  | pbot  : gammaR par_bottom noNumber.

Inductive abstract_leq : parity -> parity -> Prop :=
  | bottom_leq : forall p, abstract_leq par_bottom p
  | top_leq : forall p, abstract_leq p par_top
  | even_odd : abstract_leq par_even par_odd
  | odd_even : abstract_leq par_odd par_even.

Theorem abstract_eval_sound : forall e x p,
  (gamma p) x ->
  (gamma (abstract_eval e p)) (eval e x).
Proof.
  intros.
  unfold eval in Heval; subst.
  destruct p; simpl.
  - (* n is even *)
    simpl in Hin. constructor. assumption.
  - (* n is odd *)
    simpl in Hin. 
    apply even_S. assumption.
  - (* top *)
    constructor.
  - inversion Hin.
Qed.
(* proof the equivalance of the galois connection diagram *)
(* Peval o gamma \subset gamma o abstract_eval *)
(* etc... *)

(* refactor the above code (and finish the proofs) *)
(* implement multiple variables, with store (nat -> nat) *)
(* Add a statements SKIP, sequencing, if statements, assignment *)

