(** * Maps: Total and Partial Maps *)

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Export Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Import ListNotations.

Definition beq_string x y :=
  if string_dec x y then true else false.

Theorem beq_string_refl : forall s, true = beq_string s s.
Proof. intros s. unfold beq_string. destruct (string_dec s s) as [|Hs].
  - reflexivity.
  - destruct Hs. reflexivity.
Qed.

Theorem beq_string_true_iff : forall x y : string,
  beq_string x y = true <-> x = y.
Proof.
   intros x y.
   unfold beq_string.
   destruct (string_dec x y) as [|Hs].
   - subst. split. reflexivity. reflexivity.
   - split.
     + intros contra. inversion contra.
     + intros H. inversion H. subst. destruct Hs. reflexivity.
Qed.

Theorem beq_string_false_iff : forall x y : string,
  beq_string x y = false
  <-> x <> y.
Proof.
  intros x y. rewrite <- beq_string_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.

Theorem false_beq_string : forall x y : string,
   x <> y -> beq_string x y = false.
Proof.
  intros x y. rewrite beq_string_false_iff.
  intros H. apply H. Qed.

Definition total_map (A:Type) := string -> A.

(** Intuitively, a total map over an element type [A] is just a
    function that can be used to look up [string]s, yielding [A]s. *)

(** The function [t_empty] yields an empty total map, given a default
    element; this map always returns the default element when applied
    to any string. *)

Definition t_empty {A:Type} (v : A) : total_map A :=
  (fun _ => v).

(** More interesting is the [update] function, which (as before) takes
    a map [m], a key [x], and a value [v] and returns a new map that
    takes [x] to [v] and takes every other key to whatever [m] does. *)

Definition t_update {A:Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if beq_string x x' then v else m x'.

(** This definition is a nice example of higher-order programming:
    [t_update] takes a _function_ [m] and yields a new function
    [fun x' => ...] that behaves like the desired map. *)

(** For example, we can build a map taking [string]s to [bool]s, where
    ["foo"] and ["bar"] are mapped to [true] and every other key is
    mapped to [false], like this: *)

Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true)
           "bar" true.

(** Next, let's introduce some new notations to facilitate working
    with maps. *)

(** First, we will use the following notation to create an empty total map
    with a default value. *)
Notation "{ --> d }" := (t_empty d) (at level 0).

(** We then introduce a convenient notation for extending an existing
    map with some bindings. *)

(** (The definition of the notation is a bit ugly, but because the
    notation mechanism of Coq is not very well suited for recursive
    notations, it's the best we can do.) *)

Notation "m '&' { a --> x }" :=
  (t_update m a x) (at level 20).
Notation "m '&' { a --> x ; b --> y }" :=
  (t_update (m & { a --> x }) b y) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z }" :=
  (t_update (m & { a --> x ; b --> y }) c z) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z ; d --> t }" :=
    (t_update (m & { a --> x ; b --> y ; c --> z }) d t) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z ; d --> t ; e --> u }" :=
    (t_update (m & { a --> x ; b --> y ; c --> z ; d --> t }) e u) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v }" :=
    (t_update (m & { a --> x ; b --> y ; c --> z ; d --> t ; e --> u }) f v) (at level 20).

(** The [examplemap] above can now be defined as follows: *)

Definition examplemap' :=
  { --> false } & { "foo" --> true ; "bar" --> true }.

(** This completes the definition of total maps.  Note that we
    don't need to define a [find] operation because it is just
    function application! *)

Example update_example1 : examplemap' "baz" = false.
Proof. reflexivity. Qed.

Example update_example2 : examplemap' "foo" = true.
Proof. reflexivity. Qed.

Example update_example3 : examplemap' "quux" = false.
Proof. reflexivity. Qed.

Example update_example4 : examplemap' "bar" = true.
Proof. reflexivity. Qed.

(** To use maps in later chapters, we'll need several fundamental
    facts about how they behave. *)

(** Even if you don't work the following exercises, make sure
    you thoroughly understand the statements of the lemmas! *)

(** (Some of the proofs require the functional extensionality axiom,
    which is discussed in the [Logic] chapter.) *)

(** **** Exercise: 1 star, optional (t_apply_empty)  *)
(** First, the empty map returns its default element for all keys: *)

Lemma t_apply_empty:  forall (A:Type) (x: string) (v: A), { --> v } x = v.
Proof.
  intros A x v.
  unfold t_empty. reflexivity. Qed.
(** [] *)

(** **** Exercise: 2 stars, optional (t_update_eq)  *)
(** Next, if we update a map [m] at a key [x] with a new value [v]
    and then look up [x] in the map resulting from the [update], we
    get back [v]: *)

Lemma t_update_eq : forall A (m: total_map A) x v,
  (m & {x --> v}) x = v.
Proof.
  intros A m x v.
  unfold t_update. rewrite <- beq_string_refl.
  reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars, optional (t_update_neq)  *)
(** On the other hand, if we update a map [m] at a key [x1] and then
    look up a _different_ key [x2] in the resulting map, we get the
    same result that [m] would have given: *)

Theorem t_update_neq : forall (X:Type) v x1 x2
                         (m : total_map X),
  x1 <> x2 ->
  (m & {x1 --> v}) x2 = m x2.
Proof.
  intros X v x1 x2 m H.
  unfold t_update.
  apply beq_string_false_iff in H. rewrite H. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars, optional (t_update_shadow)  *)
(** If we update a map [m] at a key [x] with a value [v1] and then
    update again with the same key [x] and another value [v2], the
    resulting map behaves the same (gives the same result when applied
    to any key) as the simpler map obtained by performing just
    the second [update] on [m]: *)

Lemma t_update_shadow : forall A (m: total_map A) v1 v2 x,
    m & {x --> v1 ; x --> v2} = m & {x --> v2}.
Proof.
  intros A m v1 v2 x. 
  apply functional_extensionality.
  unfold t_update. 
  intros x'. destruct (beq_string x x'); reflexivity.
Qed.
(** [] *)

(** For the final two lemmas about total maps, it's convenient to use
    the reflection idioms introduced in chapter [IndProp].  We begin
    by proving a fundamental _reflection lemma_ relating the equality
    proposition on [id]s with the boolean function [beq_id]. *)

(** **** Exercise: 2 stars, optional (beq_stringP)  *)
(** Use the proof of [beq_natP] in chapter [IndProp] as a template to
    prove the following: *)

Lemma beq_stringP : forall x y, reflect (x = y) (beq_string x y).
Proof.
  intros x y. apply iff_reflect. rewrite beq_string_true_iff. reflexivity.
Qed.
(** [] *)

(** Now, given [string]s [x1] and [x2], we can use the [destruct (beq_stringP
    x1 x2)] to simultaneously perform case analysis on the result of
    [beq_string x1 x2] and generate hypotheses about the equality (in the
    sense of [=]) of [x1] and [x2]. *)

(** **** Exercise: 2 stars (t_update_same)  *)
(** With the example in chapter [IndProp] as a template, use
    [beq_stringP] to prove the following theorem, which states that if we
    update a map to assign key [x] the same value as it already has in
    [m], then the result is equal to [m]: *)

Theorem t_update_same : forall X x (m : total_map X),
    m & { x --> m x } = m.
Proof.
  intros X x m. apply functional_extensionality. intros y.
  destruct beq_stringP with (x:=x) (y:=y).
  - unfold t_update. rewrite e. rewrite <- beq_string_refl. reflexivity.
  - unfold t_update. apply beq_string_false_iff in n. rewrite n. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 3 stars, recommended (t_update_permute)  *)
(** Use [beq_stringP] to prove one final property of the [update]
    function: If we update a map [m] at two distinct keys, it doesn't
    matter in which order we do the updates. *)

Theorem beq_string_sym : forall (s1 s2 : string),
  beq_string s1 s2 = beq_string s2 s1.
Proof.
  intros s1 s2. destruct (beq_stringP s1 s2).
  - rewrite e. apply beq_string_refl.
  - symmetry. apply beq_string_false_iff. unfold not in *.
    intros H. apply n. rewrite H. reflexivity.
Qed.

Theorem t_update_permute : forall (X:Type) v1 v2 x1 x2
                             (m : total_map X),
  x2 <> x1 ->
  m & { x2 --> v2 ; x1 --> v1 }
  =  m & { x1 --> v1 ; x2 --> v2 }.
Proof.
  intros X v1 v2 x1 x2 m H. apply functional_extensionality.
  intros x.
  destruct (beq_stringP x x1).
  - rewrite e. unfold t_update. rewrite <- beq_string_refl.
    apply beq_string_false_iff in H. rewrite H. reflexivity.
  - unfold t_update. apply beq_string_false_iff in n. 
    rewrite beq_string_sym. rewrite n. reflexivity.
Qed.

(** [] *)

(* ################################################################# *)
(** * Partial maps *)

(** Finally, we define _partial maps_ on top of total maps.  A partial
    map with elements of type [A] is simply a total map with elements
    of type [option A] and default element [None]. *)

Definition partial_map (A:Type) := total_map (option A).

Definition empty {A:Type} : partial_map A :=
  t_empty None.

Definition update {A:Type} (m : partial_map A)
           (x : string) (v : A) :=
  m & { x --> (Some v) }.

(** We introduce a similar notation for partial maps, using double
    curly-brackets.  **)

Notation "m '&' {{ a --> x }}" :=
  (update m a x) (at level 20).
Notation "m '&' {{ a --> x ; b --> y }}" :=
  (update (m & {{ a --> x }}) b y) (at level 20).
Notation "m '&' {{ a --> x ; b --> y ; c --> z }}" :=
  (update (m & {{ a --> x ; b --> y }}) c z) (at level 20).
Notation "m '&' {{ a --> x ; b --> y ; c --> z ; d --> t }}" :=
    (update (m & {{ a --> x ; b --> y ; c --> z }}) d t) (at level 20).
Notation "m '&' {{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u }}" :=
    (update (m & {{ a --> x ; b --> y ; c --> z ; d --> t }}) e u) (at level 20).
Notation "m '&' {{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v }}" :=
    (update (m & {{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u }}) f v) (at level 20).

(** We now straightforwardly lift all of the basic lemmas about total
    maps to partial maps.  *)

Lemma apply_empty : forall (A: Type) (x: string),  @empty A x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.

Lemma update_eq : forall A (m: partial_map A) x v,
    (m & {{ x --> v }}) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

Theorem update_neq : forall (X:Type) v x1 x2
                       (m : partial_map X),
  x2 <> x1 ->
  (m & {{ x2 --> v }}) x1 = m x1.
Proof.
  intros X v x1 x2 m H.
  unfold update. rewrite t_update_neq. reflexivity.
  apply H. Qed.

Lemma update_shadow : forall A (m: partial_map A) v1 v2 x,
    m & {{ x --> v1 ; x --> v2 }} = m & {{x --> v2}}.
Proof.
  intros A m v1 v2 x1. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : forall X v x (m : partial_map X),
  m x = Some v ->
  m & {{x --> v}} = m.
Proof.
  intros X v x m H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall (X:Type) v1 v2 x1 x2
                                (m : partial_map X),
  x2 <> x1 ->
  m & {{x2 --> v2 ; x1 --> v1}}
  = m & {{x1 --> v1 ; x2 --> v2}}.
Proof.
  intros X v1 v2 x1 x2 m. unfold update.
  apply t_update_permute.
Qed.


