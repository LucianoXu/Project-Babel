(** * Map.v : mappings
    From Software Foundation Volumn 1.
    *)
From mathcomp Require Export all_ssreflect.
Require Export Coq.Unicode.Utf8_core.

From Babel Require Import ExtraDogma.Extensionality.

From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Lists.List.
Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope Maps_scope.
Open Scope Maps_scope.
Delimit Scope Maps_scope with MAP.


(* ################################################################# *)
(** * Identifiers *)

(** To compare strings, we use the function [eqb] from the [String]
    module in the standard library. *)

(*
Check String.eqb_refl :
    forall x : string, (x =? x)%string = true.

(** We will often use a few basic properties of string equality... *)
Check String.eqb_eq :
    forall n m : string, (n =? m)%string = true <-> n = m.
Check String.eqb_neq :
    forall n m : string, (n =? m)%string = false <-> n <> m.
Check String.eqb_spec :
    forall x y : string, reflect (x = y) (String.eqb x y).
*)

(* ################################################################# *)
(** * Total Maps *)

(** We build up to partial maps in two steps.  First, we define a type
    of _total maps_ that return a default value when we look up a key
    that is not present in the map. *)

Definition total_map (A : Type) := string -> A.

(** Intuitively, a total map over an element type [A] is just a
    function that can be used to look up [string]s, yielding [A]s. *)

(** The function [t_empty] yields an empty total map, given a default
    element; this map always returns the default element when applied
    to any string. *)

Definition t_empty {A : Type} (v : A) : total_map A :=
    (fun _ => v).

(** More interesting is the map-updating function, which (as always)
    takes a map [m], a key [x], and a value [v] and returns a new map
    that takes [x] to [v] and takes every other key to whatever [m]
    does.  The novelty here is that we achieve this effect by wrapping
    a new function around the old one. *)

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
    fun x' => if String.eqb x x' then v else m x'.

(** This definition is a nice example of higher-order programming:
    [t_update] takes a _function_ [m] and yields a new function
    [fun x' => ...] that behaves like the desired map. *)

(** Next, let's introduce some notations to facilitate working with
    maps. *)

(** First, we use the following notation to represent an empty total
    map with a default value. *)
Notation "'_' '!->' v" := (t_empty v)
    (at level 100, right associativity) : Maps_scope.

(** We next introduce a convenient notation for extending an existing
    map with a new binding. *)
Notation "x '!->' v ';' m" := (t_update m x v)
    (at level 100, v at next level, right associativity) : Maps_scope.


(** This completes the definition of total maps. *)


(** When we use maps in later chapters, we'll need several fundamental
    facts about how they behave. *)



(** First, the empty map returns its default element for all keys: *)

Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
    (_ !-> v) x = v.
Proof.
    intros. unfold t_empty. reflexivity.
Qed.
(** [] *)

(** Next, if we update a map [m] at a key [x] with a new value [v]
    and then look up [x] in the map resulting from the [update], we
    get back [v]: *)

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
    (x !-> v ; m) x = v.
Proof.
    intros. unfold t_update. destruct (eqb_spec x x).
    - reflexivity.
    - destruct n. reflexivity.
Qed.  
(** [] *)

(** On the other hand, if we update a map [m] at a key [x1] and then
    look up a _different_ key [x2] in the resulting map, we get the
    same result that [m] would have given: *)

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
    x1 <> x2 ->
    (x1 !-> v ; m) x2 = m x2.
Proof.
    intros. unfold t_update. rewrite <- eqb_neq in H. rewrite H. 
    reflexivity.
Qed.
(** [] *)

(** If we update a map [m] at a key [x] with a value [v1] and then
    update again with the same key [x] and another value [v2], the
    resulting map behaves the same (gives the same result when applied
    to any key) as the simpler map obtained by performing just
    the second [update] on [m]: *)


Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
    (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
    intros. unfold t_update. apply functional_extensionality. intros.
    destruct (x =? x0)%string.
    - reflexivity.
    - reflexivity.
Qed. 
(** [] *)

(** Given [string]s [x1] and [x2], we can use the tactic
    [destruct (eqb_spec x1 x2)] to simultaneously perform case
    analysis on the result of [String.eqb x1 x2] and generate
    hypotheses about the equality (in the sense of [=]) of [x1] and
    [x2].  With the example in chapter [IndProp] as a template,
    use [String.eqb_spec] to prove the following theorem, which states
    that if we update a map to assign key [x] the same value as it
    already has in [m], then the result is equal to [m]: *)

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
    (x !-> m x ; m) = m.
Proof.
    intros. unfold t_update. apply functional_extensionality. intros.
    destruct (eqb_spec x x0).
    - rewrite e. reflexivity.
    - reflexivity.
Qed.  
(** [] *)

(** Similarly, use [String.eqb_spec] to prove one final property of
    the [update] function: If we update a map [m] at two distinct
    keys, it doesn't matter in which order we do the updates. *)

Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                    v1 v2 x1 x2,
    x2 <> x1 ->
    (x1 !-> v1 ; x2 !-> v2 ; m)
    =
    (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
    unfold t_update. intros. apply functional_extensionality.
    intros. destruct (eqb_spec x1 x).
    - destruct (eqb_spec x2 x).
    -- rewrite e in H. rewrite e0 in H. destruct H. reflexivity.
    -- reflexivity.
    - destruct (eqb_spec x2 x).
    -- reflexivity.
    -- reflexivity.
Qed.   
(** [] *)



(* ################################################################# *)
(** * Partial maps *)

(** Lastly, we define _partial maps_ on top of total maps.  A partial
    map with elements of type [A] is simply a total map with elements
    of type [option A] and default element [None]. *)

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A :=
    t_empty None.

Definition update {A : Type} (m : partial_map A)
            (x : string) (v : A) :=
    (x !-> Some v ; m).

(** We introduce a similar notation for partial maps: *)
Notation "x '?->' v ';' m" := (update m x v)
    (at level 100, v at next level, right associativity) : Maps_scope.

(** We can also hide the last case when it is empty. *)
Notation "x '?->' v" := (update empty x v)
    (at level 100) : Maps_scope.



(** We now straightforwardly lift all of the basic lemmas about total
    maps to partial maps.  *)

Lemma apply_empty : forall (A : Type) (x : string),
    @empty A x = None.
Proof.
    intros. unfold empty. rewrite t_apply_empty.
    reflexivity.
Qed.

Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
    (x ?-> v ; m) x = Some v.
Proof.
    intros. unfold update. rewrite t_update_eq.
    reflexivity.
Qed.

Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
    x2 <> x1 ->
    (x2 ?-> v ; m) x1 = m x1.
Proof.
    intros A m x1 x2 v H.
    unfold update. rewrite t_update_neq. reflexivity.
    apply H. 
Qed.

Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
    (x ?-> v2 ; x ?-> v1 ; m) = (x ?-> v2 ; m).
Proof.
    intros A m x v1 v2. unfold update. rewrite t_update_shadow.
    reflexivity.
Qed.

Theorem update_same : forall (A : Type) (m : partial_map A) x v,
    m x = Some v ->
    (x ?-> v ; m) = m.
Proof.
    intros A m x v H. unfold update. rewrite <- H.
    apply t_update_same.
Qed.

Theorem update_permute : forall (A : Type) (m : partial_map A)
                                x1 x2 v1 v2,
    x2 <> x1 ->
    (x1 ?-> v1 ; x2 ?-> v2 ; m) = (x2 ?-> v2 ; x1 ?-> v1 ; m).
Proof.
    intros A m x1 x2 v1 v2. unfold update.
    apply t_update_permute.
Qed.

(** One last thing: For partial maps, it's convenient to introduce a
    notion of map inclusion, stating that all the entries in one map
    are also present in another: *)

Definition includedin {A : Type} (m m' : partial_map A) :=
    forall x v, m x = Some v -> m' x = Some v.

(** We can then show that map update preserves map inclusion -- that is: *)

Lemma includedin_update : forall (A : Type) (m m' : partial_map A)
                                    (x : string) (vx : A),
    includedin m m' ->
    includedin (x ?-> vx ; m) (x ?-> vx ; m').
Proof.
    unfold includedin.
    intros A m m' x vx H.
    intros y vy.
    destruct (eqb_spec x y) as [Hxy | Hxy].
    - rewrite Hxy.
    rewrite update_eq. rewrite update_eq. intro H1. apply H1.
    - rewrite update_neq. rewrite update_neq.
    + apply H.
    + apply Hxy.
    + apply Hxy.
Qed.

(** This property is quite useful for reasoning about languages with
    variable binding -- e.g., the Simply Typed Lambda Calculus, which
    we will see in _Programming Language Foundations_, where maps are
    used to keep track of which program variables are defined in a
    given scope. *)
