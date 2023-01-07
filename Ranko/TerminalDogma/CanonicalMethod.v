(** CanonicalMethod.v *)

From mathcomp Require Import all_ssreflect.
Require Import Coq.Unicode.Utf8_core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** The designing for finding Canonical structure easily. *)
Module Export infrastructure.

Require Export String.

Declare Scope CanonicalMethod_scope.
Global Open Scope CanonicalMethod_scope.

Arguments phantom {T} _.

Definition unify {T1 T2} (t1 : T1) (t2 : T2) (s : option string) :=
    phantom t1 -> phantom t2.

Definition id {T} {t : T} (x : phantom t) := x.

Notation "[find v | t1 ~ t2 ] rest" :=
    (fun v (_ : unify t1 t2 None) => rest) (at level 10) 
    : CanonicalMethod_scope.

Notation "[find v | t1 ~ t2 | msg ] rest" :=
    (fun v (_ : unify t1 t2 (Some msg)) => rest) (at level 11)
    : CanonicalMethod_scope.

Notation "’Error: t msg" := (unify _ t (Some msg)) (at level 10, only printing)
    : CanonicalMethod_scope.

End infrastructure.