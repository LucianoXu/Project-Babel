(** CanonicalInfrastructure.v *)

From mathcomp Require Import all_ssreflect.
Require Import Coq.Unicode.Utf8_core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** The infrastructure for finding Canonical structure easily. *)

Require Export String.

Declare Scope TerminalDogma_scope.
Global Open Scope TerminalDogma_scope.

(** Combined with [Coq.ssr.ssreflect.phantom] *)
Arguments phantom {T}.

Definition phantom_unify {T1 T2} (t1 : T1) (t2 : T2) 
    (s : option string) :=
    phantom t1 -> phantom t2.

Definition phantom_id {T} {t : T} (x : phantom t) := x.


Notation "[ 'find' v | t1 ~ t2 ] rest" :=
    (fun v (_ : phantom_unify t1 t2 None) => rest) 
    (at level 0, format "[ 'find'  v  |  t1  ~  t2 ]  rest") 
    : TerminalDogma_scope.

Notation "[ 'find' v | t1 ~ t2 | msg ] rest" :=
    (fun v (_ : phantom_unify t1 t2 (Some msg)) => rest) 
    (at level 0, format "[ 'find'  v  |  t1  ~  t2  |  msg ]  rest") 
    : TerminalDogma_scope.

Notation "[ 'get' v | t1 ~ t2 ]" :=
    (([find v | t1 ~ t2 ] v) _ phantom_id)
    (format "[ 'get'  v  |  t1  ~  t2 ]") 
    : TerminalDogma_scope.

Notation "’Error: t msg" := (phantom_unify _ t (Some msg)) 
    (at level 10, only printing) 
    : TerminalDogma_scope.

Notation "’Error: t 'in' 'canonical' 'infrastructure' " := 
    (phantom_unify _ t None) 
    (at level 10, only printing) 
    : TerminalDogma_scope.


(** Note for canonical structures: 
    1. For canonical structures of the same type, only the first definition
        will be used. *)