(** EqFact.v *)

From mathcomp Require Import all_ssreflect.
Require Import Coq.Unicode.Utf8_core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem pred_replace : 
    forall (A B : Type) (P : Type -> Prop), A = B -> (P A <-> P B).
Proof. move => A B P Heq. by case Heq. Qed.

Definition transport (A B : Type) : A = B -> A -> B.
Proof. move => H a. by rewrite -H. Defined.

        