(** ProofFacility.v *)

From mathcomp Require Import all_ssreflect.
Require Import Coq.Unicode.Utf8_core.

From Ranko Require Import TerminalDogma.TypeFacility.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Note that A must be a inhabited type. *)
Lemma forall_to_exists (A : iType) (P : A -> Prop):
    (forall x : A, P x) -> (exists x : A, P x).
Proof. move => H. exists [witness of A]. by apply H. Qed.