(** EpsilonDescription.v : Hilbert's epsilon operator *)

From Babel Require Import TerminalDogma.

From Coq Require Export Epsilon.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Definition epsilon_sigma (T : iType) (P : T -> Prop) := 
    epsilon_statement P (iType_inhabited _).

Definition epsilon_term (T : iType) (P : T -> Prop) :=
    proj1_sig (epsilon_sigma P).

Notation ε := epsilon_term.

Definition epsilon_spec (T : iType) (P : T -> Prop) :=
    proj2_sig (epsilon_sigma P).


Lemma epsilon_PeP (T : iType) (P : T -> Prop) : 
    (exists x, P x) -> P (ε(P)).
Proof. by apply epsilon_spec. Qed.
