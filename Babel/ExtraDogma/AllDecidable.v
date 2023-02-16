(** AllDecidable.v : assume that all propositions are decidable.*)

From Babel Require Import TerminalDogma.

From Coq Require Export Decidable.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** Assume we have an oracle which tells us whether the proposition is provable
    or not.
    
    Question: Does this axiom violates Godel's incompleteness theorem? *)

Axiom decide_oracle : Prop -> bool.

Axiom decide_oracleP : forall P, reflect P (decide_oracle P).

Lemma all_decidable : forall P : Prop, decidable P.
Proof. rewrite /decidable => P.
    case E: (decide_oracle P).
    left. by apply /decide_oracleP.
    right. destruct (decide_oracleP P) => //=.
Qed.

Lemma decide_oracle_true (P : Prop) :

    decide_oracle P = true <-> P.

Proof. split.
    move => H. by apply /decide_oracleP.
    by move => /decide_oracleP H.
Qed.

Lemma decide_oracle_false (P : Prop) :

    decide_oracle P = false <-> ~ P.

Proof. split.
    by move => /decide_oracleP H.
    move => H. by apply /decide_oracleP.
Qed.