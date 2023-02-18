(** * BoolBasic.v *)


From Babel Require Import TerminalDogma.

From Coq Require Export Bool.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Lemma true_eq_false_False : true = false <-> False.
Proof. by []. Qed.