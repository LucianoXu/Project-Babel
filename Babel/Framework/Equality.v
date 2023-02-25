(** Equality.v *)

From Babel Require Import TerminalDogma.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Lemma refl_iff_True (T : Type) (a : T) :
    a = a <-> True.
Proof. by []. Qed.
