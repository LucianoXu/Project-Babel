(** * LogicBasic.v*)


From Babel Require Import TerminalDogma.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma iff_True_R (P : Prop) :
    (P <-> True) <-> P.
Proof. split. by move ->. by move => HP; split. Qed.

Lemma iff_True_L (P : Prop) :
    (True <-> P) <-> P.
Proof. split. 
    move => H. symmetry in H. by rewrite iff_True_R in H. 
    by [].
Qed.