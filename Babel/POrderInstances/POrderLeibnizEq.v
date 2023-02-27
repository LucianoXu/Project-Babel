(** * POrderLeibnizEq.v : Library for the partial order of Leibniz equality. *)


From Babel Require Import TerminalDogma 
                          ExtraDogma.Extensionality.


From Coq Require Import Relations Classical.

From Babel Require Export POrder.

From Babel Require Import Ranko.POrderCharacter.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module LeibnizEqOrder.
Section OrderDef.


Definition poset_mixin (T : Type): Poset.mixin_of T.
Proof.
    refine (@Poset.Mixin T eq _). constructor => //=.
    rewrite /transitive.
    apply eq_trans.
Defined.

Canonical poset_type (T : Type) := Poset T (poset_mixin T).


(** Any function with LeibnizEq order as input is monotonic. *)
Definition fun_monotonicMixin {T : Type} (P : poset) (f : T -> P) : 
    MonotonicFun.mixin_of f.
Proof. porder_level. Qed.

Canonical fun_monotonicType {T : Type} (P : poset) (f : T -> P) :=
    MonotonicFun f (fun_monotonicMixin f).

End OrderDef.

Module CanonicalStruct.

Canonical poset_type.

End CanonicalStruct.

End LeibnizEqOrder.


Canonical LeibnizEqOrder.fun_monotonicType.
