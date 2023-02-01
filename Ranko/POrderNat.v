(** * POrderNat.v : Partial order of nat *)


From Ranko Require Import TerminalDogma.premises 
                          TerminalDogma.Extensionality.


From Coq Require Import Relations Classical Arith.

From Ranko Require Export NaiveSet POrder.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Module NatLePoset.

Lemma poset_mixin : Poset.class_of nat.
Proof.
    refine (@Poset.Mixin _ le _).
    constructor.
    move => x. by apply Nat.le_refl.
    move => x y z. by apply Nat.le_trans.
    move => x y. by apply Nat.le_antisymm.
Defined.

Canonical poset_type := Poset nat poset_mixin.

Lemma nat_subset_chainMixin (A : 𝒫(nat)) :
    Chain.class_of A.
Proof.
    rewrite /Chain.mixin_of => x Hx y Hy //=.
    by apply Nat.le_ge_cases.
Defined.

(** every subset of nat is a chain *)
Canonical nat_subset_chain (A : 𝒫(nat)) := Chain _ (@nat_subset_chainMixin A).


Module CanonicalStruct.

Canonical poset_type.
Canonical nat_subset_chain.

End CanonicalStruct.

End NatLePoset.
