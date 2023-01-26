(** * POrderSet.v : Library for partial orders with sets. *)


From Ranko Require Import TerminalDogma.premises 
                          TerminalDogma.Extensionality.


From Coq Require Import Relations Classical.
From Ranko Require Export NaiveSet POrder.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.




(*#########################################################*)
(** ** power set as poset *)

Module PowersetPoset.

(** inclusion order (subset) *)
Definition poset_mixin (T : Type): Poset.class_of 𝒫(T) :=
    posetMixin {|
      ord_refl := subset_refl;
      ord_trans := subset_trans;
      ord_antisym := subset_asymm;
    |}.

Definition poset_type (T : Type) := Poset 𝒫(T) (poset_mixin T).


Definition cpo_mixin (T : Type) : CPO.class_of (poset_type T).
Proof.
    refine (@cpoMixin (poset_type T) (@big_union T) _).
    move => A. apply /lubP. split.
    by apply bigU_ub. by apply bigU_lub.
Defined.

Definition cpo_type (T : Type) := CPO (poset_type T) (cpo_mixin T).

(** inverse inclusion order (supset) *)
Definition poset_inv_mixin (T : Type): Poset.class_of 𝒫(T) :=
    posetMixin {|
      ord_refl := supset_refl;
      ord_trans := supset_trans;
      ord_antisym := supset_asymm;
    |}.

Definition poset_inv_type (T : Type) := Poset 𝒫(T) (poset_inv_mixin T).

Definition cpo_inv_mixin (T : Type) : CPO.class_of (poset_inv_type T).
Proof.
    refine (@cpoMixin (poset_inv_type T) (@big_itsct T) _).
    move => A. apply /lubP. split. 
    by apply bigI_lb. by apply bigI_glb.
Defined.

Definition cpo_inv_type (T : Type) := CPO (poset_inv_type T) (cpo_inv_mixin T).
  

(** Import this module to use the subset poset canonical structures. *)
Module SubsetCanonical.

Canonical PowersetPoset.poset_type.
Canonical PowersetPoset.cpo_type.

End SubsetCanonical.

(** Import this module to use the supset poset canonical structures. *)
Module SupsetCanonical.

Canonical PowersetPoset.poset_inv_type.
Canonical PowersetPoset.cpo_inv_type.

End SupsetCanonical.


End PowersetPoset.