(** PropCLattice.v : the complete lattice of propositions. 
    Note : PropExtensionality is needed.
*)

From Babel Require Import TerminalDogma
                            POrder.
From Coq Require Import PropExtensionality.

From Babel.Ranko Require Import POrderCharacter.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module PropImplyOrder.

Lemma prop_imply_refl : forall P : Prop, P -> P.
Proof. by []. Qed.

Lemma prop_imply_trans : forall P Q R : Prop, (P -> Q) -> (Q -> R) -> (P -> R).
Proof. move => P Q R HPQ HQR HP. by apply /HQR /HPQ. Qed.

Lemma prop_imply_antisym : forall P Q : Prop, (P -> Q) -> (Q -> P) -> P = Q.
Proof. move => P Q HPQ HQP. apply propositional_extensionality. by split. Qed.

Definition poset_mixin : Poset.mixin_of Prop :=
    Poset.Mixin {|
        ord_refl := prop_imply_refl;
        ord_trans := prop_imply_trans;
        ord_antisym := prop_imply_antisym;
    |}.

Canonical poset_type := Poset Prop poset_mixin.


(** Directly construction of complete lattice. *)
Definition clattice_essence : CLattice.essence_of Prop.
Proof.
    constructor.
    refine (@CLattice.JoinEssence _ 
                (fun A : 𝒫(Prop) => exists' P ∈ A, P) _) => A.
    apply lubP; split; porder_level.
    refine (@CLattice.MeetEssence _ 
                (fun A : 𝒫(Prop) => forall' P ∈ A, P) _) => A.
    apply glbP; split; porder_level.
Defined.


Definition AUX_clattice_type := CLattice Prop 
            (CLattice.essence_to_mixin clattice_essence).


Definition lattice_mixin : Lattice.mixin_of (Poset.class Prop) :=
    Lattice.class [lattice of AUX_clattice_type].

Canonical lattice_type := Lattice Prop lattice_mixin.

Definition clattice_mixin : CLattice.mixin_of (Lattice.class Prop) :=
    CLattice.class [clattice of AUX_clattice_type].

Canonical clattice_type := CLattice Prop clattice_mixin.

Canonical cpo_type : cpo := CPO Prop (CPO.class [cpo of [clattice of Prop]]).


(** Import this module to use the subset poset canonical structures. *)
Module CanonicalStruct.

Canonical poset_type.
Canonical lattice_type.
Canonical cpo_type.
Canonical clattice_type.

End CanonicalStruct.

End PropImplyOrder.
