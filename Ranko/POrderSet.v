(** * POrderSet.v : Library for partial orders with sets. *)


From Ranko Require Import TerminalDogma.premises 
                          TerminalDogma.Extensionality.


From Coq Require Import Relations Classical.

From Ranko Require Export NemSet POrder.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.




(*#########################################################*)
(** ** power set as poset, with subset order*)

Module SubsetOrder.

(** inclusion order (subset) *)
Definition poset_mixin (T : Type): Poset.class_of 𝒫(T) :=
    posetMixin {|
      ord_refl := subset_refl;
      ord_trans := subset_trans;
      ord_antisym := subset_asymm;
    |}.

Canonical poset_type (T : Type) := Poset 𝒫(T) (poset_mixin T).


Definition cpo_mixin (T : Type) : CPO.class_of (poset_type T).
Proof.
    refine (@cpoMixin _ (@big_union T) _).
    move => A. apply /lubP. split.
    by apply bigU_ub. by apply bigU_lub.
Defined.

Canonical cpo_type (T : Type) := CPO (poset_type T) (cpo_mixin T).


(** Import this module to use the subset poset canonical structures. *)
Module CanonicalStruct.

Canonical poset_type.
Canonical cpo_type.

End CanonicalStruct.

End SubsetOrder.



(*#########################################################*)
(** ** power set as poset, with supset order*)
Module SupsetOrder.

(** inverse inclusion order (supset) *)
Definition poset_mixin (T : Type): Poset.class_of 𝒫(T) :=
    posetMixin {|
      ord_refl := supset_refl;
      ord_trans := supset_trans;
      ord_antisym := supset_asymm;
    |}.

Canonical poset_type (T : Type) := Poset 𝒫(T) (poset_mixin T).

Definition cpo_mixin (T : Type) : CPO.class_of (poset_type T).
Proof.
    refine (@cpoMixin _ (@big_itsct T) _).
    move => A. apply /lubP. split. 
    by apply bigI_lb. by apply bigI_glb.
Defined.

Canonical cpo_type (T : Type) := CPO (poset_type T) (cpo_mixin T).


(** Import this module to use the supset poset canonical structures. *)
Module CanonicalStruct.

Canonical poset_type.
Canonical cpo_type.

End CanonicalStruct.

End SupsetOrder.



(*#########################################################*)
(** ** nonempty set type as poset, with supset order*)
Module NemSetOrder.

(** inclusion order (supset) *)
Definition poset_mixin (T : iType): Poset.class_of 𝒫(T)₊ :=
    posetMixin {|
        ord_refl := nem_supset_refl;
        ord_trans := nem_supset_trans;
        ord_antisym := nem_supset_asymm;
    |}.

Canonical poset_type (T : iType) := Poset 𝒫(T)₊ (poset_mixin T).

(** This is does not always hold. 
    Consider a sequence of shrinking real intervals. 
    Maybe we need the property of Cauchy closure.
*)
Definition nem_big_itsct_chain (T : iType) (c : chain (poset_type T)) : 𝒫(T)₊.
Proof.
    refine (Nemset (⋂₊ c) _).
    rewrite /NemSet.mixin_of /nem_big_itsct /nemset2set.
    destruct c => //=. rewrite /Chain.mixin_of in m.
    case (em_classic set).

    (** if [set] is empty *)
    move => H. rewrite -H. 
    have temp : { _ | set = set } = set_uni (T).
    { apply seteqP => //=. }
    rewrite {}temp. rewrite union_uni. by apply uni_neq_em.

    (** if [set] is nonempty *)
    move => H.
    have temp : { _ | set = ∅ } = set_em (T).
    { apply seteqP => //=. }
    rewrite {}temp. rewrite union_em.

    (** the main proof *)
    rewrite /big_itsct //=. rewrite nonemptyP in H.
    destruct H as [X HXin].
Abort.


(** Import this module to use the nonempty poset canonical structures. *)
Module CanonicalStruct.

Canonical poset_type.

End CanonicalStruct.

End NemSetOrder.