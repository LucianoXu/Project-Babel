Require Import POrder POrderSet TerminalDogma.premises
                                TerminalDogma.Extensionality.

Require Import SetFacility 
                POrderFacility 
                POrderBool.

Require Import Ranko.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.




(** The type of state. *)
Axiom Stt : Type.


(** >>> *)
Import LeibnizEqOrder.CanonicalStruct.

Definition Sta := [poset of Stt].



(** >>> *)
Import FunPointwiseOrder.CanonicalStruct.
Import BoolOrder.CanonicalStruct.

Definition Asn := [clattice of [Sta ↦ᵐ bool]].



(** some wrapping definitions *)
Definition asn_impl_comp (P Q : Asn) : Sta -> bool := fun s => (P s ==> Q s).
Notation "P ⇒ Q" := (asn_impl_comp P Q) (at level 40).

Definition uni_quantification (P : Asn) : Prop := forall s, P s.
Notation "⌈ P ⌉" := (uni_quantification P).


#[local] Hint Unfold asn_impl_comp : magic_book.
#[local] Hint Unfold uni_quantification : magic_book.

Lemma Lemma_3_1 (P Q : Asn) :
    P ⊑ Q <-> ⌈ P ⇒ Q ⌉.
Proof.
    ranko.

    apply /implyP. by apply (H s).

    by move : (implyP (H x) H0).
Qed.


