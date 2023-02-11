(** IsomorphicExtensioniality.v *)
(*
From Babel Require Import TerminalDogma.premises.
From Babel Require Import TerminalDogma.Isomorphism.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Axiom: isomorphic structures are the same. *)
Axiom isomorphic_extensionality : IsomorphicExtensionality.


(** Open Question : Is isomorphic extensionality consistent with Coq and other
    logic assumptions? (I believe the answer is Yes.) *)

Definition transport_iso (A B : Type) : A ≅ B -> A -> B.
Proof. move => H a. apply isomorphic_extensionality in H. by exact ([a by H]).
Qed.
*)
        