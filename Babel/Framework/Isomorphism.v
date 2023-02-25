(** Isomorphism.v *)

From Babel Require Import TerminalDogma.
From Coq Require Import Relations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope Iso_scope.
Global Open Scope Iso_scope.

(** A and B are isomorphic types, if there exists a bijection between A and B *)
Definition isomorphic (A B : Type) := bijection A B.
Notation " A '≅' B " := (isomorphic A B) (at level 25) : Iso_scope.

(*
Lemma isomorphic_refl : reflexive _ isomorphic.
Proof. rewrite /reflexive => X.
    exists ssrfun.id. econstructor. by apply id_bijective. 
Qed.

Lemma isomorphic_symm : Relation_Definitions.symmetric _ isomorphic.
Proof. rewrite /Relation_Definitions.symmetric.
    move => X Y [f Hbij]. have [g Hg] := (bij_has_inv Hbij).
        by exists g; apply g.
Qed.

Lemma isomorphic_trans : Relation_Definitions.transitive _ isomorphic.
Proof. rewrite /Relation_Definitions.transitive => X Y Z [f Hf] [g Hg].
    exists (g ◦ f). by apply comp_bijective.
Qed.
    
Add Parametric Relation (X Y : Type) : Type isomorphic
    reflexivity proved by isomorphic_refl
    symmetry proved by isomorphic_symm
    transitivity proved by isomorphic_trans as rel_iso.
*)

Definition IsomorphicExtensionality := forall A B:Type, A ≅ B -> A = B.


(** Open question : if pred_replace has the following form:

        isomorphic A B -> (P A <-> P B) 

    Then the [isomorphic_extensionality] axiom is not necessary for theory
    transport.
*)


Theorem iso_comp (A B C D : Type) : A ≅ B -> C ≅ D -> (A -> C) ≅ (B -> D).
Abort.
