(** Isomorphism.v *)

From Ranko Require Import TerminalDogma.premises.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope Iso_scope.
Global Open Scope Iso_scope.

(** A and B are isomorphic types, if there exists a bijection between A and B *)
Definition isomorphic (A B : Type) :=
    exists f : A -> B, bijective f.
Notation " A '≅' B " := (isomorphic A B) (at level 25) : Iso_scope.

Lemma isomorphic_refl : Relation_Definitions.reflexive _ isomorphic.
Proof. rewrite /Relation_Definitions.reflexive => X.
    exists ssrfun.id. by apply id_bijective. 
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

Definition IsomorphicExtensionality := forall A B:Type, A ≅ B -> A = B.


(** Open question : if pred_replace has the following form:

        isomorphic A B -> (P A <-> P B) 

    Then the [isomorphic_extensionality] axiom is not necessary for theory
    transport.
*)


Theorem iso_comp (A B C D : Type) : A ≅ B -> C ≅ D -> (A -> C) ≅ (B -> D).
Abort.


Theorem fin_inf_neq : forall n : nat, {x | 1 <= x <= n} <> nat.
Proof. move => n H. 
    have Hcontra : {x | 1 <= x <= n} ≅ nat. { rewrite H. apply isomorphic_refl. }
Admitted.
