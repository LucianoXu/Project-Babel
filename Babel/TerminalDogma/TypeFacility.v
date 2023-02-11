(** TypeFacility.v *)

From mathcomp Require Import all_ssreflect.
Require Import Coq.Unicode.Utf8_core.

From Babel Require Import CanonicalInfrastructure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope TerminalDogma_scope.
Open Scope TerminalDogma_scope.

Theorem pred_replace : 
    forall {A B : Type} (P : Type -> Prop), A = B -> (P A <-> P B).
Proof. move => A B P Heq. by case Heq. Qed.

Definition transport {A B : Type} : A -> A = B -> B.
Proof. move => a H. by rewrite -H. Defined.

Notation "[ a 'by' HAB ]" := (transport a HAB) : TerminalDogma_scope.

        
(** inhabited type structure *)
Module IType.

Structure type := Pack {
    sort : Type;
    witness : sort;
}.

Module Exports.
Coercion sort : type >-> Sortclass.
Notation iType := type.
Notation IType t w := (Pack t w).
Notation "[ 'iType' 'of' T ]" := ([get t | sort t ~ T : Type])
  (at level 0, format "[ 'iType'  'of'  T ]") : TerminalDogma_scope.
Notation "[ 'witness' 'of' T ]" := (witness [iType of T])
  (at level 0, format "[ 'witness'  'of'  T ]") : TerminalDogma_scope.

End Exports.

End IType.
Export IType.Exports.