(** Infinity.v : builds the structures of finity and infinity *)
(*
From Ranko Require Import TerminalDogma.premises.
From Ranko Require Import TerminalDogma.Isomorphism.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Nat_scope.


(** finite type structure *)
Module FiniteType.

Structure mixin_of T := Mixin {
    card : nat;
    iso_prop : [ 1 , card ]N ≅ T;
}.
Notation class_of := mixin_of (only parsing).

Section ClassDef.

Structure type := Pack {sort; _ : class_of sort}.

Definition class cT := 
    let: Pack _ c := cT return class_of (sort cT) in c.

End ClassDef.

Module Exports.
Coercion sort : type >-> Sortclass.
Notation finiteType := type.
Notation FiniteMixin := Mixin.
Notation FiniteType T m := (@Pack T m).
Notation "[ 'finiteType' 'of' T ]" := ([get t | sort t ~ T : Type])
  (at level 0, format "[ 'finiteType'  'of'  T ]").
Notation "[ 'finiteMixin' 'of' T ]" := (class [finiteType of T])
  (at level 0, format "[ 'finiteMixin'  'of'  T ]").
End Exports.

End FiniteType.
Export FiniteType.Exports.
*)