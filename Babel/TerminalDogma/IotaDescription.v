(** IotaDescription.v : Russel's iota operator and definite description*)

From mathcomp Require Import all_ssreflect.
Require Import Coq.Unicode.Utf8_core.

From Coq Require Export Description.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Iota.
Section ClassDef.

Definition mixin_of (T : Type) (P : T -> Prop) := exists! x, P x.
Definition class_of := mixin_of.

Structure type (T : Type) := Pack {
    obj : T -> Prop;
    _ : class_of obj;
}.

Local Coercion obj : type >-> Funclass.

Variable (T : Type) (cT : type T).

Definition class := 
    let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack := Pack.

Definition iota_sigma := 
    constructive_definite_description cT class.

Definition iota_term := proj1_sig iota_sigma.
Definition iota_spec := proj2_sig iota_sigma.

End ClassDef.

Module Exports.
#[reversible]
Coercion obj : type >-> Funclass.

Notation iota := type.
Notation Iota T m := (@pack _ T m).

Notation ι := iota_term.
Notation iota_spec := iota_spec.

End Exports.

End Iota.
Export Iota.Exports.