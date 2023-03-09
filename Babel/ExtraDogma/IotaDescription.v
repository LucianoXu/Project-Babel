(** IotaDescription.v : Russel's iota operator and definite description*)

From Babel Require Import TerminalDogma.

From Coq Require Export Description.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Iota.
Section ClassDef.

Definition mixin_of (T : Type) (P : T -> Prop) := exists! x, P x.
Notation class_of := mixin_of (only parsing).

Structure type (T : Type) := Pack {
    obj : T -> Prop;
    _ : class_of obj;
}.

Local Coercion obj : type >-> Funclass.

Variable (T : Type) (P : type T).

Definition class := 
    let: Pack _ c as cT' := P return class_of cT' in c.

Definition pack := Pack.

Definition iota_sigma := 
    constructive_definite_description P class.

Definition iota_term := proj1_sig iota_sigma.
Definition iota_spec := proj2_sig iota_sigma : (P iota_term).

End ClassDef.

Module Exports.
#[reversible]
Coercion obj : type >-> Funclass.

Notation iota := type.
Notation Iota T m := (@pack _ T m).

Notation ι := iota_term.

(** understand [iota_spec] as [forall P: T -> Prop, P (ι P)] *)
Notation iota_spec := iota_spec.

End Exports.

End Iota.
Export Iota.Exports.

Lemma iota_eqP (T : Type) (P : iota T) (t : T) : 
    ι(P) = t <-> P t.
Proof.
    split. 
    move <-. by apply iota_spec.

    move : (Iota.class P).
    rewrite /Iota.mixin_of //= => [] [] x [] HPx H.
    move => HPt.
    transitivity x.
    symmetry. apply H. by apply iota_spec.
    by apply H.

Qed.
