(** MetaType.v *)
From Babel Require Import TerminalDogma 
                          ExtraDogma.Extensionality
                          SetFacility
                          POrderFacility.

From Babel Require Import Ranko
                            ExtensionalityCharacter
                            ClassicalCharacter.

From Babel Require Export MetaLanguage.Notations
                            Parity.

From Coq Require Import Relations Classical.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(****************************************)
(*                                      *)
(*       PTypeMT                        *)
(*       (PType Metatype)               *)
(*                                      *)
(****************************************)

Module PTypeMT.

Definition  pSort : PSort := 
    fun 𝑷 => Type.

Record class (𝑷 : parity): Type := Class {
    sort : pSort 𝑷;
}.

Definition type_of (𝑷 : parity) (c : class 𝑷) : Type := sort c.

Module Exports.

Coercion type_of : class >-> Sortclass.

Notation pTypeMT := class.
Notation PTypeMT s := (Class s).

End Exports.

End PTypeMT.
Export PTypeMT.Exports.

(****************************************)
(*                                      *)
(*       BaseMT                         *)
(*       (Basic Metatype)               *)
(*                                      *)
(****************************************)

Module BaseMT.
Section ClassDef.


Record mixin_of (𝑷 : parity) 
    (baseF : pTypeMT 𝑷) (baseB : pTypeMT (-𝑷)) := Mixin {
    SVal : clattice;
    sat_eval : baseB -> baseF -> SVal;
}.

Record class (𝑷 : parity) := Class {
    baseF : pTypeMT 𝑷;
    baseB : pTypeMT (-𝑷);
    mixin : mixin_of baseF baseB;
}.

End ClassDef.

Module Exports.

Coercion mixin : class >-> mixin_of.

Notation FType := baseF.
Notation BType := baseB.

Notation SVal := SVal.
Notation sat_eval := sat_eval.

Notation baseMT := class.
Notation BaseMT bP bN m := (@Class _ bP bN m).
Notation " P ∙ s " := (sat_eval (mixin _) P s) : MetaLan_scope.
Notation " ⌈ x ⇒ y ⌉ " := (forall P, P ∙ x ⊑ P ∙ y) : MetaLan_scope.

End Exports.

End BaseMT.
Export BaseMT.Exports.


Section BaseMT_Theories.

Variable (𝑷 : parity) (mT : baseMT 𝑷).

(** Definition of two kinds of correctness *)
Definition correct
    (x : FType mT) (f : BType mT -> BType mT) (y : FType mT) : Prop :=
        forall P, P ∙ x ⊑ f P ∙ y.

(** Extensionality *)
Definition sat_eq : FType mT -> FType mT -> Prop :=
    fun x y => forall P, P ∙ x = P ∙ y.

(** Proof of equivalence relation. *)
Lemma sat_eq_refl : 
    reflexive _ sat_eq.
Proof. by rewrite /sat_eq.  Qed.

Lemma sat_eq_trans : 
    transitive _ sat_eq.
Proof. 
    rewrite /transitive => P Q R.
    rewrite /sat_eq => HPQ HQR x.
    rewrite -HQR. apply HPQ.
Qed.

Lemma sat_eq_symm :
    symmetric _ sat_eq.
Proof.
    rewrite /symmetric => P Q.
    rewrite /sat_eq => H x. by rewrite H.
Qed.

Add Relation _ sat_eq
    reflexivity proved by sat_eq_refl
    symmetry proved by sat_eq_symm
    transitivity proved by sat_eq_trans
    as sat_eq_rel.


(** Morphism between extensional equivalence and correctness *)
Add Morphism correct
    with signature sat_eq ==> eq ==> sat_eq ==> iff 
        as correct_mor.
Proof.
    move => P Q HPQ f R S HRS.
    rewrite /correct. split.
    - move => H s. rewrite -(HPQ s) -(HRS (f s)). by apply H.
    - move => H s. rewrite (HPQ s) (HRS (f s)). by apply H.
Qed.

(** Injection and Equivalence *)
(** IMPORTANT : this is actually the ability of distinguish of [Asn] or [Stt]. *)
Definition sat_eval_inj :=
    forall (x y : FType mT), sat_eq x y -> x = y.

End BaseMT_Theories.

Notation " ⊨ { P } f { Q } " := (@correct FD _ P f Q) : MetaLan_scope.
Notation " ⊨ [ x ] g [ y ] " := (@correct BD _ x g y) : MetaLan_scope.
Notation " P '=FD' Q " := (@sat_eq FD _ P Q) : MetaLan_scope.
Notation " x '=BD' y " := (@sat_eq BD _ x y) : MetaLan_scope.


(****************************************)
(*                                      *)
(*       cpoMT                          *)
(*       (CPO Metatype)                 *)
(*                                      *)
(****************************************)

Module CpoMT.

Section ClassDef.

Variable (𝑷 : parity).

Record mixin_of (base : baseMT 𝑷) := Mixin {
    fType_poset_mixin : Poset.mixin_of (FType base);
    fType_cpo_mixin : CPO.mixin_of (Poset _ fType_poset_mixin);
    sat_eval_monotonicity : 
        forall (x y : Poset _ fType_poset_mixin), 
            x ⊑ y <-> ⌈ x ⇒ y ⌉;
}.

Record class := Class {
    base : baseMT 𝑷;
    mixin : mixin_of base;
}.

Local Coercion mixin : class >-> mixin_of.

Definition FType_poset (c : class) : poset 
    := Poset _ (fType_poset_mixin c).
Definition FType_cpo (c : class) : cpo 
    := CPO _ (fType_cpo_mixin c).

End ClassDef.

Module Exports.

Coercion base : class >-> baseMT.
Coercion mixin : class >-> mixin_of.

Notation FType_poset := FType_poset.
Canonical FType_poset.

Notation FType_cpo := FType_cpo.
Canonical FType_cpo.

Notation Sat_eval_monotonicity := sat_eval_monotonicity.

Notation cpoMT := class.
Notation CpoMT c m := (@Class _ c m).

End Exports.
End CpoMT.

Export CpoMT.Exports.

Section CpoMT_Theories.

Variable (𝑷 : parity) (mT : cpoMT 𝑷).

Add Morphism (@ord_op (FType_poset mT))
    with signature (@sat_eq 𝑷 mT) ==> (@sat_eq 𝑷 mT) ==> iff 
        as fType_le_mor.
Proof.
    move => x y Hxy r s Hrs.
    rewrite /correct. rewrite !Sat_eval_monotonicity.
    split.
    - move => H P. rewrite -Hxy -Hrs. by apply H.
    - move => H P. rewrite Hxy Hrs. by apply H.
Qed.

Lemma cpoMT_sat_eval_inj : sat_eval_inj mT.
Proof.
    rewrite /sat_eval_inj => x y Hxy. 
    apply poset_antisym; apply Sat_eval_monotonicity => P; 
    rewrite Hxy; by reflexivity.
Qed.

End CpoMT_Theories.

(****************************************)
(*                                      *)
(*       CLatticeMT                     *)
(*                                      *)
(*       (Complete Lattice)             *)
(****************************************)


Module CLatticeMT.

Section ClassDef.

Variable (𝑷 : parity).

Record mixin_of (cpo_mT : cpoMT 𝑷) := Mixin {
    fType_lattice_mixin : Lattice.mixin_of (FType_poset cpo_mT);
    fType_clattice_mixin : CLattice.mixin_of 
            (Lattice.class (Lattice _ fType_lattice_mixin));
    sat_eval_join_mor : 
        forall (X : 𝒫(CLattice _ fType_clattice_mixin)) P, 
            P ∙ (⊔ᶜˡ X) = ⊔ᶜˡ { P ∙ s, s | s ∈ X };
}.

Record class := Class {
    cpo_mT : cpoMT 𝑷;
    mixin : mixin_of cpo_mT;
}.

Local Coercion mixin : class >-> mixin_of.

Definition FType_clattice (c : class) : clattice := 
    CLattice _ (fType_clattice_mixin c).

End ClassDef.

Module Exports.

Coercion cpo_mT : class >-> cpoMT.
Coercion mixin : class >-> mixin_of.

Notation FType_clattice := FType_clattice.
Canonical FType_clattice.

Notation Sat_eval_join_mor := sat_eval_join_mor.

Notation cLatticeMT := class.
Notation CLatticeMT c m := (@Class _ c m).

End Exports.
End CLatticeMT.

Export CLatticeMT.Exports.