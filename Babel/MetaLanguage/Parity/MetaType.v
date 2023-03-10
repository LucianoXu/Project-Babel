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
(*       DMT                            *)
(*       (Deduction Metatype)           *)
(*                                      *)
(****************************************)

Module DMT.
Section ClassDef.

Record mixin_of (T : iType) := Mixin {
    ded_sys : T -> T -> Prop;
}.

Notation class_of := mixin_of (only parsing).

Record type := Pack {
    sort : iType;
    class : class_of sort;
}.

End ClassDef.

Module Exports.

#[reversible]
Coercion sort : type >-> iType.

Coercion class : type >-> mixin_of.

Notation dMT := type.
Notation DMT s m := (@Pack s m).
Notation Dsys := ded_sys.

Notation " ax ⊢ P ⇒ Q " := ((Dsys ax) P Q) : MetaLan_scope.

End Exports.
End DMT.
Export DMT.Exports.



(****************************************)
(*                                      *)
(*       cpoDMT                         *)
(*       (cpo with Deduction Metatype)  *)
(*                                      *)
(****************************************)

Module CpoDMT.

Section ClassDef.

Record mixin_of (T : iType) 
        (b_cpo : CPO.class_of T) (b_dMT : DMT.mixin_of T) 
        (bcpo := CPO T b_cpo) (bdMT := DMT T b_dMT):= Mixin {
    
    ded_iffP : forall (P Q : bcpo), 
        P ⊑ Q   <->   bdMT ⊢ P ⇒ Q;
}.

Record class_of (T : iType) := Class {
    b_cpo : CPO.class_of T;
    b_dMT : DMT.mixin_of T;
    mixin : mixin_of b_cpo b_dMT;
}.

Record type := Pack {
    sort : iType;
    class : class_of sort;
}.

Local Coercion sort : type >-> iType.
Local Coercion class : type >-> class_of.

Variable (cT : type).

Definition pack (T : iType) (b_cpo : CPO.class_of T) (b_dMT : DMT.mixin_of T) 
    (m : mixin_of b_cpo b_dMT) : type := @Pack T (Class m).

Definition to_cpo : cpo := CPO cT (b_cpo cT).
Definition to_dMT : dMT := DMT cT (b_dMT cT).

End ClassDef.

Module Exports.

#[reversible]
Coercion sort : type >-> iType.
Coercion to_cpo : type >-> cpo.
Coercion to_dMT : type >-> dMT.
Coercion class : type >-> class_of.

Notation cpoDMT := type.
Notation CpoDMT T m := (@pack T _ _ m).

End Exports.

End CpoDMT.
Export CpoDMT.Exports.


(****************************************)
(*                                      *)
(*       BaseMT                         *)
(*       (Basic Metatype)               *)
(*                                      *)
(****************************************)
Module BaseMT.

Section ClassDef.

Record mixin_of (FType BType : iType) := Mixin {
    SVal : clattice;
    sat_eval : BType -> FType -> SVal;
}.

Notation class_of := mixin_of (only parsing).

(** This acts as the basic rules of this program world. *)
Record type := Pack {
    fType : iType;
    bType : iType;
    class : class_of fType bType;
}.

Local Coercion class : type >-> mixin_of.


End ClassDef.


Module Exports.

Coercion class : type >-> mixin_of.

Notation baseMT := type.
Notation BaseMT fT bT m := (@Pack fT bT m).

Notation FType := fType.
Notation BType := bType.
Notation SVal := SVal.

Notation " P ∙ s " := (sat_eval (class _) P s) : MetaLan_scope.
Notation " P ∙ s :> mT" := (sat_eval (class mT) P s) 
    (only parsing): MetaLan_scope.
Notation " ⌈ x ⇒ y ⌉ " := (forall P, P ∙ x ⊑ P ∙ y) : MetaLan_scope.
Notation " ⌈ x ⇒ y ⌉ :> mT " := (forall P, P ∙ x :> mT ⊑ P ∙ y :> mT) 
    (only parsing): MetaLan_scope.


End Exports.
End BaseMT.
Export BaseMT.Exports.

(** How to do parity transformation? *)
Definition Parity_Trans : baseMT -> baseMT :=
    fun b => 
    {|
        BaseMT.fType := BType b;
        BaseMT.bType := FType b;
        BaseMT.class := {|
            BaseMT.SVal := SVal b;
            BaseMT.sat_eval := fun bt ft => BaseMT.sat_eval b ft bt;
        |};
    |}.

Definition parity_trans_involutive : 
    forall b : baseMT, Parity_Trans (Parity_Trans b) = b.
Proof. move => [] ? ? [] => //=. Qed.

    
Section BaseMT_Theories.

Variable (mT : baseMT).



(** Definition of two kinds of correctness *)
Definition correct
    (x : FType mT) (f : BType mT -> BType mT) (y : FType mT) : Prop :=
        forall P, P ∙ x ⊑ (f P)∙ y.

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

Notation " ⊨ { P } f { Q } " := (@correct _ P f Q) : MetaLan_scope.
Notation " ⊨ [ x ] g [ y ] " := (@correct _ x g y) : MetaLan_scope.
Notation " P '=FD' Q " := (@sat_eq _ P Q) : MetaLan_scope.


(****************************************)
(*                                      *)
(*       cpoMT                          *)
(*       (CPO Metatype)                 *)
(*                                      *)
(****************************************)

Module CpoMT.

Section ClassDef.


Record mixin_of (fType bType : iType)
            (b : BaseMT.mixin_of fType bType) 
            (b_cpo : CPO.class_of fType) 
            (base := BaseMT _ _ b) (bcpo := CPO _ b_cpo)
        := Mixin {

    sat_eval_monotonicity : forall (x y : bcpo), x ⊑ y <-> ⌈ x ⇒ y ⌉ :> base;
}.

Record class_of (fType bType : iType) := Class {
    base : BaseMT.mixin_of fType bType;
    base_cpo : CPO.class_of fType;
    mixin : mixin_of base base_cpo;
}.

Record type := Pack {
    fType : iType;
    bType : iType;
    class : class_of fType bType;
}.

Local Coercion class : type >-> class_of.

Definition to_baseMT (c : type) : baseMT :=
    BaseMT _ _ (base c).

Definition fType_cpo (c : type) : cpo := CPO _ (base_cpo c).

Lemma sat_eval_monotonicity_wrap (cT : type) :
    forall (x y : (fType_cpo cT)), x ⊑ y <-> ⌈ x ⇒ y ⌉ :> (to_baseMT cT).
Proof. apply sat_eval_monotonicity. by apply (class cT). Qed.


End ClassDef.

Module Exports.

Coercion class : type >-> class_of.
Coercion mixin : class_of >-> mixin_of.

Coercion to_baseMT : type >-> baseMT.

Notation FType_cpo := fType_cpo.
Notation Sat_eval_monotonicity := sat_eval_monotonicity_wrap.

Notation cpoMT := type.
Notation CpoMT fT bT m := (@Pack fT bT (Class m)).

End Exports.
End CpoMT.

Export CpoMT.Exports.

Section CpoMT_Theories.

Variable (mT : cpoMT).

Add Morphism (@ord_op (FType_cpo mT))
    with signature (@sat_eq mT) ==> (@sat_eq mT) ==> iff 
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
    apply (@poset_antisym (FType_cpo mT)). 
    all: apply Sat_eval_monotonicity => P; rewrite Hxy; by reflexivity.
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

Record mixin_of (fType bType: iType)
        (b : CpoMT.class_of fType bType) (b_cl : CLattice.class_of fType)
        (mT := CpoMT fType bType b) (cl := CLattice fType b_cl) 
            := Mixin {

    sat_eval_join_mor : 
        forall (X : 𝒫(cl)) (P : BType mT), 
          P ∙ (⊔ᶜˡ X) = ⊔ᶜˡ { P ∙ s, s | s ∈ X };
}.

Record class_of (fType bType : iType) := Class {
    b_cpoMT : CpoMT.class_of fType bType;
    b_cl : CLattice.class_of fType;
    mixin : mixin_of b_cpoMT b_cl;
}.

Record type := Pack {
    fType : iType;
    bType : iType;
    class : class_of fType bType;
}.

Local Coercion class : type >-> class_of.

Definition to_cpoMT (cT : type) : cpoMT := CpoMT _ _ (b_cpoMT cT).
Definition FType_clattice (cT : type) : clattice := CLattice _ (b_cl cT).

Lemma sat_eval_join_mor_wrap (cT : type) :
    forall (X : 𝒫(FType_clattice cT)) (P : BType (to_cpoMT cT)), 
        P ∙ (⊔ᶜˡ X) = ⊔ᶜˡ { P ∙ s, s | s ∈ X }.
Proof. apply sat_eval_join_mor. apply (mixin cT). Qed.

End ClassDef.

Module Exports.

Coercion to_cpoMT : type >-> cpoMT.
Coercion class : type >-> class_of.

Notation FType_clattice := FType_clattice.
Canonical FType_clattice.

Notation Sat_eval_join_mor := sat_eval_join_mor_wrap.

Notation cLatticeMT := type.
Notation CLatticeMT fT bT m := (@Pack fT bT (Class m)).

End Exports.
End CLatticeMT.

Export CLatticeMT.Exports.
