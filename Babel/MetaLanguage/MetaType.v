(** MetaType.v *)
From Babel Require Import TerminalDogma 
                          ExtraDogma.Extensionality
                          SetFacility
                          POrderFacility.

From Babel Require Import Ranko
                            ExtensionalityCharacter
                            ClassicalCharacter.

From Babel.MetaLanguage Require Export Notations.

From Coq Require Import Relations Classical.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(****************************************)
(*                                      *)
(*       AsnMT                          *)
(*       (Assertion Metatype)           *)
(*                                      *)
(****************************************)

Module AsnMT.

Record class : Type := Class {
    sort : iType;
}.

Module Exports.

Coercion sort : class >-> iType.

Notation asnMT := class.
Notation AsnMT s := (Class s).

End Exports.

End AsnMT.
Export AsnMT.Exports.


(****************************************)
(*                                      *)
(*       SttMT                          *)
(*       (State Metatype)               *)
(*                                      *)
(****************************************)

Module SttMT.

Record class : Type := Class {
    sort : iType;
}.

Module Exports.

Coercion sort : class >-> iType.

Notation sttMT := class.
Notation SttMT s := (Class s).

End Exports.

End SttMT.
Export SttMT.Exports.


(****************************************)
(*                                      *)
(*       BaseMT                         *)
(*       (Basic Metatype)               *)
(*                                      *)
(****************************************)

Module BaseMT.
Section ClassDef.

Record mixin_of (Stt : sttMT) (Asn : asnMT) := Mixin {
    SVal : clattice;
    sat_eval : Asn -> Stt -> SVal;
}.

Record class := Class {
    Stt : sttMT;
    Asn : asnMT;
    mixin : mixin_of Stt Asn;
}.

End ClassDef.

Module Exports.

Coercion mixin : class >-> mixin_of.

Notation Stt := Stt.
Notation Asn := Asn.
Notation SVal := SVal.
Notation sat_eval := sat_eval.

Notation baseMT := class.
Notation BaseMT stt asn m := (@Class stt asn m).
Notation " P ∙ s " := (sat_eval (mixin _) P s) : MetaLan_Scope.
Notation " ⌈ P ⇒ Q ⌉ " := (forall s, P ∙ s ⊑ Q ∙ s) : MetaLan_Scope.

End Exports.

End BaseMT.
Export BaseMT.Exports.

(** Definition of two kinds of correctness *)
Definition bwd_correct (mT : baseMT) 
    (P : Asn mT) (f : Stt mT -> Stt mT) (Q : Asn mT) : Prop :=
        forall s, P ∙ s ⊑ Q ∙ f s.
Notation " ⊨ { P } f { Q } " := (bwd_correct P f Q) : MetaLan_Scope.

Definition fwd_correct (mT : baseMT)
    (x : Stt mT) (g : Asn mT -> Asn mT) (y : Stt mT) : Prop :=
        forall P, P ∙ x ⊑ g P ∙ y.
Notation " ⊨ [ x ] g [ y ] " := (fwd_correct x g y) : MetaLan_Scope.

(** Extensionality *)
Definition sat_asn_eq (mT : baseMT) : Asn mT -> Asn mT -> Prop :=
    fun P Q => forall s, P ∙ s = Q ∙ s.
Notation " P '=asn' Q " := (sat_asn_eq P Q) : MetaLan_Scope.

Definition sat_stt_eq (mT : baseMT) : Stt mT -> Stt mT -> Prop :=
    fun x y => forall P, P ∙ x = P ∙ y.
Notation " x '=stt' y " := (sat_stt_eq x y) : MetaLan_Scope.

(** Proof of equivalence relation. *)
Lemma sat_asn_eq_refl (mT : baseMT): 
    reflexive _ (@sat_asn_eq mT).
Proof. by rewrite /sat_asn_eq. Qed.

Lemma sat_asn_eq_trans (mT : baseMT): 
    transitive _ (@sat_asn_eq mT).
Proof. 
    rewrite /transitive => P Q R.
    rewrite /sat_asn_eq => HPQ HQR x.
    rewrite -HQR. apply HPQ.
Qed.

Lemma sat_asn_eq_symm (mT : baseMT):
    symmetric _ (@sat_asn_eq mT).
Proof.
    rewrite /symmetric => P Q.
    rewrite /sat_asn_eq => H x. by rewrite H.
Qed.

Add Parametric Relation (mT : baseMT) : _ (@sat_asn_eq mT)
    reflexivity proved by (@sat_asn_eq_refl mT)
    symmetry proved by (@sat_asn_eq_symm mT)
    transitivity proved by (@sat_asn_eq_trans mT)
    as sat_asn_eq_rel.
    

(** Proof of equivalence relation. *)
Lemma sat_stt_eq_refl (mT : baseMT): 
    reflexive _ (@sat_stt_eq mT).
Proof. by rewrite /sat_stt_eq. Qed.

Lemma sat_stt_eq_trans (mT : baseMT): 
    transitive _ (@sat_stt_eq mT).
Proof. 
    rewrite /transitive => x y z.
    rewrite /sat_stt_eq => Hxy Hyz P.
    rewrite -Hyz. apply Hxy.
Qed.

Lemma sat_stt_eq_symm (mT : baseMT):
    symmetric _ (@sat_stt_eq mT).
Proof.
    rewrite /symmetric => x y.
    rewrite /sat_stt_eq => H P. by rewrite H.
Qed.

Add Parametric Relation (mT : baseMT) : _ (@sat_stt_eq mT)
    reflexivity proved by (@sat_stt_eq_refl mT)
    symmetry proved by (@sat_stt_eq_symm mT)
    transitivity proved by (@sat_stt_eq_trans mT)
    as sat_stt_eq_rel.


(** Morphism between extensional equivalence and correctness *)
Add Parametric Morphism (mT : baseMT) : (@bwd_correct mT)
    with signature (@sat_asn_eq mT) ==> eq ==> (@sat_asn_eq mT) ==> iff 
        as bwd_correct_mor.
Proof.
    move => P Q HPQ f R S HRS.
    rewrite /bwd_correct. split.
    - move => H s. rewrite -(HPQ s) -(HRS (f s)). by apply H.
    - move => H s. rewrite (HPQ s) (HRS (f s)). by apply H.
Qed.

(** Injection and Equivalence *)
(** IMPORTANT : this is actually the ability of distinguish of [Asn] or [Stt]. *)
Definition sat_eval_Asn_inj (mT : baseMT) :=
    forall (P Q : Asn mT), P =asn Q -> P = Q.

Definition sat_eval_Stt_inj (mT : baseMT) :=
    forall (x y : Stt mT), x =stt y -> x = y.


(****************************************)
(*                                      *)
(*       bwdMT                          *)
(*       (Backward Metatype)            *)
(*                                      *)
(****************************************)

Module BwdMT.

Section ClassDef.

Record mixin_of (comb : baseMT) := Mixin {
    asn_poset_mixin : Poset.mixin_of (AsnMT.sort (Asn comb));
    asn_cpo_mixin : CPO.mixin_of (Poset _ asn_poset_mixin);
    sat_eval_Asn_monotonicity : 
        forall (P Q : Poset _ asn_poset_mixin), 
            P ⊑ Q <-> ⌈ P ⇒ Q ⌉;
}.

Record class := Class {
    comb : baseMT;
    mixin : mixin_of comb;
}.

Local Coercion mixin : class >-> mixin_of.

Definition asn_poset (c : class) : poset := Poset _ (asn_poset_mixin c).
Definition asn_cpo (c : class) : cpo := CPO _ (asn_cpo_mixin c).

End ClassDef.

Module Exports.

Coercion comb : class >-> baseMT.
Coercion mixin : class >-> mixin_of.

Notation Asn_poset := asn_poset.
Canonical asn_poset.

Notation Asn_cpo := asn_cpo.
Canonical asn_cpo.

Notation Sat_eval_Asn_monotonicity := sat_eval_Asn_monotonicity.

Notation bwdMT := class.
Notation BwdMT c m := (@Class c m).

End Exports.
End BwdMT.

Export BwdMT.Exports.


Add Parametric Morphism (mT : bwdMT) : (@ord_op (Asn_poset mT))
    with signature (@sat_asn_eq mT) ==> (@sat_asn_eq mT) ==> iff 
        as asn_le_mor.
Proof.
    move => P Q HPQ R S HRS.
    rewrite /bwd_correct. rewrite !Sat_eval_Asn_monotonicity.
    split.
    - move => H s. rewrite -HPQ -HRS. by apply H.
    - move => H s. rewrite HPQ HRS. by apply H.
Qed.

Lemma bwdMT_sat_eval_Asn_inj (mT : bwdMT): sat_eval_Asn_inj mT.
Proof.
    rewrite /sat_eval_Asn_inj => P Q HPQ. 
    apply poset_antisym; apply Sat_eval_Asn_monotonicity => s; 
    rewrite HPQ; by reflexivity.
Qed.

(****************************************)
(*                                      *)
(*       bwdCMT                         *)
(*       (Backward Metatype)            *)
(*       (Complete Lattice)             *)
(****************************************)


Module BwdCMT.

Section ClassDef.

Record mixin_of (bwd_mT : bwdMT) := Mixin {
    asn_lattice_mixin : Lattice.mixin_of (Asn_poset bwd_mT);
    asn_clattice_mixin : CLattice.mixin_of (Lattice.class (Lattice _ asn_lattice_mixin));
    sat_eval_Asn_join_mor : 
        forall (Ps : 𝒫(CLattice _ asn_clattice_mixin)) s, 
            (⊔ᶜˡ Ps) ∙ s = ⊔ᶜˡ { P ∙ s, P | P ∈ Ps };
}.

Record class := Class {
    bwd_mT : bwdMT;
    mixin : mixin_of bwd_mT;
}.

Local Coercion mixin : class >-> mixin_of.

Definition asn_clattice (c : class) : clattice := CLattice _ (asn_clattice_mixin c).

End ClassDef.

Module Exports.

Coercion bwd_mT : class >-> bwdMT.
Coercion mixin : class >-> mixin_of.

Notation Asn_clattice := asn_clattice.
Canonical asn_clattice.

Notation Sat_eval_Asn_join_mor := sat_eval_Asn_join_mor.

Notation bwdCMT := class.
Notation BwdCMT c m := (@Class c m).

End Exports.
End BwdCMT.

Export BwdCMT.Exports.