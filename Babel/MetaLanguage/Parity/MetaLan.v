(** MetaLan.v *)
From Babel Require Import TerminalDogma 
                          ExtraDogma.Extensionality
                          EpsilonDescription
                          SetFacility
                          POrderFacility.

From Babel Require Import Ranko
                            ExtensionalityCharacter
                            ClassicalCharacter.

From Babel Require Import MetaLanguage.Notations
                            MetaType.

From Coq Require Import Relations Classical.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



(****************************************)
(*                                      *)
(*       AxSem                          *)
(*       (Axiomatic Semantics)          *)
(*                                      *)
(****************************************)


Module AxSem.

Section ClassDef.

Record mixin_of (mT : dMT) (syn : Type) : Type := Mixin {
    ax_sys : mT -> syn -> mT -> Prop;
}.

Notation class_of := mixin_of (only parsing).

Record type (mT : dMT) := Pack {
    syn : Type;
    class : class_of mT syn;
}.


End ClassDef.

Module Exports.

#[reversible]
Coercion syn : type >-> Sortclass.
Coercion class : type >-> mixin_of.

Notation axSem := type.
Notation AxSem s m:= (@Pack _ s m).

Notation " ⊢ { P } s { Q } " := (ax_sys _ P s Q) (only printing)
    : MetaLan_scope.
Notation " ⊢ { P } s { Q } " := (ax_sys (class _) P s Q) 
    : MetaLan_scope.
Notation " ⊢ < ax > { P } s { Q } " := (ax_sys (class ax) P s Q) 
    : MetaLan_scope.

End Exports.

End AxSem.
Export AxSem.Exports.



(****************************************)
(*                                      *)
(*       DeSem                          *)
(*       (Backward Transformer)         *)
(*                                      *)
(****************************************)


Module DeSem.
Section ClassDef.

Record mixin_of (mT : cpo) (syn : Type) : Type := Mixin {
    de_fun : syn -> mT -> mT;
    de_monot : forall (s : syn), MonotonicFun.mixin_of (de_fun s);
}.

Notation class_of := mixin_of (only parsing).

Record type (mT : cpo) : Type := Pack {
    syn : Type;
    class : class_of mT syn;
}.

End ClassDef.

Module Exports.

#[reversible]
Coercion syn : type >-> Sortclass.
Coercion class : type >-> mixin_of.

Notation deSem := type.
Notation DeSem s m := (@Pack _ s m).

Notation " ⟦ s ⟧ < de > " := (de_fun de s) : MetaLan_scope.

End Exports.

End DeSem.
Export DeSem.Exports.

(****************************************)
(*                                      *)
(*       VeriModS                       *)
(*       (Verification Module)          *)
(*                                      *)
(****************************************)

(* only soundness is required *)
Module VeriModS.
Section ClassDef.

Definition axiom (mT : cpoDMT) (syn : Type)
    (ax_m : AxSem.mixin_of mT syn) (de_m : DeSem.mixin_of mT syn) 
    (base_de := DeSem syn de_m) (base_ax := AxSem syn ax_m):=

        forall (s : syn) (P Q : [cpo of mT]),
        ⊢ <base_ax> { P } s { Q } -> P ⊑ ⟦ s ⟧ <base_de> Q.

Record mixin_of (mT : cpoDMT) (syn : Type)
    (ax_m : AxSem.mixin_of mT syn) (de_m : DeSem.mixin_of mT syn) : Type 
        := Mixin {
    soundness : axiom ax_m de_m;
}.

Record class_of (mT : cpoDMT) (syn : Type) : Type := Class {
    base_ax : AxSem.mixin_of mT syn;
    base_de : DeSem.mixin_of mT syn;
    mixin : mixin_of base_ax base_de;
}.

Record type (mT : cpoDMT) := Pack {
    syn : Type;
    class : class_of mT syn;
}.

Local Coercion syn : type >-> Sortclass.
Local Coercion class : type >-> class_of.

Definition to_axSem (mT : cpoDMT) (cT : type mT) :=
    AxSem (syn cT) (base_ax cT).

Definition to_deSem (mT : cpoDMT) (cT : type mT) :=
    DeSem (syn cT) (base_de cT).

Definition soundness_of (mT : cpoDMT) (cT : type mT) :=
    soundness (mixin cT).
    

End ClassDef.

Module Exports.

#[reversible]
Coercion syn : type >-> Sortclass.
Coercion class : type >-> class_of.
Coercion mixin : class_of >-> mixin_of.

Coercion to_axSem : type >-> axSem.
Coercion to_deSem : type >-> deSem.

Notation veriModS := type.
Notation VeriModS s m := (@Pack _ s (Class m)).

Arguments soundness_of [_] _.
Notation soundness_of := soundness_of.

End Exports.

End VeriModS.
Export VeriModS.Exports.


(****************************************)
(*                                      *)
(*       VeriModC                       *)
(*       (Verification Module)          *)
(*                                      *)
(****************************************)


(* complete *)
Module VeriModC.
Section ClassDef.

Definition axiom (mT : cpoDMT) (syn : Type)
    (ax_m : AxSem.mixin_of mT syn) (de_m : DeSem.mixin_of mT syn) 
    (base_ax := AxSem syn ax_m) (base_de := DeSem syn de_m) :=
        forall (s : syn) (P Q : [cpo of mT]),
        P ⊑ ⟦ s ⟧ <base_de> Q -> ⊢ <base_ax> { P } s { Q }.


Record mixin_of (mT : cpoDMT) (syn : Type)
    (ax_m : AxSem.mixin_of mT syn) (de_m : DeSem.mixin_of mT syn) 
        : Type := Mixin {
    completeness : axiom ax_m de_m;
}.

Record class_of (mT : cpoDMT) (syn : Type) : Type := Class {
    base_ax : AxSem.mixin_of mT syn;
    base_de : DeSem.mixin_of mT syn;
    mixin : mixin_of base_ax base_de;
}.

Record type (mT : cpoDMT) := Pack {
    syn : Type;
    class : class_of mT syn;
}.

Local Coercion syn : type >-> Sortclass.
Local Coercion class : type >-> class_of.

Definition to_axSem (mT : cpoDMT) (cT : type mT) :=
    AxSem (syn cT) (base_ax cT).

Definition to_deSem (mT : cpoDMT) (cT : type mT) :=
    DeSem (syn cT) (base_de cT).

Definition completeness_of (mT : cpoDMT) (cT : type mT) :=
    completeness (mixin cT).

End ClassDef.

Module Exports.

#[reversible]
Coercion syn : type >-> Sortclass.
Coercion class : type >-> class_of.
Coercion mixin : class_of >-> mixin_of.

Coercion to_axSem : type >-> axSem.
Coercion to_deSem : type >-> deSem.

Notation veriModC := type.
Notation VeriModC s m := (@Pack _ s (Class m)).

Arguments completeness_of [_] _.
Notation completeness_of := completeness_of.

End Exports.

End VeriModC.
Export VeriModC.Exports.


    
(****************************************)
(*                                      *)
(*       VeriModSC                      *)
(*       (Verification Module)          *)
(*                                      *)
(****************************************)


(* sound and complete *)
Module VeriModSC.
Section ClassDef.

Definition axiom (mT : cpoDMT) (syn : Type)
    (ax_m : AxSem.mixin_of mT syn) (de_m : DeSem.mixin_of mT syn) 
    (base_ax := AxSem syn ax_m) (base_de := DeSem syn de_m) :=
        forall (s : syn) (P Q : [cpo of mT]),
        P ⊑ ⟦ s ⟧ <base_de> Q <-> ⊢ <base_ax> { P } s { Q }.


Lemma to_soundness (mT : cpoDMT) (syn : Type)
    (ax_m : AxSem.mixin_of mT syn) (de_m : DeSem.mixin_of mT syn) 
    (base_ax := AxSem syn ax_m) (base_de := DeSem syn de_m):

    axiom base_ax base_de -> VeriModS.axiom base_ax base_de.
Proof. rewrite /axiom /VeriModS.axiom => H s P Q.
    by rewrite H.
Qed.


Lemma to_completeness (mT : cpoDMT) (syn : Type)
    (ax_m : AxSem.mixin_of mT syn) (de_m : DeSem.mixin_of mT syn) 
    (base_ax := AxSem syn ax_m) (base_de := DeSem syn de_m):

    axiom base_ax base_de -> VeriModC.axiom base_ax base_de.
Proof. rewrite /axiom /VeriModC.axiom => H s P Q.
    by rewrite H.
Qed.


Record mixin_of (mT : cpoDMT) (syn : Type)
    (ax_m : AxSem.mixin_of mT syn) (de_m : DeSem.mixin_of mT syn)
    (veriS_m : VeriModS.mixin_of ax_m de_m) 
    (veriC_m : VeriModC.mixin_of ax_m de_m) 
        : Type := Mixin {
}.


Lemma combine (mT : cpoDMT) (syn : Type)
    (ax_m : AxSem.mixin_of mT syn) (de_m : DeSem.mixin_of mT syn) 
    (veriS_m : VeriModS.mixin_of ax_m de_m) 
    (veriC_m : VeriModC.mixin_of ax_m de_m) :

    axiom ax_m de_m.

Proof. rewrite /axiom => s P Q. split.
    destruct veriC_m as [H_C]. by apply H_C. 
    destruct veriS_m as [H_S]. by apply H_S.
Qed.


Record class_of (mT : cpoDMT) (syn : Type) : Type := Class {
    base_ax : AxSem.mixin_of mT syn;
    base_de : DeSem.mixin_of mT syn;
    equiv : axiom base_ax base_de;
}.

Record type (mT : cpoDMT) := Pack {
    syn : Type;
    class : class_of mT syn;
}.

Local Coercion syn : type >-> Sortclass.
Local Coercion class : type >-> class_of.

Definition pack (mT : cpoDMT) (syn : Type) 
    (ax_m : AxSem.mixin_of mT syn) (de_m : DeSem.mixin_of mT syn)
    (veriS_m : VeriModS.mixin_of ax_m de_m) 
    (veriC_m : VeriModC.mixin_of ax_m de_m) 
    (m : mixin_of veriS_m veriC_m) : type mT :=
        Pack (Class (combine veriS_m veriC_m)).

Definition to_veriModS (mT : cpoDMT) (cT : type mT) :=
    VeriModS (syn cT) (VeriModS.Mixin (to_soundness (equiv cT))).

Definition to_veriModC (mT : cpoDMT) (cT : type mT) :=
    VeriModC (syn cT) (VeriModC.Mixin (to_completeness (equiv cT))).

End ClassDef.

Module Exports.

#[reversible]
Coercion syn : type >-> Sortclass.
Coercion class : type >-> class_of.

Coercion to_veriModS : type >-> veriModS.
Coercion to_veriModC : type >-> veriModC.

Notation veriModSC := type.
Notation VeriModSC s m := (@pack _ s _ _ _ _ m).

End Exports.

End VeriModSC.
Export VeriModSC.Exports.

