(** MetaLan.v *)
From Babel Require Import TerminalDogma 
                          ExtraDogma.Extensionality
                          EpsilonDescription
                          SetFacility
                          POrderFacility.

From Babel Require Import Ranko
                            ExtensionalityCharacter
                            ClassicalCharacter.

From Babel.MetaLanguage Require Import Notations
                                        MetaType.

From Coq Require Import Relations Classical.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(****************************************)
(*                                      *)
(*       Syntax                         *)
(*       (Language Syntax)              *)
(*                                      *)
(****************************************)

Module Syntax.

Record class : Type := Class {
    sort : Type;
}.

Module Exports.

Coercion sort : class >-> Sortclass.

Notation Syn := sort.

Notation syntax := class.
Notation Syntax s := (Class s).

End Exports.

End Syntax.
Export Syntax.Exports.

(****************************************)
(*                                      *)
(*       AxSem                          *)
(*       (Axiomatic Semantics)          *)
(*                                      *)
(****************************************)


Module AxSem.
Section ClassDef.

Record mixin_of (mT : asnMT) (Syn : syntax) : Type := Mixin {
    ax_sys : Asn mT -> Syn -> Asn mT -> Prop;
}.

Record class (mT : asnMT) (syn : syntax): Type := Class {
    mixin : mixin_of mT syn;
}.

End ClassDef.

Module Exports.

Coercion mixin : class >-> mixin_of.

Notation axSem := class.
Notation AxSem m s:= (@Class _ m s).

Notation " ⊢ { P } s { Q } " := (ax_sys (mixin _) P s Q) 
    : MetaLan_Scope.
Notation " ⊢ < ax > { P } s { Q } " := (ax_sys (mixin ax) P s Q) 
    : MetaLan_Scope.

End Exports.

End AxSem.
Export AxSem.Exports.


(****************************************)
(*                                      *)
(*       BwdSem                         *)
(*       (Backward Transformer)         *)
(*                                      *)
(****************************************)


Module BwdSem.
Section ClassDef.

Record mixin_of (mT : bwdMT) (Syn : syntax) : Type := Mixin {
    wp_fun : Syn -> Asn mT -> Asn mT;
    wp_monot : forall (s : Syn), MonotonicFun.mixin_of (wp_fun s);
}.

Record class (mT : bwdMT) (syn : syntax): Type := Class {
    mixin : mixin_of mT syn;
}.

End ClassDef.

Module Exports.

Coercion mixin : class >-> mixin_of.

Notation bwdSem := class.
Notation BwdSem m s := (@Class _ m s).

Notation " 'wp' < bwd > " := (wp_fun bwd) : MetaLan_Scope.

End Exports.

End BwdSem.
Export BwdSem.Exports.

(****************************************)
(*                                      *)
(*       VeriModS                       *)
(*       (Verification Module)          *)
(*                                      *)
(****************************************)

(* only soundness is required *)
Module VeriModS.
Section ClassDef.

Definition axiom (mT : bwdMT) (syn : syntax)
    (base_ax : axSem mT syn) (base_bwd : bwdSem mT syn) :=
        forall (s : Syn syn) (P Q : Asn mT),
        ⊢ <base_ax> { P } s { Q } -> P ⊑ wp <base_bwd> s P.

Record mixin_of (mT : bwdMT) (syn : syntax)
    (base_ax : axSem mT syn) (base_bwd : bwdSem mT syn) : Type := Mixin {
    _ : axiom base_ax base_bwd;
}.

Record class (mT : bwdMT) (syn : syntax) : Type := Class {
    base_ax : axSem mT syn;
    base_bwd : bwdSem mT syn;
    mixin : mixin_of base_ax base_bwd;
}.

End ClassDef.

Module Exports.

Coercion base_ax : class >-> axSem.
Coercion base_bwd : class >-> bwdSem.
Coercion mixin : class >-> mixin_of.

Notation veriModS := class.
Notation VeriModS b_ax b_bwd m := (@Class _ _ b_ax b_bwd m).

End Exports.

End VeriModS.
Export VeriModS.Exports.


(****************************************)
(*                                      *)
(*       VeriModC                       *)
(*       (Verification Module)          *)
(*                                      *)
(****************************************)


(* both sound and complete *)
Module VeriModC.
Section ClassDef.

Definition axiom (mT : bwdMT) (syn : syntax)
    (base_ax : axSem mT syn) (base_bwd : bwdSem mT syn) :=
        forall (s : Syn syn) (P Q : Asn mT),
        P ⊑ wp <base_bwd> s P -> ⊢ <base_ax> { P } s { Q }.


Record mixin_of (mT : bwdMT) (syn : syntax)
    (base_vms : veriModS mT syn) : Type := Mixin {
    _ : axiom base_vms base_vms;
}.

Record class (mT : bwdMT) (syn : syntax) : Type := Class {
    base_vms : veriModS mT syn;
    mixin : mixin_of base_vms;
}.

End ClassDef.

Module Exports.

Coercion base_vms : class >-> veriModS.
Coercion mixin : class >-> mixin_of.

Notation veriModC := class.
Notation VeriModC b_vms m := (@Class _ _ b_vms m).

End Exports.

End VeriModC.
Export VeriModC.Exports.

