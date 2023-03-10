(** USkip.v *)
From Babel Require Import TerminalDogma 
                          ExtraDogma.Extensionality
                          EpsilonDescription
                          SetFacility
                          POrderFacility.

From Babel Require Import Ranko
                            ExtensionalityCharacter
                            ClassicalCharacter.

From Babel.MetaLanguage Require Import Notations
                                        MetaType
                                        MetaLan.

From Coq Require Import Relations Classical.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Do not import this module. *)
Module USkip.

(** Syntax *)

Inductive syn :=
| skip_.

Notation Skip := skip_.

(** DeSem *)

Definition de_fun (mT : cpo): syn -> mT -> mT := 
    fun _ P => P.

Lemma de_fun_monot (mT : cpo) : 
    forall s, MonotonicFun.mixin_of (@de_fun mT s).
Proof. porder_level. Qed.

Definition deSem_mixin (mT : cpo) : DeSem.mixin_of mT syn :=
{|
	DeSem.de_fun := @de_fun mT;
    DeSem.de_monot := @de_fun_monot mT;
|}.

Definition deSem (mT : cpo) := DeSem syn (deSem_mixin mT).

(** AxSem *)

Inductive ax_sys (mT : dMT) : mT -> syn -> mT -> Prop :=
| RULE_SKIP (P Q: mT) (Himp : mT ⊢ P ⇒ Q): ax_sys P Skip Q.

Definition axSem_mixin (mT : dMT) : AxSem.mixin_of mT syn
    := AxSem.Mixin (@ax_sys mT).

Definition axSem (mT : dMT) := AxSem syn (axSem_mixin mT).

(** VeriModS *)

Definition veriModS_mixin (mT : cpoDMT) : 
    VeriModS.mixin_of (axSem mT) (deSem mT).
Proof. 
    constructor. rewrite /VeriModS.axiom => s P Q.
    move => [] R //=. rewrite /de_fun => S.
    apply (CpoDMT.class mT).
Qed.

Definition veriModS (mT : cpoDMT) := VeriModS syn (veriModS_mixin mT).

(** VeriModC *)

Definition veriModC_mixin (mT : cpoDMT) : 
    VeriModC.mixin_of (axSem mT) (deSem mT).
Proof. 
    constructor. rewrite /VeriModC.axiom.
    move => [] P Q H.

    apply RULE_SKIP.
    apply (CpoDMT.class mT).
    apply H.
Qed.

Definition veriModC (mT : cpoDMT) := VeriModC syn (veriModC_mixin mT).

(** VeriModSC *)

Definition veriModSC_mixin (mT : cpoDMT) : 
    VeriModSC.mixin_of (veriModS mT) (veriModC mT).
Proof. constructor. Qed.

Definition veriModSC (mT : cpoDMT) := VeriModSC syn (veriModSC_mixin mT).

End USkip.


