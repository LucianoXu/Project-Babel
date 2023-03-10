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

Definition syntax := Syntax syn.

Notation Skip := skip_.

(** BwdSem *)

Definition wp_fun (mT : bwdMT): syntax -> Asn mT -> Asn mT := 
    fun _ P => P.

Lemma wp_fun_monot (mT : bwdMT) : 
    forall s, MonotonicFun.mixin_of (@wp_fun mT s).
Proof. porder_level. Qed.

Definition bwdSem_mixin (mT : bwdMT) : BwdSem.mixin_of mT syntax :=
{|
	BwdSem.wp_fun := @wp_fun mT;
    BwdSem.wp_monot := @wp_fun_monot mT;
|}.

Definition bwdSem (mT : bwdMT) := BwdSem syntax (bwdSem_mixin mT).

(** AxSem *)

Inductive ax_sys (mT : asnMT) : Asn mT -> syntax -> Asn mT -> Prop :=
| RULE_SKIP (P Q: Asn mT) (Himp : P ⊑ Q) : ax_sys P Skip Q.

Definition axSem_mixin (mT : asnMT) : AxSem.mixin_of mT syntax
    := AxSem.Mixin (@ax_sys mT).

Definition axSem (mT : asnMT) := AxSem syntax (axSem_mixin mT).

(** VeriModS *)

Definition veriModS_mixin (mT : bwdMT) : 
    VeriModS.mixin_of (axSem mT) (bwdSem mT).
Proof. 
    constructor. rewrite /VeriModS.axiom => s P Q.
    move => [] R //=. rewrite /wp_fun. by reflexivity.
Qed.

Definition veriModS (mT : bwdMT) := 
    VeriModS (axSem mT) (bwdSem mT) (veriModS_mixin mT).