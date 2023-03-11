(** USeq.v *)
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
Module USeq.


(** Syntax *)

Record syn (syn0 syn1 : Type) := seq_ {
    S0 : syn0;
    S1 : syn1;
}.

Notation "s0 ⨾ s1" := {| S0 := s0; S1 := s1 |} : MetaLan_scope.


(** DeSem 
    For now let's consider backward semantics.
*)

Definition de_fun (mT : cpo) (de0 de1 : deSem mT): syn de0 de1 -> mT -> mT := 
    fun s P => ⟦ S0 s ⟧ <de0> (⟦ S1 s ⟧ <de1> P).

Lemma de_fun_monot (mT : cpo) (de0 de1 : deSem mT): 
    forall s, MonotonicFun.mixin_of (@de_fun mT de0 de1 s).
Proof. 
    porder_level.
    rewrite /de_fun.
    apply DeSem.de_monot.
    by apply DeSem.de_monot. 
Qed.

Definition deSem_mixin (mT : cpo) (de0 de1 : deSem mT) : 
    DeSem.mixin_of mT (syn de0 de1) :=
{|
	DeSem.de_fun := @de_fun mT de0 de1;
    DeSem.de_monot := @de_fun_monot mT de0 de1;
|}.

Definition deSem (mT : cpo) (de0 de1 : deSem mT) := 
    DeSem (syn de0 de1) (deSem_mixin de0 de1).



(** AxSem *)

Inductive ax_sys (mT : dMT) (ax0 ax1 : axSem mT) : 
    mT -> syn ax0 ax1 -> mT -> Prop :=

| RULE_SEQ 
        (s0 : ax0) (s1 : ax1) (P R Q : mT) 
        (H0 : ⊢ { P } s0 { R }) 
        (H1 : ⊢ { R } s1 { Q }): ax_sys P (s0 ⨾ s1)  Q.

Definition axSem_mixin (mT : dMT) (ax0 ax1 : axSem mT) : 
        AxSem.mixin_of mT (syn ax0 ax1)
    := AxSem.Mixin (@ax_sys _ ax0 ax1).

Definition axSem (mT : dMT) (ax0 ax1 : axSem mT) := 
    AxSem (syn ax0 ax1) (axSem_mixin ax0 ax1).


(** VeriModS *)

Definition veriModS_mixin (mT : cpoDMT) (veriS0 veriS1 : veriModS mT): 
    VeriModS.mixin_of (axSem veriS0 veriS1) (deSem veriS0 veriS1).
Proof. 
    constructor. rewrite /VeriModS.axiom => [] [] s0 s1 P Q.
    move => [] //=. intros. rewrite /de_fun.
    apply (soundness_of veriS1) in H1 => //=.
    apply (soundness_of veriS0) in H0 => //=.
    
    transitivity ((⟦ s2 ⟧ < DeSem veriS0 (VeriModS.base_de veriS0) >) R).
    - by [].
    - by apply (DeSem.de_monot).
Qed.

Definition veriModS (mT : cpoDMT) (veriS0 veriS1 : veriModS mT) := 
    VeriModS (syn veriS0 veriS1) (veriModS_mixin veriS0 veriS1).

    
(** VeriModC *)


Definition veriModC_mixin (mT : cpoDMT) (veriC0 veriC1 : veriModC mT): 
    VeriModC.mixin_of (axSem veriC0 veriC1) (deSem veriC0 veriC1).
Proof. 
    constructor. rewrite /VeriModC.axiom => [] [] s0 s1 P Q. simpl.
    rewrite /de_fun => //= H.
    eapply RULE_SEQ.
    instantiate (1 := (⟦ s1 ⟧ < VeriModC.base_de veriC1 >) Q).

    by apply (completeness_of _).
    apply (completeness_of _); by reflexivity.
Qed.

Definition veriModC (mT : cpoDMT) (veriC0 veriC1 : veriModC mT) := 
    VeriModC (syn veriC0 veriC1) (veriModC_mixin veriC0 veriC1).

(** VeriModSC *)

Definition veriModSC_mixin (mT : cpoDMT) (veri0 veri1 : veriModSC mT) : 
    VeriModSC.mixin_of (veriModS veri0 veri1) (veriModC veri0 veri1).
Proof. constructor. Qed.

Definition veriModSC (mT : cpoDMT) (veri0 veri1 : veriModSC mT) := 
    VeriModSC (syn veri0 veri1) (veriModSC_mixin veri0 veri1).

End USeq.
