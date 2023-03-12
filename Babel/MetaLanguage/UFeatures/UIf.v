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
Module UIf.


(** Syntax *)

Record syn (mT : cpo) (Hj : FlowCtrl.join mT) (syn0 syn1 : Type) := if_ {
    flow_split : FlowCtrl.split Hj;
    S0 : syn0;
    S1 : syn1;
}.

Notation M0 s := (FlowCtrl.M0 (flow_split s)).
Notation M1 s := (FlowCtrl.M1 (flow_split s)).

Notation "'If' M 'Then' s0 'Else' s1 'End'" := (if_ M s0 s1) : MetaLan_scope.


(** DeSem 
*)


Definition de_fun (mT : cpo) (Hj : FlowCtrl.join mT) (de0 de1 : deSem mT) : 
        syn Hj de0 de1 -> mT -> mT := 
    fun s P => ((M0 s) (⟦ S0 s ⟧ <de0> P)) ⊕[Hj] ((M1 s) (⟦ S1 s ⟧ <de1> P)).

Lemma de_fun_monot_mixin (mT : cpo) (Hj : FlowCtrl.join mT) (de0 de1 : deSem mT): 
    forall s, MonotonicFun.mixin_of (@de_fun mT Hj de0 de1 s).
Proof. 
    porder_level.
    rewrite /de_fun.

    transitivity (M0 s ((⟦ S0 s ⟧ < de0 >) x) ⊕[ Hj ] M1 s ((⟦ S1 s ⟧ < de1 >) y)).
    + apply (FlowCtrl.join_monot1).
        apply MonotonicFun.class.
        by apply DeSem.de_monot.

    + apply (FlowCtrl.join_monot0).
        apply MonotonicFun.class.
        by apply DeSem.de_monot.
Qed.

Canonical de_fun_monot (mT : cpo) (Hj : FlowCtrl.join mT) 
    (de0 de1 : deSem mT) (s : syn Hj de0 de1): [mT ↦ᵐ mT] :=
    MonotonicFun (de_fun s) (de_fun_monot_mixin s).

Lemma de_fun_conti_mixin (mT : cpo) (Hj : FlowCtrl.join mT) 
    (de0 de1 : deSem mT) (s : syn Hj de0 de1): 
        ContinuousFun.mixin_of (de_fun_monot_mixin s).
Proof.
    rewrite /ContinuousFun.mixin_of => x.
    rewrite /de_fun //=.

    rewrite !DeSem.de_conti.
    rewrite (ContinuousFun.mixin (ContinuousFun.class (M0 s))).
    rewrite (ContinuousFun.mixin (ContinuousFun.class (M1 s))) //=.

    have t := (flow_join_conti Hj 
        ((M0 s) ◦ (⟦ S0 s ⟧ < de0 >)) ((M1 s) ◦ (⟦ S1 s ⟧ < de1 >)) x).
    rewrite /conti_fun_comp /fun_comp /monotonic_mapR_chain in t. simpl in t. 
    rewrite /monotonic_mapR_chain => //=.
    
    (* 



    Check (Chain
    (((λ P : CPO.sort mT,
         ContinuousFun.obj (M0 s) (ContinuousFun.obj (⟦ S0 s ⟧ < de0 >) P)
         ⊕[ Hj] ContinuousFun.obj (M1 s) (ContinuousFun.obj (⟦ S1 s ⟧ < de1 >) P)) [<]) x)
    (monotonic_mapR_chainMixin (c:=x))).
    *)
Admitted.



Canonical de_fun_conti (mT : cpo) (Hj : FlowCtrl.join mT) (de0 de1 : deSem mT) 
        (s : syn Hj de0 de1) : 
        continuousfun mT mT :=
    ContinuousFun (de_fun s) (de_fun_conti_mixin s).


Definition deSem_mixin (mT : cpo) (Hj : FlowCtrl.join mT) (de0 de1 : deSem mT) : 
    DeSem.mixin_of mT (syn Hj de0 de1) :=
{|
    DeSem.de_fun := @de_fun mT Hj de0 de1;
|}.

Definition deSem (mT : cpo) (Hj : FlowCtrl.join mT) (de0 de1 : deSem mT) := 
    DeSem (syn Hj de0 de1) (deSem_mixin Hj de0 de1).


(** AxSem 
    Note that cpoDMT is needed here.
*)

Inductive ax_sys (mT : cpoDMT) (Hj : FlowCtrl.join mT) (ax0 ax1 : axSem mT) : 
    mT -> syn Hj ax0 ax1 -> mT -> Prop :=

| RULE_IF (M : FlowCtrl.split Hj)
        (s0 : ax0) (s1 : ax1) (P P0 P1 Q : mT) 
        (H0 : ⊢ <ax0> { P0 } s0 { Q }) 
        (H1 : ⊢ <ax1> { P1 } s1 { Q })
        (Himp : mT ⊢ P ⇒ ((FlowCtrl.M0 M P0) ⊕[Hj] (FlowCtrl.M1 M P1))): 

            ax_sys P (If M Then s0 Else s1 End) Q.            
            

Definition axSem_mixin (mT : cpoDMT) (Hj : FlowCtrl.join mT) 
    (ax0 ax1 : axSem mT) : AxSem.mixin_of mT (syn Hj ax0 ax1)
    := @AxSem.Mixin mT _ (@ax_sys mT Hj ax0 ax1).

Definition axSem (mT : cpoDMT) (Hj : FlowCtrl.join mT) (ax0 ax1 : axSem mT) := 
    AxSem (syn Hj ax0 ax1) (axSem_mixin Hj ax0 ax1).


(** VeriModS *)

Definition veriModS_mixin (mT : cpoDMT) (Hj : FlowCtrl.join mT) 
        (veriS0 veriS1 : veriModS mT): 
    VeriModS.mixin_of (axSem Hj veriS0 veriS1) (deSem Hj veriS0 veriS1).
Proof. 
    constructor. 

    rewrite /VeriModS.axiom => [] [] Hs s0 s1 P Q [] //=.

    intros M s0' s1' P' P0 P1 Q' H0 H1 Himp.
    apply (CpoDMT.class mT) in Himp.
    rewrite /de_fun => //=.

    transitivity (
        FlowCtrl.M0 M ((⟦ s0' ⟧ < VeriModS.base_de veriS0 >) Q')
        ⊕[ Hj] FlowCtrl.M1 M P1
    ).
    
    - transitivity (FlowCtrl.M0 M P0 ⊕[ Hj] FlowCtrl.M1 M P1) => //.
        apply FlowCtrl.join_monot0.
        apply MonotonicFun.class.
        apply (soundness_of veriS0) in H0 => //=.

    - apply FlowCtrl.join_monot1.
        apply MonotonicFun.class.
        apply (soundness_of veriS1) in H1 => //=.
Qed.

Definition veriModS (mT : cpoDMT) (Hj : FlowCtrl.join mT) 
        (veriS0 veriS1 : veriModS mT) := 
    VeriModS (syn Hj veriS0 veriS1) (veriModS_mixin Hj veriS0 veriS1).



(** VeriModC *)

Definition veriModC_mixin (mT : cpoDMT) (Hj : FlowCtrl.join mT) 
        (veriC0 veriC1 : veriModC mT): 
    VeriModC.mixin_of (axSem Hj veriC0 veriC1) (deSem Hj veriC0 veriC1).
Proof. 
    constructor. 
    
    rewrite /VeriModC.axiom => [] [] Hs s0 s1 P Q //=.
    rewrite /de_fun => //= H.

    eapply RULE_IF.

    - instantiate (1 := (⟦ s0 ⟧ < VeriModC.base_de veriC0 >) Q).
        apply (completeness_of _) => //=. by reflexivity.
    - instantiate (1 := (⟦ s1 ⟧ < VeriModC.base_de veriC1 >) Q).
        apply (completeness_of _) => //=. by reflexivity.

    by apply (CpoDMT.class mT).
Qed.

Definition veriModC (mT : cpoDMT) (Hj : FlowCtrl.join mT) 
        (veriC0 veriC1 : veriModC mT) := 
    VeriModC (syn Hj veriC0 veriC1) (veriModC_mixin Hj veriC0 veriC1).



(** VeriModSC *)

Definition veriModSC_mixin (mT : cpoDMT) (Hj : FlowCtrl.join mT) 
        (veri0 veri1 : veriModSC mT) : 
    VeriModSC.mixin_of (veriModS Hj veri0 veri1) (veriModC Hj veri0 veri1).
Proof. constructor. Qed.

Definition veriModSC (mT : cpoDMT) (Hj : FlowCtrl.join mT) 
        (veri0 veri1 : veriModSC mT) := 
    VeriModSC (syn Hj veri0 veri1) (veriModSC_mixin Hj veri0 veri1).

End UIf.


    
    

