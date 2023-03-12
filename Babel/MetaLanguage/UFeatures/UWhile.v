(** UWhile.v *)
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
Module UWhile.


(** Syntax *)

Record syn (mT : cpo) (Hj : FlowCtrl.join mT) (syn0 : Type) := while_ {
    flow_split : FlowCtrl.split Hj;
    S0 : syn0;
}.

Notation M0 s := (FlowCtrl.M0 (flow_split s)).
Notation M1 s := (FlowCtrl.M1 (flow_split s)).

Notation "'While' M 'Do' s0 'End'" := (while_ M s0) : MetaLan_scope.


(** DeSem 

    Notice the application of Kleene fixpoint here.
*)

Definition while_iter (mT : cpo) (Hj : FlowCtrl.join mT) 
    (de0 : deSem mT) (P : mT): 
    syn Hj de0 -> mT -> mT :=
        fun s X => ((M0 s) (⟦ S0 s ⟧ <de0> X)) ⊕[Hj] ((M1 s) P).

Lemma while_iter_mono_mixin (mT : cpo) (Hj : FlowCtrl.join mT) 
    (de0 : deSem mT) (P : mT) (s : syn Hj de0) : 
    MonotonicFun.mixin_of (while_iter P s).
Proof. rewrite /MonotonicFun.mixin_of /while_iter => x y Hxy.
    transitivity (M0 s ((⟦ S0 s ⟧ < de0 >) x) ⊕[ Hj] M1 s P).
    - apply FlowCtrl.join_monot1.
        apply MonotonicFun.class. by reflexivity.
    - apply FlowCtrl.join_monot0.
        apply MonotonicFun.class.
        by apply MonotonicFun.class.
Qed.

Canonical while_iter_mono (mT : cpo) (Hj : FlowCtrl.join mT) 
    (de0 : deSem mT) (P : mT) (s : syn Hj de0) : [ mT ↦ᵐ mT ] :=
    MonotonicFun (while_iter P s) (while_iter_mono_mixin P s).

Lemma while_iter_conti_mixin (mT : cpo) (Hj : FlowCtrl.join mT) 
    (de0 : deSem mT) (P : mT) (s : syn Hj de0) : 
    ContinuousFun.mixin_of (MonotonicFun.class (while_iter P s)).
Proof. rewrite /ContinuousFun.mixin_of => ch //=.
    rewrite /while_iter //=.
Admitted.

Canonical while_iter_conti (mT : cpo) (Hj : FlowCtrl.join mT) 
    (de0 : deSem mT) (P : mT) (s : syn Hj de0) : [ mT ↦ mT ] :=
    ContinuousFun (while_iter P s) (while_iter_conti_mixin P s).


Definition de_fun (mT : cpo) (Hj : FlowCtrl.join mT) (de0 : deSem mT) : 
    syn Hj de0 -> mT -> mT := 
        fun s P => KleeneFp (while_iter P s).

Lemma de_fun_monot_mixin (mT : cpo) (Hj : FlowCtrl.join mT) 
    (de0 : deSem mT) (s : syn Hj de0) : MonotonicFun.mixin_of (de_fun s).
Proof. rewrite /MonotonicFun.mixin_of /de_fun //= => x y Hxy.
    rewrite /KleeneFp.

    (** proof by order of functions by KleeneFp. *)
Admitted.

Canonical de_fun_monot (mT : cpo) (Hj : FlowCtrl.join mT) 
    (de0 : deSem mT) (s : syn Hj de0) : [ mT ↦ᵐ mT ] :=
    MonotonicFun (de_fun s) (de_fun_monot_mixin s).

Lemma de_fun_conti_mixin (mT : cpo) (Hj : FlowCtrl.join mT) 
    (de0 : deSem mT) (s : syn Hj de0) : 
        ContinuousFun.mixin_of (MonotonicFun.class (de_fun s)).
Proof. 
    rewrite /ContinuousFun.mixin_of //= => ch.
    rewrite /de_fun //=.
Admitted.

Canonical de_fun_conti (mT : cpo) (Hj : FlowCtrl.join mT) 
    (de0 : deSem mT) (s : syn Hj de0) : [ mT ↦ mT ] :=
    ContinuousFun (de_fun s) (de_fun_conti_mixin s).

Definition deSem_mixin (mT : cpo) (Hj : FlowCtrl.join mT) (de0 : deSem mT) : 
    DeSem.mixin_of mT (syn Hj de0) :=
{|
	DeSem.de_fun := @de_fun mT Hj de0;
|}.

Definition deSem (mT : cpo) (Hj : FlowCtrl.join mT) (de0 : deSem mT) :=
    DeSem (syn Hj de0) (deSem_mixin Hj de0).

(** AxSem 
    Note that cpoDMT is needed here.
*)

Inductive ax_sys (mT : cpoDMT) (Hj : FlowCtrl.join mT) (ax0 : axSem mT) : 
    mT -> syn Hj ax0 -> mT -> Prop :=

| RULE_LOOP (M : FlowCtrl.split Hj)
        (s0 : ax0) (P Inv Q : mT) 
        (H : ⊢ <ax0> { Inv } s0 { (FlowCtrl.M0 M Inv) ⊕[Hj] (FlowCtrl.M1 M Q) }) 
        (Himp : mT ⊢ P ⇒ ((FlowCtrl.M0 M Inv) ⊕[Hj] (FlowCtrl.M1 M Q))): 

            ax_sys P (While M Do s0 End) Q.
            

Definition axSem_mixin (mT : cpoDMT) (Hj : FlowCtrl.join mT) 
    (ax0 : axSem mT) : AxSem.mixin_of mT (syn Hj ax0)
    := @AxSem.Mixin mT _ (@ax_sys mT Hj ax0).

Definition axSem (mT : cpoDMT) (Hj : FlowCtrl.join mT) (ax0 : axSem mT) 
        : AxSem.mixin_of mT (syn Hj ax0) :=
    AxSem (syn Hj ax0) (axSem_mixin Hj ax0).
        


(*
(** VeriModS *)

Definition veriModS_mixin (mT : cpoDMT) (Hj : FlowCtrl.join mT) 
    (veriS0 : veriModS mT): 
    VeriModS.mixin_of (axSem Hj veriS0) (deSem Hj veriS0).
Proof. 
    constructor. rewrite /VeriModS.axiom => [] [] Hs s0 P Q.
    move => [] //=. intros. rewrite /de_fun.

    transitivity (
        (ContinuousFun.obj (FlowCtrl.M0 M) Inv
          ⊕[ Hj] ContinuousFun.obj (FlowCtrl.M1 M) Q0)
    ).
    - by apply /(CpoDMT.ded_iffP (CpoDMT.mixin mT)).

    apply (soundness_of veriS0) in H.
    rewrite /KleeneFp //=.


    

    

    apply (soundness_of veriS1) in H1 => //=.
    apply (soundness_of veriS0) in H0 => //=.
    
    transitivity ((⟦ s2 ⟧ < DeSem veriS0 (VeriModS.base_de veriS0) >) R).
    - by [].
    - by apply (DeSem.de_monot).
Qed.

Definition veriModS (mT : cpoDMT) (veriS0 veriS1 : veriModS mT) := 
    VeriModS (syn veriS0 veriS1) (veriModS_mixin veriS0 veriS1).
*)
End UWhile.
