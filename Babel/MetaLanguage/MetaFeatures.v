(** MetaFeatures.v *)
From Babel Require Import TerminalDogma 
                          ExtraDogma.Extensionality
                          SetFacility
                          POrderFacility
                          MetaLanguage.MetaTheory.

From Babel Require Import Ranko
                            ExtensionalityCharacter
                            ClassicalCharacter.

From Coq Require Import Relations Classical.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** Verification of Partial Correctness *)

Import VeriMod.

(** Skip*)
Module Skip.

Inductive syntax (mT : metaType) : Type := skip.

Definition wp (mT : metaType) : 
    syntax mT -> Asn mT -> Asn mT :=
    fun s => fun R => R.

Lemma wp_monotonic (mT : metaType) : 
    forall s: syntax mT, MonotonicFun.mixin_of (wp s).
Proof.
    rewrite /MonotonicFun.mixin_of => s P Q.
    by rewrite /wp.
Qed.

Inductive ax_sys (mT : metaType) : 
        Asn mT -> syntax mT -> Asn mT -> Prop :=

| RULE_SEQ (R : Asn mT) : ax_sys R (skip mT) R.

Lemma ax_sys_sound (mT : metaType) :
    forall (p : syntax mT) (P Q : Asn mT),
        ax_sys P p Q -> P ⊑ wp p Q.
Proof.
    move => [] P Q [] R.
    rewrite /wp. by reflexivity.
Qed.

Lemma ax_sys_complete (mT : metaType) :
    forall (p : syntax mT) (P Q : Asn mT),
        P ⊑ wp p Q -> ax_sys P p Q.
Proof.
Abort.

(*  
Definition type (mT : metaType) : language mT := {|
    VeriMod.syntax := syntax mT;
    VeriMod.wp := @wp mT;
    VeriMod.wp_monotonic := @wp_monotonic mT;
    VeriMod.ax_sys := @ax_sys mT;
    VeriMod.ax_sys_sound := @ax_sys_sound mT;
    VeriMod.ax_sys_complete := @ax_sys_complete mT;
|}.
*)

End Skip.



(** Sequential Composition *)
Module SeqComp.

Record syntax (mT : metaType) (L0 L1: language mT) : Type := {
    S0 : VeriMod.syntax L0;
    S1 : VeriMod.syntax L1;
}.

Definition wp (mT : metaType) (L0 L1 : language mT) : 
    syntax L0 L1 -> Asn mT -> Asn mT :=
    fun s => fun R => 
        VeriMod.wp (S0 s)
            (VeriMod.wp (S1 s) R).


Lemma wp_monotonic (mT : metaType) (L0 L1 : language mT): 
        forall s: syntax L0 L1, MonotonicFun.mixin_of (wp s).
Proof.
    rewrite /MonotonicFun.mixin_of => s P Q.
    rewrite /wp => H.
    apply VeriMod.wp_monotonic.
    by apply VeriMod.wp_monotonic.
Qed.

Inductive ax_sys (mT : metaType) (L0 L1 : language mT) : 
        Asn mT -> syntax L0 L1 -> Asn mT -> Prop :=

| RULE_SEQ (s0: VeriMod.syntax L0) (s1: VeriMod.syntax L1) 
    (P R Q : Asn mT) 
    (H1 : VeriMod.ax_sys P s0 R) (H2 : VeriMod.ax_sys R s1 Q) : 
        ax_sys P {| S0 := s0; S1 := s1 |} Q.
    
Lemma ax_sys_sound (mT : metaType) (L0 L1 : language mT) :
    forall (p : syntax L0 L1) (P Q : Asn mT),
        ax_sys P p Q -> P ⊑ wp p Q.
Proof.
    move => p P Q Hsyn.
    rewrite /wp. destruct p => //=. inversion Hsyn.
    transitivity (VeriMod.wp S2 R).
    by apply VeriMod.ax_sys_sound.
    apply VeriMod.wp_monotonic.
    by apply VeriMod.ax_sys_sound.
Qed.

Lemma ax_sys_complete (mT : metaType) (L0 L1 : language mT) :
    forall (p : syntax L0 L1) (P Q : Asn mT),
        P ⊑ wp p Q -> ax_sys P p Q.
Proof.
    rewrite /wp //= => [] [] //= s0 s1 P Q Hsem.
    apply RULE_SEQ with (R := VeriMod.wp s1 Q).
    by apply VeriMod.ax_sys_complete.
    apply VeriMod.ax_sys_complete. by reflexivity.
Qed.


Definition type (mT : metaType) (L0 L1 : language mT) : language mT := {|
    VeriMod.syntax := syntax L0 L1;
    VeriMod.wp := @wp _ L0 L1;
    VeriMod.wp_monotonic := @wp_monotonic _ L0 L1;
    VeriMod.ax_sys := @ax_sys _ L0 L1;
    VeriMod.ax_sys_sound := @ax_sys_sound _ L0 L1;
    VeriMod.ax_sys_complete := @ax_sys_complete _ L0 L1;
|}.


Module Exports.

Notation "s0 ⨾ s1" := {| S0 := s0; S1 := s1 |} (at level 50) : MetaLan_Scope.

End Exports.
End SeqComp.

Export SeqComp.
