(** MetaType.v *)
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

Definition bwd_dual (mT : baseMT) 
    (f : Stt mT -> Stt mT) (g : Asn mT -> Asn mT) : Prop :=
        forall (P : Asn mT) (s : Stt mT), (g P) ∙ s ⊑ P ∙ (f s).

Definition fwd_dual (mT : baseMT)
    (g : Asn mT -> Asn mT) (f : Stt mT -> Stt mT) : Prop :=
        forall (P : Asn mT) (s : Stt mT), P ∙ (f s) ⊑ (g P) ∙ s.

Definition bidual (mT : baseMT) 
    (f : Stt mT -> Stt mT) (g : Asn mT -> Asn mT) : Prop :=
        bwd_dual f g /\ fwd_dual g f.

Notation bidual' g := (fun f => bidual f g).

Notation " f ^← " := (ε (bidual f)) : MetaLan_Scope.
Notation " g ^→ " := (ε (bidual' g)) : MetaLan_Scope.

(** IMPORTANT : notice the relation between ' -> ' and the soundness of a
    verification system. *)
Lemma bwd_correct_dual_sufficiency (mT : bwdMT) 
    (f : Stt mT -> Stt mT) (g : Asn mT -> Asn mT) :
        bwd_dual f g -> forall (P Q : Asn_poset mT),  P ⊑ g Q -> ⊨ { P } f { Q }.
(** It's necessary to redesign the coercion path! *)
Proof.
    move => Hdual P Q.
    move => H.
        rewrite /bwd_correct => s. 
        transitivity (g Q ∙ s). by apply Sat_eval_Asn_monotonicity.
        apply Hdual.
Qed.

Lemma bwd_correct_dual_necessarity (mT : bwdMT) 
    (f : Stt mT -> Stt mT) (g : Asn mT -> Asn mT) :
        fwd_dual g f -> forall (P Q : Asn_poset mT),  ⊨ { P } f { Q } -> P ⊑ g Q.
Proof.
    move => Hdual P Q.
    rewrite /bwd_correct => H.
    apply Sat_eval_Asn_monotonicity => s.
    transitivity (Q ∙ f s) => //=.
Qed.

(** The existence of backward dual may seems trival in specific cases, but 
    demands a premise in the very general case. *)
Lemma bwd_correct_duality_expressiveness (mT : bwdMT) (f : Stt mT -> Stt mT):
    (forall (Q : Asn mT), exists P, ⊨ { P } f { Q }) -> exists g, bwd_dual f g.
Proof.
    rewrite /bwd_correct => H.
    exists (fun R => ε (fun P => ∀ s : Stt mT, P ∙ s ⊑ R ∙ f s)).

    rewrite /bwd_dual => Q s.
    move : (@epsilon_spec _ (λ P : Asn mT, ∀ s0 : Stt mT, P ∙ s0 ⊑ Q ∙ f s0) (H Q)) => //.
Qed.




Lemma lim_bwd_correct (mT : bwdCMT)
    (Ps : 𝒫(Asn mT)) (f : Stt mT -> Stt mT) (Q : Asn mT) :

    ⊨ { ⊔ᶜˡ (Ps : 𝒫(Asn_clattice mT)) } f { Q }
        -> (forall' P ∈ Ps, ⊨ { P } f { Q }).

Proof.
    - rewrite /bwd_correct => H.
        + move => P HPin s.
        transitivity ((⊔ᶜˡ) (Ps : 𝒫(Asn_clattice mT)) ∙ s).
        rewrite Sat_eval_Asn_join_mor => //=. by porder_level.
        by apply H.
Qed.

(** Important *)
Definition bwd_dual_existence (mT : bwdCMT) (f : Stt mT -> Stt mT) : 
    { g : Asn mT -> Asn mT | bwd_dual f g }.
Proof.
    econstructor.
    instantiate (1 := 
        (fun Q => ⊔ᶜˡ ({ P , P | ⊨ { P } f { Q } } : 𝒫(Asn_clattice mT)))).
    rewrite /bwd_dual => Q s.
    rewrite Sat_eval_Asn_join_mor => //=.
    (** QUESTION : is this assumption of join morphism too strong here? *)

    apply CLattice.join_prop.
    porder_level.
    by apply a0.
Qed.


(*###################################################################*)
(** Conclusions about bidual*)

Lemma bidualP (mT : baseMT)
    (f : Stt mT -> Stt mT) (g : Asn mT -> Asn mT) :
    bidual f g <-> forall P s, P ∙ f s = g P ∙ s.
Proof.
    rewrite /bidual /fwd_dual /bwd_dual. split.
    - move => [H1 H2] P s. apply poset_antisym. by apply H2. by apply H1.
    - move => H. split => P s; rewrite H; by reflexivity.
Qed.


Lemma bidual_unique_bwd (mT : baseMT)
    (f : Stt mT -> Stt mT)
    g1 g2 (H1 : bidual f g1) (H2 : bidual f g2) :
    forall P, g1 P =asn g2 P.
Proof.
    rewrite /sat_asn_eq => P s.
    rewrite bidualP in H1. rewrite bidualP in H2.
    by rewrite -H1 -H2.
Qed.

Lemma bidual_unique_fwd (mT : baseMT)
    (g : Asn mT -> Asn mT)
    f1 f2 (H1 : bidual f1 g) (H2 : bidual f2 g) :
    forall s, f1 s =stt f2 s.
Proof.
    rewrite /sat_stt_eq => s P.
    rewrite bidualP in H1. rewrite bidualP in H2.
    by rewrite H1 H2.
Qed.

Lemma bidual_bwd_eq (mT : baseMT)
    (f : Stt mT -> Stt mT) (g : Asn mT -> Asn mT):
    bidual f g -> forall P, f ^← P =asn g P.
Proof.
    move => Hdual. apply (@bidual_unique_bwd _ f).
    - rewrite /bwd_dual. apply epsilon_PeP. by exists g.
    - by [].
Qed.

Lemma bidual_fwd_eq (mT : baseMT)
    (g : Asn mT -> Asn mT) (f : Stt mT -> Stt mT):
    bidual' g f -> forall s, g ^→ s =stt f s.
Proof.
    move => Hdual. apply (@bidual_unique_fwd _ g).
    - rewrite /bwd_dual. apply epsilon_PeP. by exists f.
    - by [].
Qed.

Lemma bidual_bwd_feq (mT : bwdMT)
    (f : Stt mT -> Stt mT) (g : Asn mT -> Asn mT):
        bidual f g -> f ^← = g.
Proof. 
    move => Hdual.
    apply functional_extensionality => P.
    by apply /bwdMT_sat_eval_Asn_inj /bidual_bwd_eq.
Qed.

Lemma bidual_fwd_feq (mT : baseMT) (Hinj_Stt : sat_eval_Stt_inj mT)
    (g : Asn mT -> Asn mT) (f : Stt mT -> Stt mT):
        bidual' g f -> g ^→ = f.
Proof. 
    move => Hdual.
    apply functional_extensionality => s.
    by apply /Hinj_Stt /bidual_fwd_eq.
Qed.

Lemma bwd_dual_involutive (mT : baseMT)
    (Hinj_Stt : sat_eval_Stt_inj mT)
    (f : Stt mT -> Stt mT):
    (exists g, bidual f g) -> f ^← ^→ = f.
Proof.
    move => [g Hg].
    apply bidual_fwd_feq => //=.
    apply epsilon_PeP.
    by exists g.
Qed.

Lemma bwd_correct_dual_equiv (mT : bwdMT) 
    (f : Stt mT -> Stt mT) (g : Asn mT -> Asn mT) :
        bidual f g -> forall (P Q : Asn_poset mT),  P ⊑ g Q <-> ⊨ { P } f { Q }.
Proof.
    move => Hdual P Q. split.
    - apply /bwd_correct_dual_sufficiency.
        by apply Hdual.
    
    - apply /bwd_correct_dual_necessarity.
        by apply Hdual.
Qed.