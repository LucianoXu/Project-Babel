(** MetaType.v *)
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

Section Meta_Duality_Theories.


Definition meta_dual (mT : baseMT) 
    (f : FType mT -> FType mT) (g : BType mT -> BType mT) : Prop :=
        forall (P : BType mT) (s : FType mT), P ∙ (f s) ⊑ (g P) ∙ s.


Definition bidual (mT : baseMT) 
    (f : FType mT -> FType mT) (g : BType mT -> BType mT) : Prop :=
        meta_dual f g /\ @meta_dual (Parity_Trans mT) g f.


Notation bidual' g := (fun f => bidual f g).

Notation " f ^← " := (ε (bidual f)) : MetaLan_scope.
Notation " g ^→ " := (ε (bidual' g)) : MetaLan_scope.



(** IMPORTANT : notice the relation between ' -> ' and the soundness of a
    verification system. *)
Lemma correct_dual_sufficiency (mT : cpoMT) 
    (f : FType mT -> FType mT) (g : BType mT -> BType mT) :
        meta_dual f g -> forall (x y : FType_cpo mT),  
            x ⊑ f y -> ⊨ { (x : FType mT) } g { y }.
(** It's necessary to redesign the coercion path! *)
Proof.
    move => Hdual x y.
    move => H.
        rewrite /correct => P. 
        transitivity (P ∙ f y). by apply Sat_eval_monotonicity.
        apply Hdual.
Qed.


Lemma correct_dual_necessarity (mT : cpoMT) 
    (f : FType mT -> FType mT) (g : BType mT -> BType mT) :
        @meta_dual (Parity_Trans mT) g f -> forall (x y : FType_cpo mT),  
            ⊨ { (x : FType mT) } g { y } -> x ⊑ f y.
Proof.
    move => Hdual x y.
    rewrite /correct => H.
    apply Sat_eval_monotonicity => P.
    transitivity (g P ∙ y). by apply H. by apply Hdual.
Qed.

(** The existence of backward dual may seems trival in specific cases, but 
    demands a premise in the very general case. *)
Lemma correct_duality_expressiveness (mT : cpoMT) (g : BType mT -> BType mT):
    (forall (y : FType mT), exists x, ⊨ { x } g { y }) -> exists f, meta_dual f g.
Proof.
    rewrite /correct => H.
    exists (fun r => ε (fun x => ∀ P : BType mT, P ∙ x ⊑ (g P) ∙ r)).

    rewrite /meta_dual => Q s.

    move : (@epsilon_spec _ (λ x : FType mT, ∀ P : BType mT, P ∙ x ⊑ g P ∙ s) (H s)) => //.
Qed.



(* 
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
*)











    

(** Important *)
Definition bwd_dual_existence (mT : cLatticeMT) (g : BType mT -> BType mT) : 
    { f : FType mT -> FType mT | meta_dual f g }.
Proof.
    econstructor.
    instantiate (1 := 
        (fun y => ⊔ᶜˡ ({ x , x | ⊨ { x } g { y } } : 𝒫(FType_clattice mT)))).
    rewrite /meta_dual => Q s.
    rewrite Sat_eval_join_mor => //=.
    (** QUESTION : is this assumption of join morphism too strong here? *)

    apply CLattice.join_prop.
    porder_level.
    by apply a0.
Qed.


(*###################################################################*)
(** Conclusions about bidual*)

Lemma bidualP (mT : baseMT)
    (f : FType mT -> FType mT) (g : BType mT -> BType mT):
    bidual f g <-> forall P s, P ∙ f s = g P ∙ s.
Proof.
    rewrite /bidual /meta_dual. split.
    - move => [H1 H2] P s. apply poset_antisym. by apply H1. by apply H2.
    - move => H. split => P s. 
        + rewrite H; by reflexivity.
        + unfold Parity_Trans in *. simpl in *. rewrite H; by reflexivity.
Qed.


Lemma bidual_unique (mT : baseMT)
    (g : BType mT -> BType mT)
    (f1 f2 : FType mT -> FType mT) (H1 : bidual f1 g) (H2 : bidual f2 g) :
    forall x, f1 x =FD f2 x.
Proof.
    rewrite /sat_eq => s P.
    rewrite bidualP in H1. rewrite bidualP in H2.
    by rewrite H1 H2.
Qed.


Lemma bidual_eq (mT : baseMT)
    (g : BType mT -> BType mT) (f : FType mT -> FType mT):
    bidual f g -> forall P, g ^→ P =FD f P.
Proof.
    move => Hdual. apply (@bidual_unique _ g).
    - rewrite /meta_dual. apply epsilon_PeP. by exists f.
    - by [].
Qed.

Lemma bidual_feq (mT : cpoMT)
    (g : BType mT -> BType mT) (f : FType mT -> FType mT):
        bidual f g -> g ^→ = f.
Proof. 
    move => Hdual.
    apply functional_extensionality => s.
    by apply /cpoMT_sat_eval_inj /bidual_eq.
Qed.

Lemma dual_involutive (mT : cpoMT)
    (Hinj : sat_eval_inj (Parity_Trans mT))
    (f : FType mT -> FType mT):
    (exists g, bidual f g) -> f ^← ^→ = f.
Proof.
    move => [g Hg].
    apply bidual_feq => //=.
    apply epsilon_PeP.
    by exists g.
Qed.

Lemma correct_dual_equiv (mT : cpoMT) 
    (f : FType mT -> FType mT) (g : BType mT -> BType mT) :
        bidual f g -> forall (x y : FType_cpo mT),  
            x ⊑ f y <-> ⊨ { (x : FType mT) } g { y }.
Proof.
    move => Hdual P Q. split.
    - apply /correct_dual_sufficiency.
        by apply Hdual.
    
    - apply /correct_dual_necessarity.
        by apply Hdual.
Qed.

End Meta_Duality_Theories.