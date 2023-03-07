(** MetaRefinement.v *)
From Babel Require Import TerminalDogma 
                          ExtraDogma.Extensionality
                          ExtraDogma.AllDecidable
                          SetFacility
                          POrderFacility
                          MetaLanguage.MetaTheory.

From Coq Require Import Relations Classical.

From Babel Require Import Ranko
                            ExtensionalityCharacter
                            AllDecidableCharacter
                            ClassicalCharacter.



Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Coercion decide_oracle : Sortclass >-> bool.

Import BackwardSemModel.
Import FunPointwiseOrder.CanonicalStruct.


(*
Lemma prog_preorderMixin (mT : metaType) (L : language mT): 
    Preorder.mixin_of (syntax L).
Proof.
    refine (@Preorder.Mixin (syntax L) (fun s1 s2 => wp s1 ⊑ wp s2) _).
    constructor.
    rewrite /reflexive. ranko.
    rewrite /transitive. ranko. by transitivity (wp y x0).
Defined.

Canonical prog_preorder (mT : metaType) (L : language mT) := 
    Preorder (syntax L) (@prog_preorderMixin mT L).

*)


Module SpecMod.

Record syntax (mT : metaType) : Type := {
    pre: Asn mT;
    post: Asn mT;
}.

Definition wp (mT : metaType) : syntax mT -> Asn mT -> Asn mT :=
    fun p => fun R => 
        if post p ⊑ R 
            then pre p 
            else ⊔ᶜˡ (∅ : 𝒫(Asn mT)).

Lemma wp_monotonic (mT : metaType) : 
    forall p: syntax mT, MonotonicFun.mixin_of (wp p).
Proof.
    rewrite /MonotonicFun.mixin_of => p P Q.
    rewrite /wp => H.

    case E: (decide_oracle (post p ⊑ P)).
    - rewrite decide_oracle_true in E.
        replace (decide_oracle (post p ⊑ Q)) with true.
        by reflexivity.
        symmetry. rewrite decide_oracle_true. by transitivity P.
    - apply CLattice.join_prop. ranko.
Qed.


Definition type (mT : metaType) : language mT := {|
    BackwardSemModel.syntax := syntax mT;
    BackwardSemModel.wp := @wp mT;
    BackwardSemModel.wp_monotonic := @wp_monotonic mT;
|}.




Module Exports.

Notation "P ‖ Q" := {| pre := P; post := Q |} (at level 50) : MetaLan_Scope.
(* #[export] Hint Unfold RefinementFactory.wp_with_spec : magic_book. *)

End Exports.

End SpecMod.
Export SpecMod.Exports.



Theorem Theorem_Refinement_A (mT : metaType) 
        (L : language mT) (s : syntax L) (P Q : Asn mT) : 
        wp (P ‖ Q : syntax (SpecMod.type _)) ⊑ wp (s)
            <-> P ⊑ wp s Q.
Proof. split.
    * ranko. refine (poset_trans _ (H Q)).
        rewrite /SpecMod.wp.
        replace (decide_oracle (SpecMod.post (P ‖ Q) ⊑ Q)) with true.
        by reflexivity. 
        ranko.
    * ranko. rewrite /SpecMod.wp.
        case E: (decide_oracle (SpecMod.post (P ‖ Q) ⊑ x)); move : E.
        + ranko. apply (wp_monotonic s) in E.
        by transitivity (wp s Q).
        + ranko.
Qed. 

Theorem Theorem_Refinement_B (mT : metaType) 
        (L : language mT) (s : syntax L) (P Q : Asn mT) : 
        P ⊑ wp s Q <-> ⌈ sat_eval P ⇒ sat_eval (wp s Q) ⌉.
Proof. ranko. Qed.
















(*

(** program language model (typed) 
    stt : the variable state type considered in this model *)
Record prog_lan_model (stt : Type) : Type := {

    (* the program syntax type *)
    syntax : Type;
    
    (* the denotational semantics of the program *)
    desem : syntax -> stt -> stt;

}.

Notation " ⟦ P ⟧ " := (desem P).
Notation " ⟦ P ⟧ ( s ) " := (desem P s).


(** definition of correctness *)

Definition pred (stt : Type) := stt -> Prop.

Definition pred_order {stt : Type} (P Q : pred stt) : Prop := 
    forall s : stt, P s -> Q s.

Record correctness_formula {stt : Type} (plm : prog_lan_model stt) := {
    pre_cond : pred stt;
    mid_prog : syntax plm;
    post_cond : pred stt;
}.

Definition semantic_correct {stt : Type} {plm : prog_lan_model stt}
    (formula : correctness_formula plm) :=
    forall s : stt, (pre_cond formula) s -> (post_cond formula) ⟦ (mid_prog formula) ⟧ (s).

Definition proof_system {stt : Type} (plm : prog_lan_model stt) :=
    correctness_formula plm -> Prop.

Definition soundness {stt : Type} {plm : prog_lan_model stt} 
    (ps : proof_system plm) :=
    forall (formula : correctness_formula plm), 
        ps formula -> semantic_correct formula.

Definition completeness {stt : Type} {plm : prog_lan_model stt} 
    (ps : proof_system plm) :=
    forall (formula : correctness_formula plm),
        semantic_correct formula -> ps formula.

(** Being a weakest liberal condition *)
Definition wlp {stt : Type} {plm : prog_lan_model stt} 
            (P : pred stt) (S0 : syntax plm) (Q : pred stt) :=
    semantic_correct {| pre_cond := P; mid_prog := S0; post_cond := Q |}
    /\ forall P', semantic_correct {| pre_cond := P; mid_prog := S0; post_cond := Q |}
        -> pred_order P' P.
    
*)




(*

(** About sequential composition *)
Inductive prog_seq (plm : prog_lan_model) : Type :=
| seq_atom (S1 : syntax plm)
| seq_comp (S1 S2 : prog_seq plm).

Fixpoint desem_seq (plm : prog_lan_model) (P : prog_seq plm) : 
    stt plm -> stt plm :=
    match P with
    | seq_atom S1 => ⟦ S1 ⟧
    | seq_comp S1 S2 => (desem_seq S2) ◦ (desem_seq S1)
    end.

Definition seq_cpt (plm : prog_lan_model) : prog_lan_model :=
{|
    stt := stt plm;
    syntax := prog_seq plm;
    desem := @desem_seq plm;
|}.



*)
