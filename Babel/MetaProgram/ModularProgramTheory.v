(** ModularProgramTheory.v *)
From Babel Require Import TerminalDogma 
                          ExtraDogma.Extensionality
                          ExtraDogma.AllDecidable
                          POrderFacility.

From Babel Require Import Ranko
                            ExtensionalityCharacter
                            AllDecidableCharacter
                            ClassicalCharacter.

From Coq Require Import Relations Classical.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Coercion decide_oracle : Sortclass >-> bool.

Notation "⌈ P ⇒ Q ⌉" := (forall s, P s ⊑ Q s).


Lemma fun_impl_trans (X : Type) (Y : poset) (P Q R : X -> Y) : 

    ⌈ P ⇒ Q ⌉ -> ⌈ Q ⇒ R ⌉ -> ⌈ P ⇒ R ⌉.

Proof. ranko. transitivity (Q s); ranko. Qed.

Import FunPointwiseOrder.CanonicalStruct.

Module LangModel.


(** Meta-language type 
    Specifies the language specifications for a backward semantics language 
    model. *)
Record metaType : Type := {
    (** The type of data structure. *)
    Stt : Type;
    (** The type of assertions (complete lattice required). *)
    Asn : clattice;
    (** The type of satisfaction value (complete lattice required). *)
    SVal : clattice;
    (** The function to evaluate the satisfaction value. *)
    sat_eval : Asn -> Stt -> SVal;
    (** The consistency between [Asn] order and [SVal] order *)
    sat_eval_consistent : 
        forall (P Q : Asn), P ⊑ Q <-> ⌈ sat_eval P ⇒ sat_eval Q ⌉;
}.

(** program language model (with meta type) *)
Record feature (mT : metaType) : Type := {

    (* the program syntax type *)
    syntax : Type;

    (* the denotational semantics of the program *)
    wp : syntax -> Asn mT -> Asn mT;

    prog_monotonic : forall p: syntax, MonotonicFun.mixin_of (wp p);
}.

(** wp extensionality in the meta level *)
Axiom wp_extensionality :
        forall (mT : metaType) (L : feature mT) (p q : syntax L), 
            wp p = wp q -> p = q.


Lemma prog_porderMixin (mT : metaType) (L : feature mT): 
    Poset.mixin_of (syntax L).
Proof.
    refine (@Poset.Mixin (syntax L) (fun s1 s2 => wp s1 ⊑ wp s2) _).
    constructor.
    rewrite /reflexive. ranko. by reflexivity.
    rewrite /transitive. ranko. by transitivity (wp y x0).
    rewrite /antisymmetric. ranko.
        apply wp_extensionality. 
        apply poset_antisym. ranko. ranko.
Defined.

Canonical prog_porder (mT : metaType) (L : feature mT) := 
    Poset (syntax L) (@prog_porderMixin mT L).

End LangModel.

Import LangModel.





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

Lemma prog_monotonic (mT : metaType) : 
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


Definition specMod (mT : metaType) : feature mT := {|
    LangModel.syntax := syntax mT;
    LangModel.wp := @wp mT;
    LangModel.prog_monotonic := @prog_monotonic mT;
|}.


Module RefinementFactory.
(** Language model obtained after equiping it with specification refinement. *)
(** The program syntax. *)
Inductive prog_with_spec (mT : metaType) (L : feature mT) : Type :=
| prog_part (p : LangModel.syntax L)
| spec_part (s : LangModel.syntax (specMod mT)).

(** The wp semantics. *)
Definition wp_with_spec (mT : metaType) (L : feature mT) : 
        prog_with_spec L -> Asn mT -> Asn mT :=
    fun p => fun R =>
        match p with
        | prog_part p' => LangModel.wp p' R
        | spec_part s => wp s R
        end.

(** The prog_monotonic proof *)
Lemma prog_with_spec_monotonic (mT : metaType) (L : feature mT) : 
        forall p: prog_with_spec L, MonotonicFun.mixin_of (wp_with_spec p).
Proof.
    case.
    ranko.
    by apply prog_monotonic.
Qed.

Definition type (mT : metaType) (L : feature mT) : feature mT := {|
    LangModel.syntax := prog_with_spec L;
    LangModel.wp := @wp_with_spec _ L;
    LangModel.prog_monotonic := @prog_with_spec_monotonic _ L;
|}.

End RefinementFactory.




Module Exports.

Notation "P ‖ Q" := {| pre := P; post := Q |} (at level 50).
(* #[export] Hint Unfold RefinementFactory.wp_with_spec : magic_book. *)

End Exports.

End SpecMod.
Import SpecMod.Exports.



Theorem Theorem_Refinement_A (mT : metaType) 
        (L : feature mT) (P Q : Asn mT) 
        (s : syntax (SpecMod.RefinementFactory.type L)): 

        (SpecMod.RefinementFactory.spec_part L (P ‖ Q) 
            : (prog_porder (SpecMod.RefinementFactory.type L))) ⊑ s 
            <-> P ⊑ wp s Q.
Proof. split.
    * ranko.
    refine (poset_trans _ (H Q)).
    rewrite /SpecMod.wp.
    replace (decide_oracle (SpecMod.post (P ‖ Q) ⊑ Q))
        with true.
        + by reflexivity.
        + symmetry. rewrite decide_oracle_true. ranko. 
            by reflexivity.
    *
        ranko.
        rewrite /SpecMod.wp.
        destruct (decide_oracle (SpecMod.post (P ‖ Q) ⊑ x)) eqn: E.
        + move: H E. ranko.
            apply (poset_trans H).
            apply SpecMod.RefinementFactory.prog_with_spec_monotonic.
            by apply E.
        + apply (CLattice.join_prop (CLattice.class (Asn mT))).
            ranko.
Qed.
            

Theorem Theorem_Refinement_B (mT : metaType) 
        (L : feature mT) (P Q : Asn mT) 
        (s : syntax (SpecMod.RefinementFactory.type L)): 

        P ⊑ wp s Q <-> ⌈ sat_eval P ⇒ sat_eval (wp s Q) ⌉.

Proof. ranko. Qed.


Axiom assign_feature : forall (mT : metaType), feature mT.
Axiom seq_feature : forall (mT : metaType), feature mT -> feature mT.

Definition lang (mT : metaType) := seq_feature (assign_feature mT).
Definition lang' (mT : metaType) := seq_feature (seq_feature (assign_feature mT)).

Inductive is_lang (mT : metaType) : feature mT -> Prop := 
| is_assign : is_lang (assign_feature mT) 
| is_seq (L : feature mT) (H : is_lang L) : is_lang (seq_feature L)

| is_spec : is_lang (SpecMod.specMod mT).

(** Axiom is_lange spec : this is very convenient!*)



Theorem Theorem_Refinement' (mT : metaType) 
        (L : feature mT) (s : syntax L) (P Q : Asn mT) : 
        wp (P ‖ Q : syntax (SpecMod.specMod _)) ⊑ wp (s)
            <-> P ⊑ wp s Q.
Proof. split.
    * ranko. refine (poset_trans _ (H Q)).
        rewrite /SpecMod.wp.
        replace (decide_oracle (SpecMod.post (P ‖ Q) ⊑ Q)) with true.
        by reflexivity.
        ranko. by reflexivity.
    * ranko. rewrite /SpecMod.wp.
        case E: (decide_oracle (SpecMod.post (P ‖ Q) ⊑ x)); move : E.
        + ranko. apply (prog_monotonic s) in E.
        by transitivity (wp s Q).
        + ranko.
Qed. 


















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
