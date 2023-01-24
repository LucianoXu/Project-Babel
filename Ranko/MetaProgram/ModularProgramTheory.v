(** ModularProgramTheory.v *)
From Ranko Require Import TerminalDogma.premises 
                          TerminalDogma.Extensionality.


From Coq Require Import Classical.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** program language model (typed) 
    stt : the variable state type considered in this model *)
Record prog_lan_model (stt : Type) : Type := {

    (* the program syntax type *)
    prog : Type;
    
    (* the denotational semantics of the program *)
    desem : prog -> stt -> stt;

}.

Notation " ⟦ P ⟧ " := (desem P).
Notation " ⟦ P ⟧ ( s ) " := (desem P s).


(** definition of correctness *)

Definition pred (stt : Type) := stt -> Prop.

Definition pred_order {stt : Type} (P Q : pred stt) : Prop := 
    forall s : stt, P s -> Q s.

Record correctness_formula {stt : Type} (plm : prog_lan_model stt) := {
    pre_cond : pred stt;
    mid_prog : prog plm;
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
            (P : pred stt) (S0 : prog plm) (Q : pred stt) :=
    semantic_correct {| pre_cond := P; mid_prog := S0; post_cond := Q |}
    /\ forall P', semantic_correct {| pre_cond := P; mid_prog := S0; post_cond := Q |}
        -> pred_order P' P.
    





(*

(** About sequential composition *)
Inductive prog_seq (plm : prog_lan_model) : Type :=
| seq_atom (S1 : prog plm)
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
    prog := prog_seq plm;
    desem := @desem_seq plm;
|}.



*)