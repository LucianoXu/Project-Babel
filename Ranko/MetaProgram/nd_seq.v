(** * nd_seq.v  *)

From Ranko Require Import TerminalDogma.premises 
                          TerminalDogma.Extensionality.

From Ranko Require Import NaiveSet.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Module Type NondetSeqProgType.

(* type of state *)
Parameter X : Type.

(* type of program syntax *)
Parameter Prog : Type.

(* there exists a program structure called sequential composition *)
Parameter seq_comb : Prog -> Prog -> Prog.
Notation " P1 ; P2 " := (seq_comb P1 P2) (at level 5).

(* the point wise semantics *)
Parameter sem_point : Prog -> X -> 𝒫(X).
Notation " ⦗ P ⦘ " := (sem_point P).
Notation " ⦗ P ⦘ ( x ) " := (sem_point P x).

(* the nondeterministic semantics *)
Parameter sem : Prog -> 𝒫(X) -> 𝒫(X).
Notation " ⟦ P ⟧ " := (sem P).
Notation " ⟦ P ⟧ ( x ) " := (sem P x).


(** two requirements on the semantics *)
Axiom sem_rel : 
    forall P, ⟦ P ⟧ = ⋃ ◦ ⦗ P ⦘[<].

Axiom sem_point_seq : 
    forall P1 P2, ⦗ P1 ; P2 ⦘ = ⋃ ◦ ⦗ P2 ⦘ [<] ◦ ⦗ P1 ⦘.

End NondetSeqProgType.




Module NondetSeqProgTheory (Import NSP : NondetSeqProgType).

Theorem seq_comp : forall (P1 P2 : Prog),

        ⟦ P1 ; P2 ⟧ = ⟦ P2 ⟧ ◦ ⟦ P1 ⟧.

Proof.
    move => P1 P2.
    rewrite !sem_rel.
    rewrite sem_point_seq.

    (* set function equality *)
    rewrite -[RHS]fun_assoc
         [(⋃ ◦ ⦗ P2 ⦘ [<]) ◦ ⋃] fun_assoc.
    rewrite mapR_bigU_swapF.
    rewrite -bigU_fun_distF.
    rewrite -[⋃ ◦ ⦗ P2 ⦘ [<] ◦ ⦗ P1 ⦘]fun_assoc.
    rewrite -double_mapRF.
    by rewrite fun_assoc.
Qed.
    
End NondetSeqProgTheory.
