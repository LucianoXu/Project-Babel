(** * nd_seq_study.v  *)

From Ranko Require Import TerminalDogma.premises 
                          TerminalDogma.Extensionality.

From Ranko Require Import QTheory NaiveSet.

From Coq Require Import Classical Arith Relations Reals.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section NondetProg.

(* type of state *)
Variable (X : Type).

(* type of program *)
Variable (Prog : Type).
Parameter seq_comb : Prog -> Prog -> Prog.
Notation " P1 ; P2 " := (seq_comb P1 P2) (at level 5).

Parameter sem_point : Prog -> X -> 𝒫(X).
Notation " ⦗ P ⦘ " := (sem_point P).
Notation " ⦗ P ⦘ ( x ) " := (sem_point P x).

Definition sem (P : Prog) : 𝒫(X) -> 𝒫(X) :=
    fun (A : 𝒫(X)) => ⋃ { ⦗ P ⦘ (x), x | x ∈ A }.

Notation " ⟦ P ⟧ " := (sem P).
Notation " ⟦ P ⟧ ( x ) " := (sem P x).
    
Hypothesis sem_point_seq : forall (P1 P2 : Prog),

        ⦗ P1 ; P2 ⦘ = fun A => ⋃ { ⦗ P2 ⦘ (x), x | x ∈ ⦗ P1 ⦘ (A) }.



Theorem seq_comp :  forall (P1 P2 : Prog),

        ⟦ P1 ; P2 ⟧ = ⟦ P2 ⟧ ◦ ⟦ P1 ⟧.

Proof. 
    move => P1 P2. 
    apply functional_extensionality => A.
    rewrite /sem.
    rewrite sem_point_seq.

    (* set equality *)
    rewrite sep_big_union_dist.
    rewrite -big_union_sep_dist.
    rewrite sep_union_dist.
    rewrite /f_map.
    by [].
Qed.
    
    