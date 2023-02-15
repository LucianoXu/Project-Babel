(** Nondet.v : describing nondeterministic quantum programs 
            with Feng Yuan *)
(*

From Babel Require Import TerminalDogma 
                          ExtraDogma.Extensionality.

From Babel Require Import QTheory
                          NaiveSet.

From Coq Require Import Classical
                        Reals.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Module QTheorySet_Nondet_Fun (Import QTB : QTheoryBasicType).

Definition PDensitySet (H : HilbertSpace) := 𝒫(𝒟(H)⁻).
Definition PDensitySet_uni (H : HilbertSpace): 𝒫(𝒟(H)⁻) := 𝕌.

Definition union_set (H : HilbertSpace) (A B : 𝒫(𝒟(H)⁻)) := A ∪ B.
Notation " A '∪' B " := (@union_set _ A B).

Definition add_set (H : HilbertSpace) (A B : 𝒫(𝒟(H)⁻)) :=
    A @ (@add_PDenOpt H) @ B.
Notation " A + B " := (@add_set _ A B).

    
Lemma add_set_uni_l : forall {H : HilbertSpace} (s : 𝒫(𝒟( H )⁻)), 
    𝕌 + s = 𝕌.
Proof.
Admitted.

Lemma add_set_uni_r : forall {H : HilbertSpace} (s : 𝒫(𝒟( H )⁻)), 
    s + 𝕌 = 𝕌.
Proof.
Admitted.

Definition InitSttS (qs : QvarScope)(qv_init : qs)(rho_s : 𝒫(𝒟( qs )⁻)) :=
    (InitStt qv_init) @ rho_s.

Definition UapplyS (qs : QvarScope)(qv_U : qs)
    (U : UnitaryOpt qv_U) (rho_s : 𝒫(𝒟( qs )⁻)) :=
    (Uapply U) @ rho_s.

Definition MapplyS (qs : QvarScope)(qv_M : qs)
    (M : MeaOpt qv_M) (r : bool) (rho_s : 𝒫(𝒟( qs )⁻)) :=
    (Mapply M r) @ rho_s.

(*
Lemma MapplyS_repeat : forall (qs : QvarScope)
    (qv_M : qs) (m : MeaOpt qv_M) 
    (rho_s : 𝒫(𝒟( qs )⁻)) (result : bool), 
    MapplyS m result (MapplyS m result rho_s ) 
    = MapplyS m result rho_s .
Proof.
Admitted.
*)

Definition scalar_convex_combS (qs : QvarScope) (p : [0, 1]R)
    (rho_s1 rho_s2 : 𝒫(𝒟( qs )⁻)) : 𝒫(𝒟( qs )⁻) :=
    rho_s1 @ (scalar_convex_comb p) @ rho_s2.
Notation " A [ p '⊹' ] B " := (@scalar_convex_combS _ p A B)
    (at level 10).



End QTheorySet_Nondet_Fun.


Module QNondetProg 

(** This Module relies on a basic theory of quantum. *)
                     (Import QTB : QTheoryBasicType).

Module Import QTheorySet_Nondet := QTheorySet_Nondet_Fun QTB.

Declare Scope QNondetP_scope.
Open Scope QNondetP_scope.


(** A legal parallel quantum program (after syntax check) *)
Inductive prog (qs : QvarScope): Type :=
| skip_
| init_ (qv : qs) 
| unitary_ (qv : qs) (U : UnitaryOpt qv)
| seq_ (S1 S2 : prog qs)
| prob_ (S1 S2 : prog qs) (p : [0, 1]R)
| nondet_ (S1 S2 : prog qs)
| if_ (qv_m : qs) (m : MeaOpt qv_m) (S0 S1: prog qs)
| while_ (qv_m : qs) (m : MeaOpt qv_m) (S0 : prog qs).

Notation " 'Skip' " := (@skip_ _) : QNondetP_scope.
Notation " qv <- '0' " := (@init_ _ qv) (at level 10) : QNondetP_scope.
Notation " qv *= U " := (@unitary_ _ qv U) (at level 10) : QNondetP_scope.
Notation " S1 ;; S2 " := (@seq_ _ S1 S2) 
    (at level 95, right associativity) : QNondetP_scope.
Notation " S1 [ p ⊕ ] S2 " := (@prob_ _ S1 S2 p) : QNondetP_scope.
Notation " S1 □ S2 " := (@nondet_ _ S1 S2) (at level 5) : QNondetP_scope.
Notation " 'If' m [[ qv_m ]] 'Then' S0 'Else' S1 'End' " := 
    (@if_ _ qv_m m S0 S1) (at level 90) : QNondetP_scope.
Notation " 'While' m [[ qv_m ]] 'Do' S0 'End' " := 
    (@while_ _ qv_m m S0) (at level 90) : QNondetP_scope.


Reserved Notation "⟦ P ⟧ ( rho_s )".

Fixpoint DeSem (qs : QvarScope) (P : prog qs) (rho_s : 𝒫(𝒟(qs)⁻)) 
    : 𝒫(𝒟(qs)⁻) :=
    match P with
    | Skip => 
        rho_s

    | qv <- 0 => 
        InitSttS qv rho_s

    | qv *= U => 
        UapplyS U rho_s

    | S1 ;; S2 => 
        ⟦ S2 ⟧ ( ⟦ S1 ⟧ (rho_s) )

    | S1 [ p ⊕ ] S2 => 
        ⟦ S1 ⟧ (rho_s) [ p ⊹ ] ⟦ S2 ⟧ (rho_s)

    | S1 □ S2 => 
        ⟦ S1 ⟧ (rho_s) ∪ ⟦ S2 ⟧ (rho_s)
        
    | If m [[ qv_m ]] Then S0 Else S1 End
        => ⟦ S0 ⟧ (MapplyS m true rho_s) + ⟦S1⟧ (MapplyS m false rho_s)

    | _ => rho_s
    end
    where " ⟦ P ⟧ ( rho_s ) " := (DeSem P rho_s).


End QNondetProg.

*)