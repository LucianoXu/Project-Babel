(** * Parallel.v : describing parallel quantum programs *)

From Ranko Require Import TerminalDogma.premises 
                          TerminalDogma.Extensionality.

From Ranko Require Import QTheory.

From Coq Require Import Classical Arith Relations Reals.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Module QParallelProg 

(** This Module relies on a basic theory of quantum, *)
                     (QTB : QTheoryBasicType) 

(** and a theory to combine sets into quantums. *)
                     (QTS : QTheorySetType QTB).

(** Get the extended theory of quantum sets *)
Module Import QTS_ext := QTheorySet QTB QTS.

Declare Scope QPP_scope.
Open Scope QPP_scope.

(** A legal parallel quantum program (after syntax check) *)
Inductive prog (qs : QvarScope): Type :=
| skip_
| abort_ 
| init_ (qv : qs) 
| unitary_ (qv : qs) (U : UnitaryOpt qv)
| if_ (qv_m : qs) (m : MeaOpt qv_m) (S0 S1: prog qs)
| while_ (qv_m : qs) (m : MeaOpt qv_m) (S0 : prog qs)
| seq_ (S1 S2 : prog qs)
| prob_ (p : [0, 1]R) (S1 S2 : prog qs)
| nondet_ (S1 S2 : prog qs)
| atom_ (S0 : prog qs)
| parallel_ (S1 S2 : prog qs).

Notation " 'Skip' " := (@skip_ _) : QPP_scope.
Notation " 'Abort' " := (@abort_ _) : QPP_scope.
Notation " qv <- '0' " := (@init_ _ qv) (at level 10) : QPP_scope.
Notation " qv *= U " := (@unitary_ _ qv U) (at level 10) : QPP_scope.
Notation " 'If' m [[ qv_m ]] 'Then' S0 'Else' S1 'End' " := 
    (@if_ _ qv_m m S0 S1) (at level 90) : QPP_scope.
Notation " 'While' m [[ qv_m ]] 'Do' S0 'End' " := 
    (@while_ _ qv_m m S0) (at level 90) : QPP_scope.
Notation " S1 ;; S2 " := (@seq_ _ S1 S2) 
    (at level 95, right associativity) : QPP_scope.
Notation " S1 [ p ⊕ ] S2 " := (@prob_ _ p S1 S2) 
    (format "S1  [ p  ⊕ ]  S2"): QPP_scope.
Notation " S1 □ S2 " := (@nondet_ _ S1 S2) (at level 3): QPP_scope.
Notation " << P >> " := (@atom_ _ P) : QPP_scope.
Notation " [ S1 // S2 ] " := (@parallel_ _ S1 S2) (at level 5) : QPP_scope.

Fixpoint non_parallel {qs : QvarScope} (P : prog qs) : bool :=
    match P with 
    | [S1 // S2] => false
    | If m [[ qv_m ]] Then S0 Else S1 End => non_parallel S0 && non_parallel S1
    | While m [[ qv_m ]] Do S0 End => non_parallel S0
    | S1 ;; S2 => non_parallel S1 && non_parallel S2
    | _ => true
    end.

(** Get the quantum variable of the program *)
Fixpoint qvar_of_prog {qs : QvarScope} (S0 : prog qs) : qs :=
    match S0 with
    | Skip => em_var _
    | Abort => em_var _
    | qv <- 0 => qv
    | qv *= _ => qv
    | If _ [[ qv_m ]] Then S0 Else S1 End
        => qv_m [+] (qvar_of_prog S0) [+] (qvar_of_prog S1)
    | While _ [[ qv_m ]] Do S0 End
        => qv_m [+] (qvar_of_prog S0)
    | S1;;S2 => (qvar_of_prog S1) [+] (qvar_of_prog S2)
    | S1 [ p ⊕ ] S2 => (qvar_of_prog S1) [+] (qvar_of_prog S2)
    | S1 □ S2 =>(qvar_of_prog S1) [+] (qvar_of_prog S2)
    | <<S0>> => qvar_of_prog S0
    | [ S1 // S2 ] => (qvar_of_prog S1) [+] (qvar_of_prog S2)
    end.
Coercion qvar_of_prog : prog >-> Qvar.


Fixpoint seq_Head {qs : QvarScope} (S0 : prog qs) : prog qs :=
    match S0 with
    | P0 ;; P1 => seq_Head P0
    | _ => S0
    end.
Fixpoint seq_Tail {qs : QvarScope} (S0 : prog qs) : option (prog qs) :=
    match S0 with
    | P0 ;; P1 => match seq_Tail P0 with
                  | None => Some P1
                  | Some Q => Some (Q ;; P1)
                  end
    | _ => None
    end.

(** make a choice for the parallel component program *)
Definition Step {qs : QvarScope} (S1 S2: prog qs) 
              (b : bool) : prog qs :=
    if b then
        match seq_Tail S1 with
        | None => (* if S1 is not a sequence *)
            match S1 with
            | If m [[ qv_m ]] Then P0 Else P1 End => 
                If m [[ qv_m ]] Then [ P0 // S2 ] Else [ P1 // S2 ] End
            | While m [[ qv_m ]] Do P0 End =>
                If m [[ qv_m ]] Then [ P0 ;; While m [[qv_m]] Do P0 End // S2 ]
                                Else [ Skip // S2] End
            | _ => S1 ;; [ Skip // S2 ]
            end 
        (** Note that here we give a different interpretation of 
            nested parallel composition 
            We consider the inner parallel composition as a 'atomic' action
            performed in parallel *)
        | Some Q => seq_Head S1 ;; [ Q // S2 ]
        end
    else
        match seq_Tail S2 with
        | None => (* if S2 is not a sequence *)
            match S2 with
            | If m [[ qv_m ]] Then P0 Else P1 End => 
                If m [[ qv_m ]] Then [ S1 // P0 ] Else [ S1 // P1 ] End
            | While m [[ qv_m ]] Do P0 End =>
                If m [[ qv_m ]] Then [ S1 // P0 ;; While m [[qv_m]] Do P0 End ]
                                Else [ S1 // Skip] End
            | _ => S2 ;; [ S1 // Skip ]
            end 
        (** Note that here we give a different interpretation of 
            nested parallel composition *)
        | Some Q => seq_Head S2 ;; [ S1 // Q ]
    end.

(* ############################################################ *)
(** ** Operational Semantics *)

(** The configuration of computation *)
Inductive cfg (qs : QvarScope): Type :=
| Srho_pair (S0 : prog qs) (rho : 𝒟( qs )⁻ )
| Terminated (rho : 𝒟( qs )⁻ ).
Notation " <{ S0 , rho }> " := (@Srho_pair _ S0 rho ) : QPP_scope.
Notation " <{ '↓' , rho }> " := (@Terminated _ rho) : QPP_scope.



Reserved Notation " c1 -=> c2 " (at level 20).
Reserved Notation " c1 -=>* c2 " (at level 20).


Inductive opSem_trans qs : cfg qs -> cfg qs -> Prop :=
| skip_step rho : 
    <{ Skip, rho }> -=> <{ ↓, rho }>

| abort_step rho:
    <{ Abort, rho }> -=> <{ ↓, 𝟎 }>

| init_step qv rho:
    <{ qv <- 0, rho }> -=> <{ ↓, InitStt qv rho }>

| unitary_step qv U rho:
    <{ qv *= U, rho }> -=> <{ ↓, Uapply U rho }>

| if_step_Y qv_m m S0 S1 rho:
    <{ If m [[qv_m]] Then S0 Else S1 End, rho }>
    -=> <{ S0, Mapply m true rho }>

| if_step_N qv_m m S0 S1 rho:
    <{ If m [[qv_m]] Then S0 Else S1 End, rho }>
        -=> <{ S1, Mapply m false rho }>

| while_step_Y qv_m m S0 rho:
    <{ While m [[qv_m]] Do S0 End, rho }>
        -=> <{ S0 ;; While m [[qv_m]] Do S0 End, Mapply m true rho }>

| while_step_N qv_m m S0 rho:
    <{ While m [[qv_m]] Do S0 End, rho }>
        -=> <{ ↓, Mapply m true rho }>

| seq_step_p S0 St S1 rho0 rho1:
    <{ S0, rho0 }> -=> <{ St, rho1 }>
    -> <{ S0 ;; S1, rho0 }> -=> <{ St ;; S1, rho1 }>

| seq_step_t S0 S1 rho0 rho1:
    <{ S0, rho0 }> -=> <{ ↓, rho1 }>
        -> <{ S0 ;; S1, rho0 }> -=> <{ S1, rho1 }>

| atom_step S0 rho0 rho1 :
    <{ S0, rho0 }> -=>* <{ ↓, rho1 }>
        -> <{ <<S0>>, rho0 }> -=> <{ ↓, rho1 }>

| parallel_step_0 S0 S1 rho :
    <{ [S0 // S1], rho }> -=> <{ Step S0 S1 true, rho }>

| parallel_step_1 S0 S1 rho :
    <{ [S0 // S1], rho }> -=> <{ Step S0 S1 false, rho }>

where " c1 -=> c2 " := (opSem_trans c1 c2)
    and " c1 -=>* c2 " := (clos_trans _ (@opSem_trans _) c1 c2).



(* ############################################################ *)
(** ** Denotational Semantics *)

Reserved Notation " ⦗ P , n ⦘ ( rho ) " 
    (at level 10, rho at next level, format "⦗  P ,  n  ⦘ ( rho )").
    
Reserved Notation " ⦗ P , n ⦘ " 
    (at level 10, format "⦗  P ,  n  ⦘").

Reserved Notation " ⦗ ↓ ⦘ ( rho ) " 
    (at level 10, rho at next level, only printing, format "⦗  ↓  ⦘ ( rho )").

Reserved Notation " ⦗ ↓ ⦘" 
    (at level 10, only printing, format "⦗  ↓  ⦘").

(** Define the denotational semantics of calculating n steps 
    parameter :
        [P : option (prog qs)], if [P] is [None] then the program is 
            terminated.*)
Fixpoint deSemN_point {qs : QvarScope} (P : option (prog qs)) (n : nat)
    (rho : 𝒟( qs )⁻) : 𝒫(𝒟( qs )⁻) :=
    match P with
    | None => {{ rho }}
    | Some P => 
        match n with
        | 0 => 𝕌
        | n'.+1 => 
            match P with
            | Skip => 
                {{ rho }}

            | Abort => 
                𝕌 
                (** Note : universal set is necessary here. Otherwise, it's
                    hard to construct the infimum set. *)

            | qv <- 0 => 
                {{ InitStt qv rho }}

            | qv *= U => 
                {{ Uapply U rho }}

            | If m [[ qv_m ]] Then P0 Else P1 End =>
                (⦗ P0, n' ⦘ ( Mapply m true rho ))
                + (⦗ P1, n' ⦘ ( Mapply m false rho ))

            | While m [[ qv_m ]] Do P0 End  =>
                ⦗ P0;; While m [[ qv_m ]] Do P0 End, n' ⦘ (Mapply m true rho)
                + {{ Mapply m false rho }}

            | S1 ;; S2 => 
                ⋃ { ⦗ S2, n' ⦘ (rho') , rho' | rho' ∈ ⦗ S1, n' ⦘ (rho) }

            | S1 [ p ⊕ ] S2 =>
                (⦗ S1, n' ⦘( rho )[ p ⊕ ] ⦗ S2, n' ⦘( rho ))%QTS

            | S1 □ S2 =>
                ⦗ S1, n' ⦘(rho) ∪ ⦗ S2, n' ⦘(rho)

            | << P >> => 
                ⦗ P, n' ⦘ (rho)

            | [ S1 // S2 ] => 
                (** Note that here we give a different interpretation of 
                    nested parallel composition *)
                (⦗ Step S1 S2 true, n' ⦘ (rho))
                ∪ (⦗ Step S1 S2 false, n' ⦘ (rho))

            end
        end
    end
    where " ⦗ P , n ⦘ " := (deSemN_point (Some P) n) : QPP_scope and
    " ⦗ P , n ⦘ ( rho ) " := (deSemN_point (Some P) n rho) : QPP_scope.

Notation " ⦗ ↓ ⦘ ( rho ) " := (deSemN_point None _ rho) :QPP_scope.
Notation " ⦗ ↓ ⦘ " := (deSemN_point None _ ) :QPP_scope.


Definition deSemN {qs : QvarScope} (P : option (prog qs)) (n : nat)
    (rho_s : 𝒫(𝒟( qs )⁻)) : 𝒫(𝒟( qs )⁻) :=
    match P with
    | None => rho_s
    | Some P =>
        ⋃ ⦗ P, n ⦘ [@] (rho_s)
    end.

Notation " ⟦ P , n ⟧ " := (deSemN (Some P) n)
    (at level 10, format "⟦  P ,  n  ⟧") : QPP_scope.

Notation " ⟦ P , n ⟧ ( rho_s ) " := (deSemN (Some P) n rho_s)
    (at level 10, rho_s at next level, 
    format "⟦  P ,  n  ⟧ ( rho_s )") : QPP_scope.
    
Notation " ⟦ ↓ ⟧ ( rho_s ) " := (deSemN None _ rho_s )
    (only printing, format "⟦  ↓  ⟧ ( rho_s )") : QPP_scope.



Lemma deSem0_nem (qs : QvarScope) P (rho_s : 𝒫(𝒟( qs )⁻)) :

    rho_s <> ∅ -> ⟦ P , 0 ⟧ (rho_s) = 𝕌.

Proof.
    rewrite /deSemN /deSemN_point /f_map //=. by apply big_union_sgl_nem.
Qed.

Lemma deSem0_em (qs : QvarScope) (P : prog qs) n:
    
    ⟦ P , n ⟧ (∅) = ∅.

Proof.
Admitted.


Section DeSemPointStep.

Variable (qs : QvarScope) (rho : 𝒟( qs )⁻).


Lemma deSemN_seq_point S1 S2 n:

            ⦗ S1 ;; S2, n.+1 ⦘ (rho) = 
                ⋃ { ⦗ S2, n ⦘ (rho') , rho' | rho' ∈ ⦗ S1, n ⦘ (rho) }.

Proof. by []. Qed.


Lemma deSemN_seq_point_fun (S1 S2 : prog qs) n:

            ⦗ S1 ;; S2, n.+1 ⦘ = 
                fun rho => ⋃ { ⦗ S2, n ⦘ (rho') , rho' | rho' ∈ ⦗ S1, n ⦘ (rho) }.

Proof. by []. Qed.


Lemma deSemN_if_point qv_m m S0 S1 n:

    ⦗ If m [[ qv_m ]] Then S0 Else S1 End, n.+1 ⦘ (rho) = 
        (⦗ S0, n ⦘ ( Mapply m true rho ))
        + (⦗ S1, n ⦘ ( Mapply m false rho )).

Proof. by []. Qed.

Lemma deSemN_if_point_fun qv_m m (S0 S1 : prog qs) n:

    ⦗ If m [[ qv_m ]] Then S0 Else S1 End, n.+1 ⦘= 
        fun x => (⦗ S0, n ⦘ ( Mapply m true x ))
        + (⦗ S1, n ⦘ ( Mapply m false x )).

Proof. by []. Qed.

(* 
Lemma deSemN_if {qs : QvarScope} qv_m m S0 S1: 
        forall (rho_s : 𝒫(𝒟( qs )⁻)) n,

            ⟦ If m [[ qv_m ]] Then S0 Else S1 End , n.+1 ⟧ (rho_s)
            = ⟦ S0, n ⟧ (MapplyS m true rho_s) 
                + ⟦ S1, n ⟧ (MapplyS m false rho_s).

Proof. by []. Qed.
*)

Lemma deSemN_while_point qv_m m S0 n:

            ⦗ While m [[ qv_m ]] Do S0 End, n.+1 ⦘ (rho) = 
                (⦗ S0 ;; While m [[ qv_m ]] Do S0 End, n ⦘ ( Mapply m true rho ))
                + {{ Mapply m false rho }}.

Proof. by []. Qed.

(*
Lemma deSemN_while {qs : QvarScope} qv_m m S0:
        forall (rho_s : 𝒫(𝒟( qs )⁻)) n, 
        
            ⟦ While m [[ qv_m ]] Do S0 End, n.+1 ⟧(rho_s)
            = ⟦ S0;; While m [[ qv_m ]] Do S0 End, n ⟧ (MapplyS m true rho_s)
                + (MapplyS m false rho_s).

Proof. by []. Qed.
*)

Lemma deSemN_prob_point p S1 S2 n:

            ⦗ S1 [ p ⊕ ] S2, n.+1 ⦘ (rho)
            = (⦗ S1, n ⦘(rho) [ p ⊕ ] ⦗ S2, n⦘(rho))%QTS.

Proof. by []. Qed.

(******)

Lemma deSemN_nondet_point S1 S2 n:
        
            ⦗ S1 □ S2, n.+1 ⦘ (rho)
            = ⦗ S1, n ⦘(rho) ∪ ⦗ S2, n ⦘(rho).

Proof. by []. Qed.

(******)

Lemma deSemN_atom_point P n: 
        
            ⦗ <<P>>, n.+1 ⦘ (rho) = ⦗ P, n ⦘ (rho).

Proof. by []. Qed.

(******)

Lemma deSemN_parallel_point S1 S2 n: 
        
            ⦗ [ S1 // S2 ], n.+1 ⦘ (rho) 
            = (⦗ Step S1 S2 true, n ⦘ (rho))
                ∪ (⦗ Step S1 S2 false, n ⦘ (rho)).

Proof. by []. Qed.

End DeSemPointStep.



Section DeSemStep.

Variable (qs : QvarScope) (rho_s : 𝒫(𝒟( qs )⁻)).


Lemma deSemN_skip n:

            ⟦ Skip, n.+1 ⟧(rho_s) = rho_s.

Proof. 
    rewrite /deSemN. case (em_classic rho_s).
    move => ->. apply deSem0_em.
    rewrite /f_map => H //=. by apply big_union_rei.
Qed.


(***********************************)
(** The gadget for abort semantics *)

Lemma rho_s_em_em:

        rho_s = ∅ -> { _ : 𝒟(qs)⁻ | rho_s <> ∅ } = ∅.

Proof.
    move => ->.
    replace (∅ ≠ ∅) with False => //.
    by apply propositional_extensionality.
Qed.

Lemma rho_s_nem_U:

        rho_s <> ∅ -> { _ : 𝒟(qs)⁻ | rho_s <> ∅ } = 𝕌.

Proof.
    move => H.
    replace (rho_s <> ∅) with True => //.
    by apply propositional_extensionality.
Qed.


(***********************************)

Lemma deSemN_abort n:

            ⟦ Abort, n.+1 ⟧(rho_s) = { _ | rho_s <> ∅ }.

(** Note that rho_s not empty is needed for this argument *)

Proof. 
    rewrite /deSemN.
    rewrite /f_map => //=.
    case (em_classic rho_s).

    move => H. rewrite big_union_sgl_em //.
    by rewrite rho_s_em_em.

    move => H. rewrite big_union_sgl_nem //.
    by rewrite rho_s_nem_U.
Qed.

Lemma deSemN_init qv n:
 
            ⟦ qv <-0 , n.+1 ⟧(rho_s) = InitSttS qv rho_s.

Proof. 
    rewrite /InitSttS /deSemN /f_map //=. 
    by apply big_union_fun_rei.
Qed.

Lemma deSemN_unitary qv U n:
 
            ⟦ qv *= U , n.+1 ⟧(rho_s) = UapplyS U rho_s.

Proof. 
    rewrite /UapplyS /deSemN /f_map //=. 
    by apply big_union_fun_rei.
Qed.

Lemma deSemN_if qv_m m S0 S1 n:

            ⟦ If m [[ qv_m ]] Then S0 Else S1 End, n.+1 ⟧ (rho_s) 
            = ( ⟦ S0 , n ⟧ (MapplyS m true rho_s)
            + ⟦ S1 , n ⟧ (MapplyS m false rho_s) )%QTS.

Proof.
    rewrite /deSemN //=.
Admitted.

Lemma deSemN_while qv_m m S0 n:

            ⟦ While m [[ qv_m ]] Do S0 End, n.+1 ⟧ (rho_s) 
            = ( ⟦ S0 ;; While m [[ qv_m ]] Do S0 End, n ⟧ (MapplyS m true rho_s)
            + MapplyS m false rho_s )%QTS.

Proof.
    rewrite /deSemN //=.
Admitted.

Lemma deSemN_seq S0 S1 n:

            ⟦ S0 ;; S1, n.+1 ⟧ (rho_s) = ⟦ S1 , n ⟧ (⟦ S0, n ⟧ (rho_s)).

Proof.
    rewrite /deSemN /f_map.
    rewrite deSemN_seq_point_fun /f_map.

    rewrite sep_big_union_dist /f_map.
    rewrite sep_union_dist /f_map.

    rewrite big_union_dist.
    by rewrite big_union_sep_sep_dist.
Qed.

Lemma deSemN_prob p S1 S2 n:

        ⟦ S1 [p ⊕] S2, n.+1 ⟧(rho_s) 
        = (⟦ S1, n ⟧( rho_s )[ p ⊕ ] ⟦ S2, n ⟧( rho_s ))%QTS.

Proof.
Admitted.

Lemma deSemN_nondet S1 S2 n:
        ⟦ S1 □ S2, n.+1 ⟧(rho_s) = ⟦ S1, n ⟧(rho_s) ∪ ⟦ S2, n ⟧(rho_s).
Proof.
    rewrite /deSemN /f_map => //=.
    by rewrite union_big_union_dist.
Qed.

Lemma deSemN_atom P n:
        ⟦ <<P>>, n.+1 ⟧(rho_s) = ⟦ P, n ⟧(rho_s).
Proof. by []. Qed.


Lemma deSemN_parallel S1 S2 n:
        ⟦ [ S1 // S2], n.+1 ⟧(rho_s) 
        =  (⟦ Step S1 S2 true, n ⟧(rho_s)) ∪ (⟦ Step S1 S2 false, n ⟧(rho_s)).
Proof.
    rewrite /deSemN /f_map.
    by rewrite union_big_union_dist.
Qed.

End DeSemStep.


Section DeSemStepFun.

Variable (qs : QvarScope).

Lemma deSemN_skip_fun n:

            ⟦ (@skip_ qs) , n.+1 ⟧ = (fun rho_s => rho_s).
Proof.
    apply functional_extensionality => x.
    apply deSemN_skip.
Qed.

Lemma deSemN_abort_fun n:

            ⟦ (@abort_ qs), n.+1 ⟧ = (fun rho_s => { _ | rho_s <> ∅ }).

(** TODO try to use this technique elsewhere! *)

Proof. 
    apply functional_extensionality => x.
    apply deSemN_abort.
Qed.

Lemma deSemN_init_fun (qv : qs) n:
 
            ⟦ qv <-0 , n.+1 ⟧ = InitSttS qv.

Proof.
    apply functional_extensionality => x.
    apply deSemN_init.
Qed.

Lemma deSemN_unitary_fun (qv : qs) U n:
 
            ⟦ qv *= U , n.+1 ⟧ = UapplyS U.

Proof.
    apply functional_extensionality => x.
    apply deSemN_unitary.
Qed.

Lemma deSemN_if_fun (qv_m : qs) m S0 S1 n:

            ⟦ If m [[ qv_m ]] Then S0 Else S1 End, n.+1 ⟧
            = fun rho_s => 
                ( ⟦ S0 , n ⟧ (MapplyS m true rho_s)
                + ⟦ S1 , n ⟧ (MapplyS m false rho_s) )%QTS.

Proof.
    apply functional_extensionality => x.
    apply deSemN_if.
Qed.

Lemma deSemN_while_fun (qv_m : qs) m S0 n:

            ⟦ While m [[ qv_m ]] Do S0 End, n.+1 ⟧
            = fun rho_s => 
                ( ⟦ S0 ;; While m [[ qv_m ]] Do S0 End, n ⟧ (MapplyS m true rho_s)
                + MapplyS m false rho_s )%QTS.

Proof.
    apply functional_extensionality => x.
    apply deSemN_while.
Qed.

Lemma deSemN_seq_fun (S0 S1 : prog qs) n:

            ⟦ S0 ;; S1, n.+1 ⟧ = ⟦ S1 , n ⟧ ◦ ⟦ S0, n ⟧.

Proof.
    apply functional_extensionality => x.
    apply deSemN_seq.
Qed.

Lemma deSemN_prob_fun p (S1 S2 : prog qs) n:

        ⟦ S1 [p ⊕] S2, n.+1 ⟧
        = fun rho_s =>
            (⟦ S1, n ⟧( rho_s )[ p ⊕ ] ⟦ S2, n ⟧( rho_s ))%QTS.

Proof.
    apply functional_extensionality => x.
    apply deSemN_prob.
Qed.

Lemma deSemN_nondet_fun (S1 S2 : prog qs) n:
        ⟦ S1 □ S2, n.+1 ⟧ = fun rho_s => ⟦ S1, n ⟧(rho_s) ∪ ⟦ S2, n ⟧(rho_s).
Proof.
    apply functional_extensionality => x.
    apply deSemN_nondet.
Qed.

Lemma deSemN_atom_fun (P : prog qs) n:
        ⟦ <<P>>, n.+1 ⟧ = ⟦ P, n ⟧.
Proof. by []. Qed.

Lemma deSemN_parallel_fun (S1 S2 : prog qs) n:
        ⟦ [ S1 // S2], n.+1 ⟧
        = fun rho_s => 
            (⟦ Step S1 S2 true, n ⟧(rho_s)) ∪ (⟦ Step S1 S2 false, n ⟧(rho_s)).
Proof.
    apply functional_extensionality => x.
    apply deSemN_parallel.
Qed.

End DeSemStepFun.






Lemma deSem0_smaller {qs : QvarScope}:
    forall (S0 : prog qs) (r1 r2 : 𝒫(𝒟( qs )⁻)) (n : nat), 

        r1 ⊑♯ r2 -> ⟦ S0, 0 ⟧ (r1) ⊑♯ ⟦ S0, n ⟧ (r2).

Proof. move => S0 r1 r2 n.
    case (em_classic r1).
    { move => -> /subset_emP ->.
        rewrite !deSem0_em //. }
    { move => Hr1. case (em_classic r2).
        move => -> _. by rewrite [in X in _ ⊑♯ X]deSem0_em //.
        move => Hr2. by rewrite !deSem0_nem //. }
Qed.



(* The strong relation between deSemN and order *)
Lemma deSemN_monotonic_strong {qs : QvarScope}:
    forall (S0 : prog qs) (r1 r2 : 𝒫(𝒟( qs )⁻)) (n i : nat), 
        (i <= n)%nat -> r1 ⊑♯ r2 -> ⟦ S0, i ⟧ (r1) ⊑♯ ⟦ S0, n ⟧ (r2).
Proof. 
    rewrite /PDenSetOrder => S0 r1 r2 n.

    (* induction on n *)
    elim: n S0 r1 r2.
    (* induction basis, n = 0 *)
    move => S0 r1 r2 i. rewrite leqn0 => /eqP ->. by apply deSem0_smaller.


    (* induction step, process i=0 first *)
    move => n IHn S0 r1 r2 i Hi Hr1r2. case: i Hi.
    move => _. by apply deSem0_smaller.

    move => i Hi.
    (* case on programs *)
    case: S0.
    (* skip, abort, init, unitary*)
    1, 2, 3, 4: rewrite /deSemN; intros; by rewrite Hr1r2.
    (* if *)
    move => qv_m m S0 S1. rewrite !deSemN_if. 
    apply PDenSetOrder_add_split; apply IHn => //; by apply PDenSetOrder_M.
    (* while *)
    move => qv_m m S0. rewrite !deSemN_while.
    apply PDenSetOrder_add_split. apply IHn => //.
    1, 2 : by apply PDenSetOrder_M.
    (* sequence *)
    move => S1 S2. rewrite !deSemN_seq. apply IHn => //. by apply IHn.
    (* probability *)
    move => p S1 S2. rewrite !deSemN_prob. apply PDensetOrder_cv_comb_split; by apply IHn.
    (* nondet*)
    move => S1 S2. rewrite !deSemN_nondet. apply PDenSetOrder_union_split; by apply IHn.
    (* atom *)
    move => S0 => //=. by apply IHn.
    (* parallel *)
    move => S1 S2. rewrite !deSemN_parallel. 
    by apply PDenSetOrder_union_split; apply IHn.
Qed.


Lemma deSemN_monotonic_rho {qs : QvarScope} :
    forall (S0 : prog qs) (r1 r2 : 𝒫(𝒟( qs )⁻)) n, 
        r1 ⊑♯ r2 -> ⟦ S0, n ⟧ (r1) ⊑♯ ⟦ S0, n ⟧ (r2).
Proof.
    move => S0 r1 r2 n.
    by apply (@deSemN_monotonic_strong qs S0 r1 r2 n n).
Qed.



(** Prove that [opSemN c i] is increasing when i increases. *)
Lemma deSemN_monotonic_N {qs : QvarScope} (P : prog qs) (rho_s : 𝒫(𝒟( qs )⁻)): 
    forall i n, (i <= n)%nat -> ⟦ P, i ⟧ (rho_s) ⊑♯ ⟦ P, n ⟧ (rho_s).
Proof. move => i n Hin. 
    by apply deSemN_monotonic_strong.
Qed.

Lemma deSemN_monotonic_step {qs : QvarScope} (P : prog qs) (rho_s : 𝒫(𝒟( qs )⁻)): 
    forall n, ⟦ P, n ⟧ (rho_s) ⊑♯ ⟦ P, n.+1 ⟧ (rho_s).
Proof. move => n. apply deSemN_monotonic_strong => //. Qed.
Arguments deSemN_monotonic_step {qs} P rho_s.



(** Some preparatings of order theory *)

(* TODO #4
Definition f_chain_obj {H : HilbertSpace} (f : 𝒫(𝒟( H )⁻) -> 𝒫(𝒟( H )⁻))
    (ch : chain H) : nat -> 𝒫(𝒟( H )⁻) :=
        fun n => f (ch _[n]).

Lemma f_chain_inc {H : HilbertSpace} (f : 𝒫(𝒟( H )⁻) -> 𝒫(𝒟( H )⁻))
    (ch : chain H) :
    forall n 
    forall n, f_chain_obj f ch n ⊑♯ f_chain_obj f ch n.+1.
Proof.
    move => n. apply 
*)


(** Define the operationa semantics (infinite step) *)
Definition chain_deSemN {qs : QvarScope} (P : prog qs) rho_s : chain qs :=
    mk_chain (deSemN_monotonic_step P rho_s).

(* TODO we can implement a general lemma for monotonic functions *)
Lemma chain_deSemN_n {qs : QvarScope} (P : prog qs) rho_s n :
        chain_deSemN P rho_s _[n] = ⟦ P, n ⟧ (rho_s).
Proof. by []. Qed.


Definition DeSem {qs : QvarScope} (P : prog qs) rho_s : 𝒫(𝒟( qs )⁻) :=
    lim→∞ (chain_deSemN P rho_s).

Notation " ⟦ P ⟧ ( rho_s ) " := (@DeSem _ P rho_s) 
    (at level 10, format "⟦  P  ⟧ ( rho_s )"): QPP_scope.

Lemma DeSem_ub : forall {qs : QvarScope} n (P : prog qs) rho_s, 
    ⟦ P, n ⟧ (rho_s) ⊑♯ ⟦ P ⟧ (rho_s).
Proof. 
    rewrite /DeSem => qs n P rho_s. rewrite -chain_deSemN_n. 
    by apply chain_limit_ub.
Qed.
Arguments DeSem_ub {qs} n P rho_s.

Lemma DeSem_lub : forall {qs : QvarScope} (P : prog qs) rho_s rho_ub, 
    (forall n, ⟦ P, n ⟧(rho_s) ⊑♯ rho_ub) -> ⟦ P ⟧ (rho_s) ⊑♯ rho_ub.
Proof.
    rewrite /DeSem => qs P rho_s rho_ub H. apply chain_limit_lub. by apply H.
Qed.

Lemma DeSem_lubP : forall {qs : QvarScope} (P : prog qs) rho_s rho_ub, 
    (forall n, ⟦ P, n ⟧(rho_s) ⊑♯ rho_ub) <-> ⟦ P ⟧ (rho_s) ⊑♯ rho_ub.
Proof. split. by apply DeSem_lub.
    move => HP n. transitivity (⟦ P ⟧ (rho_s)) => //. 
    by apply DeSem_ub.
Qed.

Lemma DeSem_em {qs : QvarScope} (P : prog qs) :
        ⟦ P ⟧ (∅) = ∅.
Proof.
Admitted.



(** Properties of Denotational Semantics *)

Lemma DeSem_skip {qs : QvarScope} (rho_s : 𝒫(𝒟( qs )⁻)):
    ⟦ Skip ⟧ (rho_s) = rho_s.
Proof.
    apply PDenSetOrder_asymm.
    apply DeSem_lub. case. 
        case (em_classic rho_s).
            by move => ->.
            move => H. by rewrite deSem0_nem //.
        move => n. by rewrite deSemN_skip.

    transitivity (⟦ Skip, 1 ⟧(rho_s)). by rewrite deSemN_skip.
    by apply DeSem_ub.
Qed.

Lemma DeSem_abort {qs : QvarScope} (rho_s : 𝒫(𝒟( qs )⁻)):
    ⟦ Abort ⟧ (rho_s) = { _ | rho_s <> ∅ }.
Proof.
    apply PDenSetOrder_asymm.
    apply DeSem_lub. case.
        case (em_classic rho_s).
            move => H. by rewrite rho_s_em_em //.
            move => H. rewrite rho_s_nem_U //. by rewrite deSem0_nem.
        move => H. by rewrite deSemN_abort.
    transitivity (⟦ Abort, 1 ⟧(rho_s)). by rewrite deSemN_abort.
    by apply DeSem_ub.
Qed.

Lemma DeSem_init {qs : QvarScope} qv (rho_s : 𝒫(𝒟( qs )⁻)):
    ⟦ qv <- 0 ⟧ (rho_s) = InitSttS qv rho_s.
Proof.
    apply PDenSetOrder_asymm.
    apply DeSem_lub. case. 

        case (em_classic rho_s).
            rewrite /InitSttS => ->. by rewrite f_map_em.
            move => H. by rewrite deSem0_nem //.
        move => H. by rewrite deSemN_init.
        
    transitivity (⟦ qv <- 0, 1 ⟧ (rho_s)). by rewrite deSemN_init.
    by apply DeSem_ub.
Qed.

Lemma DeSem_unitary {qs : QvarScope} qv U (rho_s : 𝒫(𝒟( qs )⁻)):
    ⟦ qv *= U ⟧ (rho_s) = UapplyS U rho_s.
Proof.
    apply PDenSetOrder_asymm.
    apply DeSem_lub. case.

    case (em_classic rho_s).
        rewrite /UapplyS => ->. by rewrite f_map_em.
        move => H. by rewrite deSem0_nem //.
    move => H. by rewrite deSemN_unitary.

    transitivity (⟦ qv *= U, 1⟧ (rho_s)). by rewrite deSemN_unitary.
    by apply DeSem_ub.
Qed.


Lemma DeSem_if {qs : QvarScope} qv_m m S0 S1 (rho_s : 𝒫(𝒟( qs )⁻)):
    rho_s <> ∅ ->
    ⟦ If m [[qv_m]] Then S0 Else S1 End ⟧ (rho_s) 
        = ⟦ S0 ⟧ (MapplyS m true rho_s) + ⟦ S1 ⟧ (MapplyS m false rho_s).
Proof.
    move => Hnem. apply PDenSetOrder_asymm.

    (*
           ⟦S0⟧  ⟦S1⟧ ⟦IF⟧
            0  +  0   0
                    \
            1  +  1   1
                    \
            2  +  2   2
                    \
              ...    ...

    *)
    (* proof : ⟦S0⟧ + ⟦S1⟧ is the upper bound, therefore larger than lub ⟦IF⟧. *)
    apply DeSem_lub. case. by rewrite deSem0_nem //.
    move => n //. rewrite deSemN_if. apply PDenSetOrder_add_split; apply DeSem_ub.

    (* proof : ⟦IF⟧ is the upper bound, therefore larger than lub ⟦S0⟧ + ⟦S1⟧.
        For this purpose we need the continuity of add. *)
    rewrite ![⟦ _ ⟧ (MapplyS m _ rho_s)]/DeSem. rewrite add_continuous.
    apply chain_limit_lub => l. rewrite /chain_add /chain_add_obj => //=.
    rewrite -deSemN_if. by apply DeSem_ub.
Qed.


Lemma DeSem_while {qs : QvarScope} qv_m m S0 (rho_s : 𝒫(𝒟( qs )⁻)):
    rho_s <> ∅ ->
    ⟦ While m [[qv_m]] Do S0 End ⟧ (rho_s) 
        = ⟦ S0 ;; While m [[qv_m]] Do S0 End ⟧ (MapplyS m true rho_s) 
            + MapplyS m false rho_s.
Proof.
    move => Hnem. apply PDenSetOrder_asymm.

    apply DeSem_lub. case. by rewrite deSem0_nem //.
    move => n //. rewrite deSemN_while. apply PDenSetOrder_add_split. 
    by apply DeSem_ub. by reflexivity.


    rewrite [⟦ _ ⟧ (MapplyS m _ rho_s)]/DeSem.

    (* We need to transform the [MapplyS m rho_s false] term into a singleton
        chain. *)
    rewrite -(singleton_chain_limit (MapplyS m false rho_s)).
    rewrite add_continuous.
    apply chain_limit_lub => l. rewrite /chain_add /chain_add_obj => //=.
    rewrite -deSemN_while. by apply DeSem_ub.
Qed.


(* The chain of deSemN ch (different from chain_deSemN) *)
Definition deSemN_chain_obj {qs : QvarScope} (S : prog qs) (ch : chain qs) n :=
    fun i => ⟦ S, n ⟧(ch _[i]).

Lemma deSemN_chain_prop {qs : QvarScope} (S : prog qs) (ch : chain qs) n
    : forall i, deSemN_chain_obj S ch n i ⊑♯ deSemN_chain_obj S ch n i.+1.
Proof. 
    rewrite /deSemN_chain_obj => i. apply deSemN_monotonic_rho.
    by apply ch.
Qed.
Arguments deSemN_chain_prop {qs} S ch.

Definition deSemN_chain {qs : QvarScope} (S : prog qs) (ch : chain qs) n :=
    mk_chain (deSemN_chain_prop S ch n).



Lemma lim_ch_em_deSemN_em (qs : QvarScope) (S : prog qs) (ch : chain qs) n:
    (lim→∞ (ch)) = ∅ -> (lim→∞ (deSemN_chain S ch n)) = ∅.
Proof.
Admitted.

Lemma lim_ch_nem_chi_nem (qs : QvarScope) (ch : chain qs) i :
    (lim→∞ (ch)) ≠ ∅ -> ch _[i] ≠ ∅.
Proof.
    move => Hch. have Htemp := (@chain_limit_ub _ ch i).
    move => Heq. apply /Hch /subset_emP. rewrite -Heq. apply Htemp.
Qed.


Theorem deSem0_continuous (qs : QvarScope) (S : prog qs) (ch : chain qs):
    ⟦ S, 0 ⟧ (lim→∞ (ch)) = lim→∞ (deSemN_chain S ch 0).
Proof.
    rewrite /deSemN_chain /deSemN_chain_obj //.
    case (em_classic (lim→∞ (ch))).
    case S.
    move => H. rewrite H. rewrite deSem0_em.
Admitted.


(** TODO #8 *)
Theorem deSemN_continuous (qs : QvarScope) (S : prog qs) (ch : chain qs) n:
        ⟦ S, n ⟧ (lim→∞ (ch)) = lim→∞ (deSemN_chain S ch n).
Proof.
    elim: n S ch.
    (* induction basis *)
    move => S ch //. apply deSem0_continuous.
    
    (* apply PDenSetOrder_asymm.
    
    (* deSemN is continuous, for all sets (including the empty set) *)
    case (em_classic (lim→∞ (ch))).
    move => Hlimch.
    have Htemp : (lim→∞ (deSemN_chain S ch 0)) = ∅.
    { apply PDenSetOrder_asymm. by []. 
    }
    move => ->. rewrite deSem0_em.

    by apply PDenSet_uni_least.
    apply chain_limit_lub. by rewrite /deSemN_chain /deSemN_chain_obj //=.
    *)

    (* induction step, case on program [S] *)
    move => n IHn. case.

    (* skip *)
    move => ch.
    rewrite /deSemN_chain /deSemN_chain_obj deSemN_skip. f_equal. 
    apply /chain_eqP. by rewrite /chain_obj deSemN_skip_fun.

    (* abort *) 
    move => ch.
    rewrite deSemN_abort. case (em_classic (lim→∞ (ch))).

    move => H. rewrite rho_s_em_em //. rewrite lim_ch_em_deSemN_em //.
    
    move => H. rewrite rho_s_nem_U //. apply PDenSetOrder_asymm.
    by []. apply chain_limit_lub => i //=. rewrite /deSemN_chain_obj.
    rewrite deSemN_abort rho_s_nem_U //. by apply lim_ch_nem_chi_nem. 

    (* init *)
    move => ch qv. 
    rewrite /deSemN_chain /deSemN_chain_obj deSemN_init init_continuous. 
    f_equal. apply /chain_eqP. by rewrite /chain_obj deSemN_init_fun.

    (* unitary *)
    move => ch qv U. rewrite /deSemN_chain /deSemN_chain_obj.
    rewrite deSemN_unitary unitary_continuous. f_equal. 
    apply /chain_eqP. by rewrite /chain_obj deSemN_unitary_fun.

    (* if *)
    move => qv_m m S0 S1 ch. rewrite deSemN_if.
    rewrite !mea_continuous !IHn add_continuous. f_equal. 
    rewrite chain_eqP //.
    rewrite /deSemN_chain /deSemN_chain_obj /chain_obj. by rewrite deSemN_if_fun.
    
    (* While *)
    move => qv_m m S0 ch. rewrite deSemN_while.
    rewrite !mea_continuous IHn add_continuous. f_equal.     
    rewrite chain_eqP //.
    rewrite /deSemN_chain /deSemN_chain_obj /chain_obj. by rewrite deSemN_while_fun.

    (* Seq *)
    move => S1 S2 ch. rewrite deSemN_seq.
    rewrite !IHn. f_equal.     
    rewrite chain_eqP //.
    rewrite /deSemN_chain /deSemN_chain_obj /chain_obj. by rewrite deSemN_seq_fun.

    (* probability *)
    move => p S1 S2 ch. rewrite deSemN_prob.
    rewrite !IHn cvcomb_continuous. f_equal.
    rewrite chain_eqP //.
    rewrite /deSemN_chain /deSemN_chain_obj /chain_obj. by rewrite deSemN_prob_fun.

    (* nondeterminism *)
    move => S1 S2 ch. rewrite deSemN_nondet.
    rewrite !IHn union_continuous. f_equal. 
    rewrite chain_eqP //.
    rewrite /deSemN_chain /deSemN_chain_obj /chain_obj. by rewrite deSemN_nondet_fun.
 
    (* atom *)
    move => S0 ch. rewrite deSemN_atom.
    rewrite IHn. f_equal. by apply /chain_eqP.

    (* parallel *)
    move => S1 S2 ch. rewrite deSemN_parallel.
    rewrite !IHn union_continuous. f_equal.     
    rewrite chain_eqP //.
    rewrite /deSemN_chain /deSemN_chain_obj /chain_obj. 
    by rewrite deSemN_parallel_fun.
Qed.



Lemma DeSem_seq {qs : QvarScope} S1 S2 (rho_s : 𝒫(𝒟( qs )⁻)):
    ⟦ S1 ;; S2 ⟧ (rho_s) =  ⟦ S2 ⟧ ( ⟦ S1 ⟧ (rho_s) ).
Proof.
    apply PDenSetOrder_asymm.

    apply DeSem_lub. case. 
    (* induction basis, case on whether rho_s is empty *)
    case (em_classic rho_s).
    move => ->. by rewrite deSem0_em !DeSem_em.
    move => H. by rewrite deSem0_nem.

    (* induction step *)
    move => n. rewrite deSemN_seq. transitivity (⟦ S2, n ⟧(⟦ S1 ⟧ (rho_s))).
    apply deSemN_monotonic_rho. by apply DeSem_ub.
    by apply DeSem_ub.

    apply DeSem_lub => n.
    rewrite [⟦ S1 ⟧(_)]/DeSem. rewrite deSemN_continuous.
    apply chain_limit_lub => i.
    rewrite /deSemN_chain /deSemN_chain_obj.
    (* using [max i n] steps in [S1 ;; S2] *)
    move : (DeSem_ub (max i n).+1 (S1;;S2) rho_s).
    case E : (i <= n)%nat. 
    { move /leP : E => E. rewrite (max_r _ _ E) => H.
    transitivity (⟦ S2, n ⟧ (⟦ S1, n ⟧(rho_s))).
    apply deSemN_monotonic_rho.
    by apply /deSemN_monotonic_N /leP.
    rewrite deSemN_seq in H.
    by apply H. }

    move /leP /Nat.lt_nge /Nat.lt_le_incl: E => E. rewrite (max_l _ _ E) => H.
    transitivity (⟦ S2, i ⟧ (⟦ S1, i ⟧(rho_s))).
    by apply /deSemN_monotonic_N /leP.
    rewrite deSemN_seq in H.
    by apply H.
Qed.    

Lemma DeSem_atom {qs : QvarScope} P (rho_s : 𝒫(𝒟( qs )⁻)):
    ⟦ <<P>> ⟧ (rho_s) =  ⟦ P ⟧ (rho_s).
Proof.

    apply PDenSetOrder_asymm.

    apply DeSem_lub. case. 
    case (em_classic rho_s).
        move => ->. by rewrite deSem0_em DeSem_em.
        move => H. by rewrite deSem0_nem.
    move => n. rewrite deSemN_atom. by apply DeSem_ub.

    apply DeSem_lub => n. rewrite -deSemN_atom. by apply DeSem_ub.
Qed.

Lemma DeSem_para {qs : QvarScope} S1 S2 (rho_s : 𝒫(𝒟( qs )⁻)):
    ⟦ [S1 // S2] ⟧ (rho_s) = 
        ⟦ Step S1 S2 true ⟧ (rho_s) ∪ ⟦ Step S1 S2 false ⟧ (rho_s).
Proof.
    apply PDenSetOrder_asymm.

    apply DeSem_lub. case.
    case (em_classic rho_s).
        move => ->. by rewrite deSem0_em !DeSem_em union_same.
        move => H. by rewrite deSem0_nem.

    move => n. rewrite deSemN_parallel. 
    apply PDenSetOrder_union_split; by apply DeSem_ub.

    rewrite ![⟦ Step _ _ _ ⟧(rho_s)]/DeSem. 
    rewrite union_continuous. apply chain_limit_lub => l.
    rewrite /chain_union /chain_union_obj /chain_deSemN /chain_obj => //.
    rewrite -deSemN_parallel. by apply DeSem_ub.
Qed.

End QParallelProg.
    




    