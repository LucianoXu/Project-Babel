(** * Parallel.v : describing parallel quantum programs *)

From Babel Require Import TerminalDogma.premises 
                          TerminalDogma.Extensionality.

From Babel Require Import QTheory POrderFacility POrderSet POrderNat
                            nd_seq.

From Babel.Ranko Require Import CentralCharacter.

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


(** use the number order *)
Import NatLePoset.CanonicalStruct.
Import SubsetOrder.CanonicalStruct.


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
Notation " S1 ; S2 " := (@seq_ _ S1 S2) 
    (at level 95, right associativity) : QPP_scope.
Notation " S1 [ p ⊕ ] S2 " := (@prob_ _ p S1 S2) 
    (format "S1  [ p  ⊕ ]  S2"): QPP_scope.
Notation " S1 □ S2 " := (@nondet_ _ S1 S2) (at level 3): QPP_scope.
Notation " << P >> " := (@atom_ _ P) : QPP_scope.
Notation " [ S1 // S2 ] " := (@parallel_ _ S1 S2) (at level 0) : QPP_scope.

Fixpoint non_parallel {qs : QvarScope} (P : prog qs) : bool :=
    match P with 
    | [S1 // S2] => false
    | If m [[ qv_m ]] Then S0 Else S1 End => non_parallel S0 && non_parallel S1
    | While m [[ qv_m ]] Do S0 End => non_parallel S0
    | S1 ; S2 => non_parallel S1 && non_parallel S2
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
    | S1;S2 => (qvar_of_prog S1) [+] (qvar_of_prog S2)
    | S1 [ p ⊕ ] S2 => (qvar_of_prog S1) [+] (qvar_of_prog S2)
    | S1 □ S2 =>(qvar_of_prog S1) [+] (qvar_of_prog S2)
    | <<S0>> => qvar_of_prog S0
    | [ S1 // S2 ] => (qvar_of_prog S1) [+] (qvar_of_prog S2)
    end.
Coercion qvar_of_prog : prog >-> Qvar.


Fixpoint seq_Head {qs : QvarScope} (S0 : prog qs) : prog qs :=
    match S0 with
    | P0 ; P1 => seq_Head P0
    | _ => S0
    end.
Fixpoint seq_Tail {qs : QvarScope} (S0 : prog qs) : option (prog qs) :=
    match S0 with
    | P0 ; P1 => match seq_Tail P0 with
                  | None => Some P1
                  | Some Q => Some (Q ; P1)
                  end
    | _ => None
    end.

(** Refine the step statement *)
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
                If m [[ qv_m ]] Then [ P0 ; While m [[qv_m]] Do P0 End // S2 ]
                                Else [ Skip // S2] End
            | _ => S1 ; [ Skip // S2 ]
            end 
        (** Note that here we give a different interpretation of 
            nested parallel composition 
            We consider the inner parallel composition as a 'atomic' action
            performed in parallel *)
        | Some Q => seq_Head S1 ; [ Q // S2 ]
        end
    else
        match seq_Tail S2 with
        | None => (* if S2 is not a sequence *)
            match S2 with
            | If m [[ qv_m ]] Then P0 Else P1 End => 
                If m [[ qv_m ]] Then [ S1 // P0 ] Else [ S1 // P1 ] End
            | While m [[ qv_m ]] Do P0 End =>
                If m [[ qv_m ]] Then [ S1 // P0 ; While m [[qv_m]] Do P0 End ]
                                Else [ S1 // Skip] End
            | _ => S2 ; [ S1 // Skip ]
            end 
        (** Note that here we give a different interpretation of 
            nested parallel composition *)
        | Some Q => seq_Head S2 ; [ S1 // Q ]
    end.
Arguments Step : simpl nomatch.
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
        -=> <{ S0 ; While m [[qv_m]] Do S0 End, Mapply m true rho }>

| while_step_N qv_m m S0 rho:
    <{ While m [[qv_m]] Do S0 End, rho }>
        -=> <{ ↓, Mapply m true rho }>

| seq_step_p S0 St S1 rho0 rho1:
    <{ S0, rho0 }> -=> <{ St, rho1 }>
    -> <{ S0 ; S1, rho0 }> -=> <{ St ; S1, rho1 }>

| seq_step_t S0 S1 rho0 rho1:
    <{ S0, rho0 }> -=> <{ ↓, rho1 }>
        -> <{ S0 ; S1, rho0 }> -=> <{ S1, rho1 }>

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
        | 0 => ∅
        | n'.+1 => 
            match P with
            | Skip => 
                {{ rho }}

            | Abort => 
                𝕌 

            | qv <- 0 => 
                {{ InitStt qv rho }}

            | qv *= U => 
                {{ Uapply U rho }}

            | If m [[ qv_m ]] Then P0 Else P1 End =>
                (⦗ P0, n' ⦘ ( Mapply m true rho ))
                + (⦗ P1, n' ⦘ ( Mapply m false rho ))

            | While m [[ qv_m ]] Do P0 End  =>
                ⦗ P0; While m [[ qv_m ]] Do P0 End, n' ⦘ (Mapply m true rho)
                + {{ Mapply m false rho }}

            | S1 ; S2 => 
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

Arguments deSemN_point : simpl nomatch.

Notation " ⦗ ↓ ⦘ ( rho ) " := (deSemN_point None _ rho) :QPP_scope.
Notation " ⦗ ↓ ⦘ " := (deSemN_point None _ ) :QPP_scope.

(** lift to set input *)
Definition deSemN {qs : QvarScope} (P : prog qs) (n : nat) := ⋃ ◦ ⦗ P, n ⦘ [<].


Notation " ⟦ P , n ⟧ " := (deSemN P n)
    (at level 10, format "⟦  P ,  n  ⟧") : QPP_scope.

Notation " ⟦ P , n ⟧ ( rho_s ) " := (deSemN P n rho_s)
    (at level 10, rho_s at next level, 
    format "⟦  P ,  n  ⟧ ( rho_s )") : QPP_scope.

(*
(** Prove that [⦗ P , n ⦘ ( rho )] is always nonempty. *)
Lemma deSemN_point_nemMixin {qs : QvarScope} (P : prog qs) (n : nat) rho :
    NemSet.class_of (⦗ P , n ⦘ (rho)).
Proof.
    rewrite /NemSet.mixin_of. elim: n P rho.
    move => P rho //=. apply uni_neq_em.
    
    (** induction step *)
    move => n IHn. case => //=.

    (** skip, abort, init, unitary *)
    1,2,3,4 : intros; apply NemSet.class.

    (** if *)
    move => qv_m m S0 S1 rho. 
    by apply add_set_nem; apply IHn.

    (** while *)
    move => qv_m m S0 rho.
    apply add_set_nem. by apply IHn. by apply NemSet.class.

    (** sequence *)
    move => S1 S2 rho.
    apply bigU_nemP. apply forall_to_exists_nonempty.
    rewrite mapR_eq_emP. by apply IHn.
    move => //= A [] x [_ Hx]. rewrite -Hx. by apply IHn.

    (** probability *)
    move => p S1 S2 rho.
    apply scalar_convex_combS_nemMixin; by apply IHn.

    (** nondeterministic *)
    move => S1 S2 rho.
    apply union_nem_L. by apply IHn.

    (** parallel *)
    move => S1 S2 rho.
    apply union_nem_L. by apply IHn.
Qed.



(** Prove that [⟦ P , n ⟧ (rho_s)] is always nonempty. *)

Lemma deSemN_nemMixin {qs : QvarScope} (P : prog qs) (n : nat) 
    (rho_s : 𝒫(𝒟( qs )⁻)) (Hnem : NemSet.class_of rho_s) : 
        NemSet.class_of (⟦ P , n ⟧ (rho_s)).
Proof.
    rewrite /NemSet.mixin_of /deSemN.
    apply bigU_nemP. apply forall_to_exists_nonempty.
    by rewrite mapR_eq_emP.
    move => A [] x [_ Hx]. rewrite -Hx. by apply deSemN_point_nemMixin.
Qed.

Canonical deSemN_nemType 
    {qs : QvarScope} (P : prog qs) (n : nat) (rho_s : 𝒫(𝒟( qs )⁻)₊) :=
        NemSet _ (@deSemN_nemMixin _ P n _ (NemSet.class rho_s)).
*)


Section DeSemPointStep.

Variable (qs : QvarScope) (rho : 𝒟( qs )⁻) (n : nat).

Lemma deSemN_seq_point_fun (S1 S2 : prog qs):

    ⦗ S1 ; S2, n.+1 ⦘ = ⋃ ◦ ⦗ S2, n ⦘ [<] ◦ ⦗ S1, n ⦘.

Proof. by []. Qed.

End DeSemPointStep.



Section DeSemStep.

Variable (qs : QvarScope) (rho_s : 𝒫(𝒟( qs )⁻)₊).
(*


Lemma deSemN_skip n:

            ⟦ Skip, n.+1 ⟧(rho_s) = rho_s.

Proof. 
    rewrite /deSemN /fun_comp /mapR //=.
    by rewrite bigU_rei.
Qed.



Lemma deSemN_abort n:

            ⟦ Abort, n ⟧(rho_s) = 𝕌.

Proof. 
    rewrite /deSemN /fun_comp /mapR //=.
    case: n => //=.
    rewrite bigU_sgt_nem => //. apply NemSet.class.
    rewrite bigU_sgt_nem => //=. by apply NemSet.class.
Qed.


Lemma deSemN_init qv n:
 
            ⟦ qv <-0 , n.+1 ⟧(rho_s) = (InitStt qv) [<] rho_s.

Proof. 
    rewrite /deSemN /fun_comp /mapR //=.
    by rewrite bigU_fun_rei.
Qed.


Lemma deSemN_unitary qv U n:
 
            ⟦ qv *= U , n.+1 ⟧(rho_s) = (Uapply U) [<] rho_s.

Proof. 
    rewrite /deSemN /mapR //=. 
    by apply bigU_fun_rei.
Qed.
Lemma deSemN_if qv_m m S0 S1 n:

            ⟦ If m [[ qv_m ]] Then S0 Else S1 End, n.+1 ⟧ (rho_s) 
            = ( ⟦ S0 , n ⟧ ((Mapply m true) [<] rho_s)
            + ⟦ S1 , n ⟧ ((Mapply m false) [<] rho_s) )%QTS.

Proof.

    rewrite /deSemN /fun_comp /mapR //=. 
    

Abort.

Lemma deSemN_while qv_m m S0 n:

            ⟦ While m [[ qv_m ]] Do S0 End, n.+1 ⟧ (rho_s) 
            = ( ⟦ S0 ; While m [[ qv_m ]] Do S0 End, n ⟧ (MapplyS m true rho_s)
            + MapplyS m false rho_s )%QTS.

Proof.
    rewrite /deSemN //=.
Abort.

Lemma deSemN_seq S0 S1 n:

            ⟦ S0 ; S1, n.+1 ⟧ (rho_s) = ⟦ S1 , n ⟧ (⟦ S0, n ⟧ (rho_s)).

Proof.
    equal_f_comp rho_s.
    rewrite /deSemN deSemN_seq_point_fun.
    
    rewrite -[RHS]fun_assoc
        [(⋃ ◦ ⦗ S1, n ⦘ [<]) ◦ ⋃] fun_assoc.
    rewrite mapR_bigU_swapF.
    rewrite -bigU_fun_distF.
    rewrite -[⋃ ◦ ⦗ S1, n ⦘ [<] ◦ ⦗ S0, n ⦘]fun_assoc.
    rewrite -double_mapRF.
    by rewrite fun_assoc.
Qed.

Lemma deSemN_prob p S1 S2 n:

        ⟦ S1 [p ⊕] S2, n.+1 ⟧(rho_s) 
        = (⟦ S1, n ⟧( rho_s )[ p ⊕ ] ⟦ S2, n ⟧( rho_s ))%QTS.

Proof.
Abort.
*)

Lemma deSemN_nondet S1 S2 n:
        ⟦ S1 □ S2, n.+1 ⟧(rho_s) = ⟦ S1, n ⟧(rho_s) ∪ ⟦ S2, n ⟧(rho_s).
Proof.
    rewrite /deSemN /mapR => //=.
    by rewrite union_bigU_mapR_dist.
Qed.

Lemma deSemN_atom P n:
        ⟦ <<P>>, n.+1 ⟧(rho_s) = ⟦ P, n ⟧(rho_s).
Proof. by []. Qed.


Lemma deSemN_parallel S1 S2 n:
        ⟦ [ S1 // S2], n.+1 ⟧(rho_s) 
        =  (⟦ Step S1 S2 true, n ⟧(rho_s)) ∪ (⟦ Step S1 S2 false, n ⟧(rho_s)).
Proof.
    rewrite /deSemN /mapR.
    by rewrite union_bigU_mapR_dist.
Qed.

End DeSemStep.



Lemma deSem0 (qs : QvarScope) P (rho_s : 𝒫(𝒟( qs )⁻)) :
        
        ⟦ P , 0 ⟧ (rho_s) = ∅.

Proof.
    rewrite /deSemN /fun_comp /mapR //=.
    case (em_classic rho_s).
    move => ->. by apply bigU_sgt_em.
    move => ?. by apply bigU_sgt_nem.
Qed.


Lemma deSem_em (qs : QvarScope) (P : prog qs) n :

        ⟦ P , n ⟧ (∅) = ∅.

Proof.
    rewrite /deSemN /fun_comp => //=.
    rewrite mapR_em. by apply big_union_em.
Qed.
    


Lemma deSemN_monotonicMixin {qs : QvarScope} (P : prog qs) (n : nat) :
    MonotonicFun.mixin_of (⟦ P, n ⟧).
Proof.
    rewrite /MonotonicFun.mixin_of => A B HAinB.

    (** prove the special cases *)
    case: n. by rewrite !deSem0.
    move => n.
    case: (em_classic A); case: (em_classic B).
    move => -> ->. by rewrite deSem_em.
    move => _ ->. by rewrite deSem_em.
    move => HB HA. rewrite HB //= in HAinB. 
        rewrite subset_emP in HAinB. by destruct (HA HAinB).

    move => HB HA.

    rewrite /deSemN /fun_comp.

    case P; rewrite /mapR //=; intros; apply bigU_mor_sub;
    by apply mapR_mor_sub.
Qed.

Canonical deSemN_monotonicfun {qs : QvarScope} (P : prog qs) (n : nat) :=
    MonotonicFun _ (@deSemN_monotonicMixin qs P n).


Lemma deSemN_continuousMixin {qs : QvarScope} (P : prog qs) (n : nat) :
    ContinuousFun.mixin_of (MonotonicFun.class (⟦ P, n ⟧)).
Proof.
    rewrite /ContinuousFun.mixin_of //= => c.
    rewrite /monotonic_mapR_chain  /CPO.join_op  //=.
    rewrite /deSemN.
    equal_f_comp c. 
    (** LHS *)
    rewrite -fun_assoc.
    rewrite [((⋃ ◦ ⦗ P, n ⦘ [<]) ◦ ⋃)]fun_assoc. 
    rewrite mapR_bigU_swapF.
    (** RHS *)
    rewrite -[in RHS]fun_assoc.
    rewrite bigU_fun_distF.
    by [].
Qed.



(* The strong relation between opSemN and order *)
Lemma deSemN_point_monotonic_strong {qs : QvarScope} :
    forall (S0 : prog qs) (rho : 𝒟( qs )⁻) n i, 
        (i <= n)%nat -> ⦗ S0, i ⦘ (rho) ⊆ ⦗ S0, n ⦘ (rho).
Proof.
    move => S0 rho n.

    (* induction on n *)
    elim: n S0 rho.
    (* induction basis, n = 0*)
    move => S0 rho i. by rewrite leqn0 => /eqP ->.

    (* induction step, process i=0 first *)
    move => n IHn S0 rho i Hi. case: i Hi.
    by move => _.

    move => i Hi.
    (* case on programs *)
    case: S0.
    (* skip abort, init, unitary *)
    1,2,3,4: by intros.
    (* if *)
    move => qv_m m S0 S1. 
    by apply PDenSetOrder_add_split; apply /IHn.
    (* while *)
    move => qv_m m S0 /=. 
    apply PDenSetOrder_add_split; last first => //.
    by apply IHn.
    (* sequence *)
    move => S1 S2 /=.
    apply bigU_mapR_mor_sub.
    by apply IHn.
    move => t. by apply IHn.
    (* probability *)
    move => p S1 S2 /=.
    apply PDensetOrder_cv_comb_split; by apply IHn.
    (* nondet *)
    move => S1 S2 /=.
    apply PDenSetOrder_union_split; by apply IHn.
    (* atom *)
    move => S0 /=. by apply IHn => //.
    (* parallel *)
    move => S1 S2 /=. 
    apply PDenSetOrder_union_split; by apply IHn.
Qed.

Lemma deSemN_point_monotonic_step {qs : QvarScope} (P : prog qs) rho: 
    forall n, ⦗ P, n ⦘ (rho) ⊆ ⦗ P, n.+1 ⦘ (rho).
Proof. move => n. by apply deSemN_point_monotonic_strong. Qed.
Arguments deSemN_point_monotonic_step {qs} P rho.


(* The strong relation between deSemN and order *)
Lemma deSemN_monotonic_strong {qs : QvarScope}:
    forall (S0 : prog qs) (r1 r2 : 𝒫(𝒟( qs )⁻)) (n i : nat), 
        (i <= n)%nat -> r1 ⊆ r2 -> ⟦ S0, i ⟧ (r1) ⊆ ⟦ S0, n ⟧ (r2).
Proof. 
    rewrite /deSemN => S0 r1 r2 n i Hi Hr1r2.
    apply bigU_mapR_mor_sub => // t.
    by apply deSemN_point_monotonic_strong.
Qed.


Lemma deSemN_monotonic_rho {qs : QvarScope} :
    forall (S0 : prog qs) (r1 r2 : 𝒫(𝒟( qs )⁻)) n, 
        r1 ⊆ r2 -> ⟦ S0, n ⟧ (r1) ⊆ ⟦ S0, n ⟧ (r2).
Proof.
    move => S0 r1 r2 n.
    by apply (@deSemN_monotonic_strong qs S0 r1 r2 n n).
Qed.



(** Prove that [opSemN c i] is increasing when i increases. *)
Lemma deSemN_monotonic_N {qs : QvarScope} (P : prog qs) (rho_s : 𝒫(𝒟( qs )⁻)): 
    forall i n, (i <= n)%nat -> ⟦ P, i ⟧ (rho_s) ⊆ ⟦ P, n ⟧ (rho_s).
Proof. move => i n Hin. 
    by apply deSemN_monotonic_strong.
Qed.

Lemma deSemN_monotonic_step {qs : QvarScope} (P : prog qs) (rho_s : 𝒫(𝒟( qs )⁻)): 
    forall n, ⟦ P, n ⟧ (rho_s) ⊆ ⟦ P, n.+1 ⟧ (rho_s).
Proof. move => n. by apply deSemN_monotonic_strong. Qed.
Arguments deSemN_monotonic_step {qs} P rho_s.



(** Construct the monotonic structure *)
Definition deSemN_n {qs : QvarScope} (P : prog qs) rho_s n := deSemN P n rho_s.


Lemma deSemN_n_monotonicMixin 
    {qs : QvarScope} (P : prog qs) (rho_s : 𝒫(𝒟( qs )⁻)) : 
    MonotonicFun.mixin_of (deSemN_n P rho_s).
Proof.
    rewrite /MonotonicFun.mixin_of => x y Hxy.
    rewrite /deSemN_n. apply deSemN_monotonic_N. apply /leP. by apply Hxy.
Defined.

Canonical deSemN_n_monotonic 
    {qs : QvarScope} (P : prog qs) (rho_s : 𝒫(𝒟( qs )⁻)) := 
    MonotonicFun _ (@deSemN_n_monotonicMixin _ P rho_s).


(*
Lemma deSemN_n_continuousMixin
    {qs : QvarScope} (P : prog qs) (rho_s : 𝒫(𝒟( qs )⁻)) : True.
    ContinuousFun.mixin_of (MonotonicFun.class (deSemN_n P rho_s)).


(** Define the operationa semantics (infinite step) *)
Definition chain_deSemN {qs : QvarScope} (P : prog qs) rho_s : chain 𝒟(qs)⁻ :=
    mk_chain (deSemN_monotonic_step P rho_s).
(** Note that these two chains are different.
    One on step number, and another on ch index. *)



(* TODO we can implement a general lemma for monotonic functions *)
Lemma chain_deSemN_n {qs : QvarScope} (P : prog qs) rho_s n :
        chain_deSemN P rho_s _[n] = ⟦ P, n ⟧ (rho_s).
Proof. by []. Qed.
*)


Definition DeSem 
    {qs : QvarScope} (P : prog qs) (rho_s : 𝒫(𝒟( qs )⁻)) : 𝒫(𝒟( qs )⁻) := 
        
        ⊔ᶜˡ ((deSemN_n P rho_s) [<] 𝕌).

Notation " ⟦ P ⟧ " := (@DeSem _ P) 
        (at level 10, format "⟦  P  ⟧"): QPP_scope.  
Notation " ⟦ P ⟧ ( rho_s ) " := (@DeSem _ P rho_s) 
    (at level 10, format "⟦  P  ⟧ ( rho_s )"): QPP_scope.

Lemma DeSem_monotonicMixin {qs : QvarScope} (P : prog qs) : 
    MonotonicFun.mixin_of (⟦ P ⟧).
Proof.
    rewrite /MonotonicFun.mixin_of //= => A B HAB.
    rewrite !/DeSem /CLattice.join_op //=.
    apply bigU_mapR_mor_sub => //=.
    rewrite /deSemN_n => n.
    by apply (MonotonicFun.class (⟦ P, n ⟧)).
Qed.

Canonical DeSem_monotonicfun {qs : QvarScope} (P : prog qs) :=
    MonotonicFun _ (@DeSem_monotonicMixin qs P).

(* 

Lemma DeSem_continuousMixin {qs : QvarScope} (P : prog qs) :
    ContinuousFun.mixin_of (MonotonicFun.class (⟦ P ⟧)).
Proof.
    rewrite /ContinuousFun.mixin_of /CPO.join_op //= => c.
    rewrite /DeSem /CLattice.join_op //=. apply poset_antisym.
    rewrite /mapR //=.
    equal_f_comp c.
    rewrite -fun_assoc.
    rewrite 



Lemma DeSem_ub : forall {qs : QvarScope} n (P : prog qs) rho_s, 
    ⟦ P, n ⟧ (rho_s) ⊑ ⟦ P ⟧ (rho_s).
Proof.
    rewrite /DeSem => qs n P rho_s //=.
    have t := CPO.join_prop (CPO.class _ ) [chain of ((deSemN_n P rho_s) [<] (𝕌))].
    apply t => //=.
    exists n. by split.
Qed.
Arguments DeSem_ub {qs} n P rho_s.

Lemma DeSem_lub : forall {qs : QvarScope} (P : prog qs) rho_s rho_ub, 
    (forall n, ⟦ P, n ⟧(rho_s) ⊑ rho_ub) -> ⟦ P ⟧ (rho_s) ⊑ rho_ub.
Proof.
    rewrite /DeSem => qs P rho_s rho_ub H //=.
    have t := CPO.join_prop (CPO.class _ ) [chain of ((deSemN_n P rho_s) [<] (𝕌))].
    apply t => //=.

Qed.

Lemma DeSem_lubP : forall {qs : QvarScope} (P : prog qs) rho_s rho_ub, 
    (forall n, ⟦ P, n ⟧(rho_s) ⊑ rho_ub) <-> ⟦ P ⟧ (rho_s) ⊑ rho_ub.
Proof. split. by apply DeSem_lub.
    move => HP n. transitivity (⟦ P ⟧ (rho_s)) => //. 
    by apply DeSem_ub.
Qed.
*)

(*##################################################################*)
(* tactic *)

Ltac deSem_simpl_branch :=
    (   rewrite /deSemN_n
        || rewrite /deSemN
    ) => //=.


Ltac deSem_move_up_branch := 
    match goal with
    | H : _ = ⦗ _, _ ⦘(_) |- _ => clear H
    | H : _ = ⟦ _, _ ⟧(_) |- _ => clear H
    | n : nat |- _ ∈ ⦗ Skip , ?n ⦘(_) -> _ =>
        generalize dependent n; case => //=
    | n : nat |- _ ∈ ⦗ Abort , ?n ⦘(_) -> _ =>
        generalize dependent n; case => //=
    | n : nat |- _ ∈ ⦗ _ <- 0, ?n ⦘(_) -> _ =>
        generalize dependent n; case => //=
    | n : nat |- _ ∈ ⦗ _ *= _, ?n ⦘(_) -> _ =>
        generalize dependent n; case => //=

    | n : nat |- _ ∈ ⦗ If _ [[_]] Then _ Else _ End , ?n ⦘(_) -> _ =>
        generalize dependent n; case => //=
    
    | n : nat |- _ ∈ ⦗ While _ [[_]] Do _ End , ?n ⦘(_) -> _ =>
        generalize dependent n; case => //=

    (** to avoid dead loop *)
    | n : nat |- _ ∈ ⦗ _; While _ [[_]] Do _ End , ?n ⦘(_) -> _ => intros ?

    | n : nat |- _ ∈ ⦗ _; _ , ?n ⦘(_) -> _ =>
        generalize dependent n; case => //=

    | n : nat |- _ ∈ ⦗ << _ >>, ?n ⦘(_) -> _ =>
        generalize dependent n; case => //=

    | n : nat |- _ ∈ ⦗ [_ // _], ?n ⦘(_) -> _ =>
        generalize dependent n; case => //=
        
    end.

Ltac deSem_step
        top_step
        :=
        match goal with
        | _ => progress repeat deSem_simpl_branch
        | _ => progress deSem_move_up_branch

        | _ => set_step top_step integer:(0)
        end.
    
Ltac deSem_step_sealed :=
    idtac; let rec top := deSem_step_sealed in deSem_step top.

Ltac deSem_killer := 
    all_move_down;
    repeat deSem_step_sealed.

(*##################################################################*)



(** Properties of Denotational Semantics *)

Lemma DeSem_skip {qs : QvarScope} (rho_s : 𝒫(𝒟( qs )⁻)₊):
    ⟦ Skip ⟧ (rho_s) = rho_s.
Proof.
    deSem_killer.
    instantiate (1:=1%nat). deSem_killer. 

    (*
    rewrite /DeSem /CLattice.join_op //=. apply poset_antisym.

    apply bigU_lub => a [] i [] _ ->.
    rewrite /deSemN_n /deSemN -fun_compP.
    case: i.
    (** n = 0 *)
    rewrite /deSemN_point. rewrite /mapR.
    rewrite bigU_sgt_nem //=. by apply NemSet.class.
    (** n > 0 *)
    rewrite /mapR //= => n. by rewrite bigU_rei.

    apply bigU_ub => //=. exists 1%nat. split => //=.
    rewrite /deSemN_n /deSemN /fun_comp /mapR //=.
    by rewrite bigU_rei.
    *)
Qed.

Lemma DeSem_abort {qs : QvarScope} (rho_s : 𝒫(𝒟( qs )⁻)₊):
    ⟦ Abort ⟧ (rho_s) = 𝕌.
Proof.
    deSem_killer.
    instantiate (1:=1%nat). deSem_killer. 
Qed.

Lemma DeSem_init {qs : QvarScope} qv (rho_s : 𝒫(𝒟( qs )⁻)₊):
    ⟦ qv <- 0 ⟧ (rho_s) = (InitStt qv) [<] rho_s.
Proof.
    deSem_killer.
    instantiate (1:=1%nat). deSem_killer. 
Qed.

Lemma DeSem_unitary {qs : QvarScope} qv U (rho_s : 𝒫(𝒟( qs )⁻)₊):
    ⟦ qv *= U ⟧ (rho_s) = (Uapply U) [<] rho_s.
Proof.
    deSem_killer.
    instantiate (1:=1%nat). deSem_killer. 
Qed.




Lemma DeSem_if {qs : QvarScope} qv_m m S0 S1 (rho_s : 𝒫(𝒟( qs )⁻)):
    
    ⟦ If m [[qv_m]] Then S0 Else S1 End ⟧ (rho_s) 
        = ⋃ ((fun rho => 
            (⟦ S0 ⟧ ({{ Mapply m true rho }}) + ⟦ S1 ⟧ ({{ Mapply m false rho}}))) [<] rho_s).

Proof.
    deSem_killer. apply a0. apply a1.
    instantiate(1:= (Nat.max x11 x5).+1). deSem_killer.
    apply (set_belong_cut (⦗ S1, x5 ⦘((Mapply m false x1)))) => //.
    apply deSemN_point_monotonic_strong. apply /leP. apply Nat.le_max_r.
    apply (set_belong_cut (⦗ S0, x11 ⦘((Mapply m true x1)))) => //.
    apply deSemN_point_monotonic_strong. apply /leP. apply Nat.le_max_l.
Qed.


Lemma DeSem_while {qs : QvarScope} qv_m m S0 (rho_s : 𝒫(𝒟( qs )⁻)):
    ⟦ While m [[qv_m]] Do S0 End ⟧ (rho_s) 
        = ⋃ (( fun rho =>
            ⟦ S0 ; While m [[qv_m]] Do S0 End ⟧ ({{ Mapply m true rho }}) 
            + {{ Mapply m false rho }}) [<] rho_s).
Proof.
    deSem_killer.
    apply a0.
    instantiate(1 := x7.+1 ).
    deSem_killer.
Qed.

Lemma DeSem_seq {qs : QvarScope} S1 S2 (rho_s : 𝒫(𝒟( qs )⁻)):
    ⟦ S1 ; S2 ⟧ (rho_s) =  ⟦ S2 ⟧ ( ⟦ S1 ⟧ (rho_s) ).
Proof.
    deSem_killer. apply a0.
    instantiate(1 := (max x1 x5).+1). deSem_killer.
    instantiate(1 := x3). 
    apply (set_belong_cut (⦗ S1, x5 ⦘(x7))) => //.
    apply deSemN_point_monotonic_strong. apply /leP. apply Nat.le_max_r.
    apply (set_belong_cut (⦗ S2, x1 ⦘(x3))) => //.
    apply deSemN_point_monotonic_strong. apply /leP. apply Nat.le_max_l.
Qed.    


Lemma DeSem_atom {qs : QvarScope} P (rho_s : 𝒫(𝒟( qs )⁻)):
    ⟦ <<P>> ⟧ (rho_s) =  ⟦ P ⟧ (rho_s).
Proof.
    deSem_killer.
    instantiate (1:=x1.+1).
    deSem_killer.
Qed.


Lemma DeSem_para {qs : QvarScope} S1 S2 (rho_s : 𝒫(𝒟( qs )⁻)):
    ⟦ [S1 // S2] ⟧ (rho_s) = 
        ⟦ Step S1 S2 true ⟧ (rho_s) ∪ ⟦ Step S1 S2 false ⟧ (rho_s).
Proof.
    deSem_killer.
    all : instantiate (1:=x1.+1); deSem_killer.
Qed.

(*
(** The chain of chain_deSemN_point *)

Definition deSemN_point_map_chain 
    {qs : QvarScope} (P : prog qs) ch n : chain (𝒫(𝒟(qs)⁻)) :=
    fmap_chain (⦗ P, n ⦘) ch.


(** The relation between three chains: 
    - bigU chain
    - deSemN_point chain
    - deSemN chain
*)

Lemma deSem_chain_decompose 
    {qs : QvarScope} (P : prog qs) rho_s n :
    deSemN_chain P rho_s n = bigU_chain (deSemN_point_map_chain P rho_s n).
Proof. 
    apply chain_eqP. apply functional_extensionality => i.
    rewrite /deSemN_chain /deSemN_chain_obj {1}/chain_obj.
    rewrite /bigU_chain /bigU_chain_obj {2}/chain_obj.
    rewrite /deSemN_point_map_chain /fmap_chain /fmap_chain_obj {2}/chain_obj.
    by [].
Qed.


(*#########################################################################*)









(** Here is some dirty work about empty set *)
Lemma lim_ch_em_ex_em (qs : QvarScope) (ch : chain qs) :
    (lim→∞ (ch)) = ∅ -> exists i, ch _[i] = ∅.
Proof.
    (** This is not true. *)
Abort.

Lemma lim_ch_em_deSemN_point_em (qs : QvarScope) (S : prog qs) (ch : chain 𝒟(qs)⁻) n:
    (lim→∞ (ch)) = ∅ -> (lim→∞ (deSemN_point_map_chain S ch n)) = ∅.
Admitted.

Lemma lim_ch_em_deSemN_em (qs : QvarScope) (S : prog qs) (ch : chain 𝒟(qs)⁻) n:
    (lim→∞ (ch)) = ∅ -> (lim→∞ (deSemN_chain S ch n)) = ∅.
Proof.
    move => Hem.
    rewrite deSem_chain_decompose. rewrite -bigU_continuous. 
    rewrite lim_ch_em_deSemN_point_em //. by apply big_union_em.
Qed.

Lemma lim_ch_nem_chi_nem (qs : QvarScope) (ch : chain 𝒟( qs )⁻) i :
    (lim→∞ (ch)) <> ∅ -> ch _[i] <> ∅.
Proof.
    move => Hch. have Htemp := (@chain_limit_ub _ ch i).
    move => Heq. apply /Hch /subset_emP. rewrite -Heq. apply Htemp.
Qed.


Theorem deSem0_continuous (qs : QvarScope) (S : prog qs) (ch : chain 𝒟(qs)⁻):
    ⟦ S, 0 ⟧ (lim→∞ (ch)) = lim→∞ (deSemN_chain S ch 0).
Proof.
    case (em_classic (lim→∞ (ch))).
    move => H. rewrite H deSem0_em. rewrite lim_ch_em_deSemN_em //.
    move => H. rewrite deSem0_nem //. apply poset_antisym => //.
    apply chain_limit_lub => i. 
    rewrite /deSemN_chain /deSemN_chain_obj {1}/chain_obj. 
    rewrite deSem0_nem //. by apply lim_ch_nem_chi_nem.
Qed.


Theorem deSemN_point_continuous 
    (qs : QvarScope) (S : prog qs) (ch : chain 𝒟(qs)⁻) n:
    ⦗ S, n ⦘ [<] (lim→∞ (ch)) = lim→∞ (deSemN_point_map_chain S ch n).
Proof. 
    apply fmap_continuous.
Qed.



(** TODO #8 *)
Theorem deSemN_continuous (qs : QvarScope) (S : prog qs) (ch : chain 𝒟(qs)⁻) n:
        ⟦ S, n ⟧ (lim→∞ (ch)) = lim→∞ (deSemN_chain S ch n).
Proof.
    rewrite /deSemN /fun_comp.
    rewrite deSemN_point_continuous bigU_continuous.
    by rewrite deSem_chain_decompose.
Qed.



*)
End QParallelProg.


