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

Reserved Notation " ⟦ P , n ⟧ ( rho_s ) " 
    (format "⟦  P ,  n  ⟧ ( rho_s )").
Reserved Notation " ⟦ ↓ ⟧ ( rho_s ) " 
    (only printing, format "⟦  ↓  ⟧ ( rho_s )").

(** Define the denotational semantics of calculating n steps 
    parameter :
        [P : option (prog qs)], if [P] is [None] then the program is 
            terminated.*)
Fixpoint deSemN {qs : QvarScope} (P : option (prog qs)) (n : nat)
    (rho_s : 𝒫(𝒟( qs )⁻)) : 𝒫(𝒟( qs )⁻) :=
    match P with
    | None => rho_s
    | Some P => 
        match n with
        | 0 => {U}
        | n'.+1 => 
            match P with
            | Skip => 
                rho_s

            | Abort => 
                {U} 
                (** Note : universal set is necessary here. Otherwise, it's
                    hard to construct the infimum set. *)

            | qv <- 0 => 
                InitSttS qv rho_s

            | qv *= U => 
                UapplyS U rho_s

            | If m [[ qv_m ]] Then P0 Else P1 End =>
                (⟦ P0, n' ⟧ ( MapplyS m true rho_s ))
                + (⟦ P1, n' ⟧ ( MapplyS m false rho_s ))

            | While m [[ qv_m ]] Do P0 End  =>
                ⟦ P0;; While m [[ qv_m ]] Do P0 End, n' ⟧ (MapplyS m true rho_s)
                + MapplyS m false rho_s

            | S1 ;; S2 => 
                ⟦ S2, n' ⟧ (⟦ S1, n' ⟧ (rho_s))

            | S1 [ p ⊕ ] S2 =>
                (⟦ S1, n' ⟧(rho_s) [ p ⊕ ] ⟦ S2, n'⟧(rho_s))%QTS

            | S1 □ S2 =>
                ⟦ S1, n' ⟧(rho_s) ∪ ⟦ S2, n' ⟧(rho_s)

            | << P >> => 
                ⟦ P, n' ⟧ (rho_s)

            | [ S1 // S2 ] => 
                (** Note that here we give a different interpretation of 
                    nested parallel composition *)
                (⟦ Step S1 S2 true, n'⟧ (rho_s))
                ∪ (⟦ Step S1 S2 false, n'⟧ (rho_s))

            end
        end
    end
    where " ⟦ P , n ⟧ ( rho_s ) " := (deSemN (Some P) n rho_s) : QPP_scope.

Notation " ⟦ ↓ ⟧ ( rho_s ) " := (deSemN None _ rho_s) :QPP_scope.


Lemma deSemN_seq_ex {qs : QvarScope} S0 S1 :
        forall (rho_s : 𝒫(𝒟( qs )⁻)) n, exists a b, 
        
            ⟦ S0 ;; S1, n ⟧ (rho_s) = ⟦ S1 , b ⟧ (⟦ S0, a ⟧ (rho_s)).

Proof.
    (** This property does not hold in the finite situation, because S0 can
        have branches of different lengths. *)
Abort.

Lemma deSemN_seq {qs : QvarScope} S0 S1 :
        forall (rho_s : 𝒫(𝒟( qs )⁻)) n, 

            ⟦ S0 ;; S1, n.+1 ⟧ (rho_s) = ⟦ S1 , n ⟧ (⟦ S0, n ⟧ (rho_s)).

Proof. by []. Qed.


Lemma deSemN_if {qs : QvarScope} qv_m m S0 S1: 
        forall (rho_s : 𝒫(𝒟( qs )⁻)) n,

            ⟦ If m [[ qv_m ]] Then S0 Else S1 End , n.+1 ⟧ (rho_s)
            = ⟦ S0, n ⟧ (MapplyS m true rho_s) 
                + ⟦ S1, n ⟧ (MapplyS m false rho_s).

Proof. by []. Qed.


Lemma deSemN_while {qs : QvarScope} qv_m m S0:
        forall (rho_s : 𝒫(𝒟( qs )⁻)) n, 
        
            ⟦ While m [[ qv_m ]] Do S0 End, n.+1 ⟧(rho_s)
            = ⟦ S0;; While m [[ qv_m ]] Do S0 End, n ⟧ (MapplyS m true rho_s)
                + (MapplyS m false rho_s).

Proof. by []. Qed.


Lemma deSemN_prob {qs : QvarScope} p S1 S2:
        forall (rho_s : 𝒫(𝒟( qs )⁻)) n, 

            ⟦ S1 [ p ⊕ ] S2, n.+1 ⟧ (rho_s)
            = (⟦ S1, n ⟧(rho_s) [ p ⊕ ] ⟦ S2, n⟧(rho_s))%QTS.

Proof. by []. Qed.


Lemma deSemN_nondet {qs : QvarScope} S1 S2:
        forall (rho_s : 𝒫(𝒟( qs )⁻)) n, 
        
            ⟦ S1 □ S2, n.+1 ⟧ (rho_s)
            = ⟦ S1, n ⟧(rho_s) ∪ ⟦ S2, n ⟧(rho_s).

Proof. by []. Qed.


Lemma deSemN_atom {qs : QvarScope} P :
        forall (rho_s : 𝒫(𝒟( qs )⁻)) n, 
        
            ⟦ <<P>>, n.+1 ⟧ (rho_s) = ⟦ P, n ⟧ (rho_s).

Proof. by []. Qed.


Lemma deSemN_parallel {qs : QvarScope} S1 S2 :
        forall (rho_s : 𝒫(𝒟( qs )⁻)) n, 
        
            ⟦ [ S1 // S2 ], n.+1 ⟧ (rho_s) 
            = (⟦ Step S1 S2 true, n ⟧ (rho_s))
                ∪ (⟦ Step S1 S2 false, n ⟧ (rho_s)).

Proof. by []. Qed.





(* The strong relation between opSemN and order *)
Lemma deSemN_monotonic_strong {qs : QvarScope} :
    forall (S0 : prog qs) (r1 r2 : 𝒫(𝒟( qs )⁻)) (n i : nat), 
        (i <= n)%nat -> r1 ⊑♯ r2 -> ⟦ S0, i ⟧ (r1) ⊑♯ ⟦ S0, n ⟧ (r2).
Proof. 
    move => S0 r1 r2 n.

    (* induction on n *)
    elim: n S0 r1 r2.
    (* induction basis, n = 0*)
    move => S0 r1 r2 i. rewrite leqn0 => /eqP ->. by reflexivity.

    (* induction step, process i=0 first *)
    move => n IHn S0 r1 r2 i Hi Hr1r2. case: i Hi.
    move => _. by apply PDenSet_uni_least.

    move => i Hi.
    (* case on programs *)
    case: S0.
    (* skip, abort *)
    1, 2 : by [].
    (* init *)
    move => qv //=. by apply PDenSetOrder_Init.
    (* unitary *)
    move => qv U //=. by apply PDenSetOrder_U.
    (* if *)
    move => qv_m m S0 S1 //=. 
    by apply PDenSetOrder_add_split; apply /IHn => //; apply PDenSetOrder_M.
    (* while *)
    move => qv_m m S0 //=.
    apply PDenSetOrder_add_split; last first. by apply PDenSetOrder_M.
    apply IHn => //. by apply PDenSetOrder_M.
    (* sequence *)
    move => S1 S2 //=. apply IHn => //. by apply IHn.
    (* probability *)
    move => p S1 S2 //=. apply PDensetOrder_cv_comb_split; by apply IHn.
    (* nondet*)
    move => S1 S2 //=. apply PDenSetOrder_union_split; by apply IHn.
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
    (format "⟦  P  ⟧ ( rho_s )"): QPP_scope.

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


(** Properties of Operationl Semantics *)

Lemma DeSem_skip {qs : QvarScope} (rho_s : 𝒫(𝒟( qs )⁻)):
    ⟦ Skip ⟧ (rho_s) = rho_s.
Proof.
    apply PDenSetOrder_asymm.
    apply DeSem_lub. case. by apply PDenSet_uni_least.
    by move => n //=.
    transitivity (⟦ Skip, 1 ⟧(rho_s)). by reflexivity.
    by apply DeSem_ub.
Qed.

Lemma DeSem_abort {qs : QvarScope} (rho_s : 𝒫(𝒟( qs )⁻)):
    ⟦ Abort ⟧ (rho_s) = {U}.
Proof.
    apply PDenSetOrder_asymm.
    apply DeSem_lub. case. by apply PDenSet_uni_least.
    by move => n //=.
    transitivity (⟦ Abort, 1 ⟧(rho_s)). by reflexivity.
    by apply DeSem_ub.
Qed.

Lemma DeSem_init {qs : QvarScope} qv (rho_s : 𝒫(𝒟( qs )⁻)):
    ⟦ qv <- 0 ⟧ (rho_s) = InitSttS qv rho_s.
Proof.
    apply PDenSetOrder_asymm.
    apply DeSem_lub. case. by apply PDenSet_uni_least.
    by move => n //=.
    transitivity (⟦ qv <- 0, 1 ⟧ (rho_s)). by reflexivity.
    by apply DeSem_ub.
Qed.

Lemma DeSem_unitary {qs : QvarScope} qv U (rho_s : 𝒫(𝒟( qs )⁻)):
    ⟦ qv *= U ⟧ (rho_s) = UapplyS U rho_s.
Proof.
    apply PDenSetOrder_asymm.
    apply DeSem_lub. case. by apply PDenSet_uni_least.
    by move => n //=.
    transitivity (⟦ qv *= U, 1⟧ (rho_s)). by reflexivity.
    by apply DeSem_ub.
Qed.


Lemma DeSem_if {qs : QvarScope} qv_m m S0 S1 (rho_s : 𝒫(𝒟( qs )⁻)):
    ⟦ If m [[qv_m]] Then S0 Else S1 End ⟧ (rho_s) 
        = ⟦ S0 ⟧ (MapplyS m true rho_s) + ⟦ S1 ⟧ (MapplyS m false rho_s).
Proof.
    apply PDenSetOrder_asymm.

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
    apply DeSem_lub. case. by apply PDenSet_uni_least.
    move => n //=. apply PDenSetOrder_add_split; apply DeSem_ub.

    (* proof : ⟦IF⟧ is the upper bound, therefore larger than lub ⟦S0⟧ + ⟦S1⟧.
        For this purpose we need the continuity of add. *)
    rewrite ![⟦ _ ⟧ (MapplyS m _ rho_s)]/DeSem. rewrite add_continuous.
    apply chain_limit_lub => l. rewrite /chain_add /chain_add_obj => //=.
    rewrite -deSemN_if. by apply DeSem_ub.
Qed.


Lemma DeSem_while {qs : QvarScope} qv_m m S0 (rho_s : 𝒫(𝒟( qs )⁻)):
    ⟦ While m [[qv_m]] Do S0 End ⟧ (rho_s) 
        = ⟦ S0 ;; While m [[qv_m]] Do S0 End ⟧ (MapplyS m true rho_s) 
            + MapplyS m false rho_s.
Proof.
    apply PDenSetOrder_asymm.

    apply DeSem_lub. case. by apply PDenSet_uni_least.
    move => n //=. apply PDenSetOrder_add_split. 
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



Theorem deSemN_continuous (qs : QvarScope) (S : prog qs) (ch : chain qs) n:
        ⟦ S, n ⟧ (lim→∞ (ch)) = lim→∞ (deSemN_chain S ch n).
Proof.
    elim: n S ch.
    (* induction basis *)
    move => S ch //=. apply PDenSetOrder_asymm.
    by apply PDenSet_uni_least.
    apply chain_limit_lub. by rewrite /deSemN_chain /deSemN_chain_obj //=.

    (* induction step, case on program [S] *)
    move => n IHn. case.
    (* skip *)
    move => ch.
    rewrite /deSemN_chain /deSemN_chain_obj => //=. f_equal. 
    by apply /chain_eqP.
    (* abort *) 
    move => ch //=. apply PDenSetOrder_asymm. 
    by apply PDenSet_uni_least.
    apply chain_limit_lub. by rewrite /deSemN_chain /deSemN_chain_obj. 
    (* init *)
    move => ch qv //=. rewrite init_continuous. f_equal. 
    by apply /chain_eqP.
    (* unitary *)
    move => ch qv U //=. rewrite unitary_continuous. f_equal. 
    by apply /chain_eqP.
    (* if *)
    move => qv_m m S0 S1 ch. rewrite deSemN_if.
    rewrite !mea_continuous !IHn add_continuous. f_equal. by apply /chain_eqP.
    (* While *)
    move => qv_m m S0 ch. rewrite deSemN_while.
    rewrite !mea_continuous IHn add_continuous. f_equal. by apply /chain_eqP.
    (* Seq *)
    move => S1 S2 ch. rewrite deSemN_seq.
    rewrite !IHn. f_equal. by apply /chain_eqP.
    (* probability *)
    move => p S1 S2 ch. rewrite deSemN_prob.
    rewrite !IHn cvcomb_continuous. f_equal. by apply /chain_eqP.
    (* nondeterminism *)
    move => S1 S2 ch. rewrite deSemN_nondet.
    rewrite !IHn union_continuous. f_equal. by apply /chain_eqP.
    (* atom *)
    move => S0 ch. rewrite deSemN_atom.
    rewrite IHn. f_equal. by apply /chain_eqP.
    (* parallel *)
    move => S1 S2 ch. rewrite deSemN_parallel.
    rewrite !IHn union_continuous. f_equal. by apply /chain_eqP.
Qed.



Lemma DeSem_seq {qs : QvarScope} S1 S2 (rho_s : 𝒫(𝒟( qs )⁻)):
    ⟦ S1 ;; S2 ⟧ (rho_s) =  ⟦ S2 ⟧ ( ⟦ S1 ⟧ (rho_s) ).
Proof.
    apply PDenSetOrder_asymm.

    apply DeSem_lub. case. by apply PDenSet_uni_least.
    move => n //=. transitivity (⟦ S2, n ⟧(⟦ S1 ⟧ (rho_s))).
    apply deSemN_monotonic_rho. by apply DeSem_ub.
    by apply DeSem_ub.

    apply DeSem_lub => n.
    rewrite [⟦ S1 ⟧(_)]/DeSem. rewrite deSemN_continuous.
    apply chain_limit_lub => i.
    rewrite /deSemN_chain /deSemN_chain_obj //=.
    (* using [max i n] steps in [S1 ;; S2] *)
    move : (DeSem_ub (max i n).+1 (S1;;S2) rho_s) => //=.
    case E : (i <= n)%nat. 
    { move /leP : E => E. rewrite (max_r _ _ E) => H.
    transitivity (⟦ S2, n ⟧ (⟦ S1, n ⟧(rho_s))).
    apply deSemN_monotonic_rho.
    by apply /deSemN_monotonic_N /leP.
    by apply H. }
    move /leP /Nat.lt_nge /Nat.lt_le_incl: E => E. rewrite (max_l _ _ E) => H.
    transitivity (⟦ S2, i ⟧ (⟦ S1, i ⟧(rho_s))).
    by apply /deSemN_monotonic_N /leP.
    by apply H.
Qed.    

Lemma DeSem_atom {qs : QvarScope} P (rho_s : 𝒫(𝒟( qs )⁻)):
    ⟦ <<P>> ⟧ (rho_s) =  ⟦ P ⟧ (rho_s).
Proof.

    apply PDenSetOrder_asymm.

    apply DeSem_lub. case => n //=. by apply DeSem_ub.

    apply DeSem_lub => n. rewrite -deSemN_atom. by apply DeSem_ub.
Qed.

Lemma DeSem_para {qs : QvarScope} S1 S2 (rho_s : 𝒫(𝒟( qs )⁻)):
    ⟦ [S1 // S2] ⟧ (rho_s) = 
        ⟦ Step S1 S2 true ⟧ (rho_s) ∪ ⟦ Step S1 S2 false ⟧ (rho_s).
Proof.
    apply PDenSetOrder_asymm.

    apply DeSem_lub. case. by apply PDenSet_uni_least.
    move => n. rewrite deSemN_parallel. 
    apply PDenSetOrder_union_split; by apply DeSem_ub.

    rewrite ![⟦ Step _ _ _ ⟧(rho_s)]/DeSem. 
    rewrite union_continuous. apply chain_limit_lub => l.
    rewrite /chain_union /chain_union_obj /chain_deSemN /chain_obj => //.
    rewrite -deSemN_parallel. by apply DeSem_ub.
Qed.

End QParallelProg.
    




    