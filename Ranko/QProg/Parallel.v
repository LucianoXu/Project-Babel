(** Parallel.v : describing parallel quantum programs *)

From Ranko Require Import TerminalDogma.premises 
                          TerminalDogma.Extensionality.

From Ranko Require Import QTheory.

From Coq Require Import Classical.
From Coq Require Import Arith.

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
    | <<S0>> => qvar_of_prog S0
    | [ S1 // S2 ] => (qvar_of_prog S1) [+] (qvar_of_prog S2)
    end.
Coercion qvar_of_prog : prog >-> Qvar.

(** The configuration of computation *)
Inductive cfg (qs : QvarScope): Type :=
| Srho_pair (S0 : prog qs) (rho_s : 𝒫(𝒟( qs )⁻))
| Terminated (rho_s : 𝒫(𝒟( qs )⁻)).
Notation " <{ S0 , rho_s }> " := (@Srho_pair _ S0 rho_s ) : QPP_scope.
Notation " <{ '↓' , rho_s }> " := (@Terminated _ rho_s) : QPP_scope.


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

(** Define the operational semantics *)
Fixpoint opSemN {qs : QvarScope} (c : cfg qs) (n : nat) : 𝒫(𝒟( qs )⁻) :=
    match c with
    | <{ ↓ , rho_s }> => rho_s
    | <{ P , rho_s }> => 
        match n with
        | 0 => PDensitySet_uni
        | n'.+1 => 
            match P with
            | Skip => 
                rho_s
            | Abort => 
                PDensitySet_uni
            | qv <- 0 => 
                InitSttS qv rho_s
            | qv *= U => 
                UapplyS U rho_s
            | If m [[ qv_m ]] Then P0 Else P1 End =>
                (opSemN <{ P0, MapplyS m true rho_s }> n')
                + (opSemN <{ P1, MapplyS m false rho_s }> n')
            | While m [[ qv_m ]] Do P0 End  =>
                (opSemN <{ P0;; While m [[ qv_m ]] Do P0 End 
                        , MapplyS m true rho_s }> n')
                + MapplyS m false rho_s
            | S1 ;; S2 => 
                opSemN <{ S2 , opSemN <{S1, rho_s}> n' }> n'
            | << P >> => 
                opSemN <{ P, rho_s }> n'
            | [ S1 // S2 ] => 
                (** Note that here we give a different interpretation of 
                    nested parallel composition *)
                (opSemN <{ Step S1 S2 true , rho_s }> n')
                ∪ (opSemN <{ Step S1 S2 false , rho_s }> n')
            end
        end
    end.


Lemma opSemN_seq_ex {qs : QvarScope} S0 S1 :
        forall rho_s n, exists a b, opSemN <{ S0 ;; S1, rho_s }> n = 
                @opSemN qs <{ S1 , opSemN <{ S0, rho_s}> a }> b.
Proof.
    (** This property does not hold in the finite situation, because S0 can
        have branches of different lengths. *)
Abort.

Lemma opSemN_seq {qs : QvarScope} S0 S1 :
        forall rho_s n, opSemN <{ S0 ;; S1, rho_s }> n.+1 = 
                @opSemN qs <{ S1 , opSemN <{ S0, rho_s}> n }> n.
Proof. move => rho_s. by case. Qed.


Lemma opSemN_if {qs : QvarScope} qv_m m S0 S1: 
        forall rho_s n, opSemN <{ If m [[ qv_m ]] Then S0 Else S1 End , rho_s }> n.+1
                    = opSemN <{ S0, MapplyS m true rho_s }> n
                        + @opSemN qs <{ S1, MapplyS m false rho_s }> n.
Proof. move => rho_s. by case. Qed.

Lemma opSemN_while {qs : QvarScope} qv_m m S0:
        forall rho_s n, opSemN <{ While m [[ qv_m ]] Do S0 End , rho_s }> n.+1
                    = opSemN <{ S0;; While m [[ qv_m ]] Do S0 End , 
                            MapplyS m true rho_s }> n
                        + (@MapplyS qs qv_m m false rho_s).
Proof. move => rho_s. by case. Qed.

Lemma opSemN_atom {qs : QvarScope} P :
        forall rho_s n, opSemN <{ <<P>>, rho_s }> n.+1
                    = @opSemN qs <{ P, rho_s }> n.
Proof. move => rho_s. by case. Qed.

Lemma opSemN_parallel {qs : QvarScope} S1 S2 :
        forall rho_s n, opSemN <{ [ S1 // S2 ], rho_s }> n.+1
                    = (opSemN <{ Step S1 S2 true , rho_s }> n)
                        ∪ (@opSemN qs <{ Step S1 S2 false , rho_s }> n).
Proof. move => rho_s. by case. Qed.






(* The relation between opSemN and order *)
Lemma PDenSetOrder_opSemN_strong {qs : QvarScope} :
    forall (S0 : prog qs) (r1 r2 : 𝒫(𝒟( qs )⁻)) n i, 
        i <= n -> r1 ⊑♯ r2 -> opSemN <{ S0 , r1 }> i ⊑♯ opSemN <{ S0 , r2 }> i.
Proof. 
    move => S0 r1 r2 n.

    (* induction on n *)
    elim: n S0 r1 r2.
    (* induction basis, n = 0*)
    move => S0 r1 r2 i. rewrite leqn0 => /eqP ->. by reflexivity.

    (* induction step, process i=0 first *)
    move => n IHn S0 r1 r2 i Hi Hr1r2. case: i Hi.
    by reflexivity.

    move => i Hi.
    (* case on programs *)
    case: S0.
    (* skip *)
    by move => //=.
    (* abort *)
    move => //=. by reflexivity.
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
    move => S1 S2 //=. apply IHn => //. by apply IHn => //.
    (* atom *)
    move => S0 => //=. by apply IHn => //.
    (* parallel *)
    move => S1 S2. rewrite !opSemN_parallel. 
    by apply PDenSetOrder_union_split; apply IHn.
Qed.

Lemma PDenSetOrder_opSemN {qs : QvarScope} :
    forall (S0 : prog qs) (r1 r2 : 𝒫(𝒟( qs )⁻)) n, 
        r1 ⊑♯ r2 -> opSemN <{ S0 , r1 }> n ⊑♯ opSemN <{ S0 , r2 }> n.
Proof.
    move => S0 r1 r2 n.
    by apply (@PDenSetOrder_opSemN_strong qs S0 r1 r2 n n).
Qed.



(** Prove that [opSemN c i] is increasing when i increases. *)
Lemma opSemN_inc_strong {qs : QvarScope} : 
    forall (c : cfg qs) n i, i <= n -> opSemN c i ⊑♯ opSemN c i.+1.
Proof.
    (** process terminated configurations first *)
    move => []; last first.
    move => rho_s n. case => //=; by reflexivity.

    (* induction on n *)
    move => S0 rho_s n. elim : n S0 rho_s.

    (* induction basi, n = 0 *)
    move => S0 rho_s i. rewrite leqn0 => /eqP ->. by apply PDenSet_uni_least.

    (* induction step, process i=0 first *)
    move => n IHn S0 rho_s. case.
    move => _ //=. by apply PDenSet_uni_least.
    
    (* case on programs *)
    case : S0 rho_s.

    (* skip, abort, init, unitary *)
    1,2,3,4: move => i Hi => //=; by reflexivity.
    
    (* if *)
    move => qv_m m S0 S1 rho_s i Hi. rewrite !opSemN_if.
    by apply PDenSetOrder_add_split; apply /IHn.

    (* while *)
    move => qv_m m S0 rho_s i Hi. rewrite !opSemN_while.
    apply PDenSetOrder_add_split. by apply /IHn. by reflexivity.

    (* seq *)
    move => S1 S2 rho_s i Hi. rewrite !opSemN_seq.
    transitivity (opSemN <{ S2, opSemN <{ S1, rho_s }> i.+1 }> i).
    apply PDenSetOrder_opSemN. (* Here the relation on order and opSemN is used. *)
    by apply IHn.
    by apply IHn.

    (* atom *)
    move => S0 rho_s i Hi. rewrite !opSemN_atom.
    by apply IHn.

    (* parallel *)
    move => S1 S2 rho_s i Hi. rewrite !opSemN_parallel.
    apply PDenSetOrder_union_split; by apply IHn.
Qed.

Lemma opSemN_inc_step {qs : QvarScope} : 
    forall (c : cfg qs) n, opSemN c n ⊑♯ opSemN c n.+1.
Proof. move => c n. by apply (@opSemN_inc_strong qs c n n). Qed.

Lemma opSemN_inc {qs : QvarScope} : 
    forall (c : cfg qs) i n, i <= n -> opSemN c i ⊑♯ opSemN c n.
Proof.
    (** process terminated configurations first *)
    case; last first.
    move => rho_s. case. case.
    move => _. by reflexivity.
    move => n _. by reflexivity.
    move => i n. elim: n.
    move => _. by reflexivity.
    move => n _ _. by reflexivity.

    move => S0 rho_s.

    (* we prove a equivalent proposition, which is easier to be proved. *)
    have temp : forall (i x : nat),
        opSemN <{ S0, rho_s }> i ⊑♯ opSemN <{ S0, rho_s }> (x + i)%nat.
    { move => i. elim. by reflexivity.
        move => n IHn. replace (n.+1 + i)%nat with (n + i).+1; last first.
            by [].
            transitivity (opSemN <{ S0, rho_s }> (n + i)).
            by apply IHn.
            by apply opSemN_inc_step. }

    move => i n Hi.
    replace n with (i + (n - i)%nat)%nat; last first.
    by apply subnKC.
    
    replace (i + (n - i))%nat with ((n-i)%nat+i)%nat; last first.
    apply Nat.add_comm.
    apply temp.
Qed.





(** Define the operationa semantics (infinite step) *)
Definition chain_opSemN {qs : QvarScope} (P : prog qs) rho_s : chain qs :=
    {|  chain_obj := fun n=>opSemN <{P,rho_s}> n; 
        chain_prop := fun n=>opSemN_inc_step <{P,rho_s}> n |}.

(* TODO we can implement a general lemma for monotonic functions *)
Lemma chain_opSemN_n {qs : QvarScope} (P : prog qs) rho_s n :
        chain_opSemN P rho_s _[n] = opSemN <{P, rho_s}> n.
Proof. by []. Qed.
    
Definition OpSem {qs : QvarScope} (P : prog qs) rho_s : 𝒫(𝒟( qs )⁻) :=
    lim→∞ (chain_opSemN P rho_s).

Notation " '⟦' P '⟧' ( rho_s ) " := (@OpSem _ P rho_s) : QPP_scope.

Lemma OpSem_ub : forall {qs : QvarScope} n (P : prog qs) rho_s, 
    opSemN <{P, rho_s}> n ⊑♯ ⟦ P ⟧ (rho_s).
Proof. 
    rewrite /OpSem => qs n P rho_s. rewrite -chain_opSemN_n. 
    by apply chain_limit_ub.
Qed.

Lemma OpSem_lub : forall {qs : QvarScope} (P : prog qs) rho_s rho_ub, 
    (forall n, opSemN <{P, rho_s}> n ⊑♯ rho_ub) -> ⟦ P ⟧ (rho_s) ⊑♯ rho_ub.
Proof.
    rewrite /OpSem => qs P rho_s rho_ub H. apply chain_limit_lub. by apply H.
Qed.

Lemma OpSem_lubP : forall {qs : QvarScope} (P : prog qs) rho_s rho_ub, 
    (forall n, opSemN <{P, rho_s}> n ⊑♯ rho_ub) <-> ⟦ P ⟧ (rho_s) ⊑♯ rho_ub.
Proof. split. by apply OpSem_lub.
    move => HP n. transitivity (⟦ P ⟧ (rho_s)) => //. 
    by apply OpSem_ub.
Qed.


(** Properties of Operationl Semantics *)

Lemma OpSem_skip {qs : QvarScope} (rho_s : 𝒫(𝒟( qs )⁻)):
    ⟦ Skip ⟧ (rho_s) = rho_s.
Proof.
    apply PDenSetOrder_asymm.
    apply OpSem_lub. case. by apply PDenSet_uni_least.
    move => n //=. by reflexivity.
    transitivity (opSemN <{ Skip, rho_s }> 1). by reflexivity.
    by apply OpSem_ub.
Qed.

Lemma OpSem_abort {qs : QvarScope} (rho_s : 𝒫(𝒟( qs )⁻)):
    ⟦ Abort ⟧ (rho_s) = PDensitySet_uni.
Proof.
    apply PDenSetOrder_asymm.
    apply OpSem_lub. case. by apply PDenSet_uni_least.
    move => n //=. by reflexivity.
    transitivity (opSemN <{ Abort, rho_s }> 1). by reflexivity.
    by apply OpSem_ub.
Qed.

Lemma OpSem_init {qs : QvarScope} qv (rho_s : 𝒫(𝒟( qs )⁻)):
    ⟦ qv <- 0 ⟧ (rho_s) = InitSttS qv rho_s.
Proof.
    apply PDenSetOrder_asymm.
    apply OpSem_lub. case. by apply PDenSet_uni_least.
    move => n //=. by reflexivity.
    transitivity (opSemN <{ qv <- 0, rho_s }> 1). by reflexivity.
    by apply OpSem_ub.
Qed.

Lemma OpSem_unitary {qs : QvarScope} qv U (rho_s : 𝒫(𝒟( qs )⁻)):
    ⟦ qv *= U ⟧ (rho_s) = UapplyS U rho_s.
Proof.
    apply PDenSetOrder_asymm.
    apply OpSem_lub. case. by apply PDenSet_uni_least.
    move => n //=. by reflexivity.
    transitivity (opSemN <{ qv *= U, rho_s }> 1). by reflexivity.
    by apply OpSem_ub.
Qed.


Lemma OpSem_if {qs : QvarScope} qv_m m S0 S1 (rho_s : 𝒫(𝒟( qs )⁻)):
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
    apply OpSem_lub. case. by apply PDenSet_uni_least.
    move => n //=. apply PDenSetOrder_add_split; apply OpSem_ub.

    (* proof : ⟦IF⟧ is the upper bound, therefore larger than lub ⟦S0⟧ + ⟦S1⟧.
        For this purpose we need the continuity of add. *)
    rewrite ![⟦ _ ⟧ (MapplyS m _ rho_s)]/OpSem. rewrite add_continuous.
    apply chain_limit_lub => l. rewrite /chain_add /chain_add_obj => //=.
    rewrite -opSemN_if. by apply OpSem_ub.
Qed.


Lemma OpSem_while {qs : QvarScope} qv_m m S0 (rho_s : 𝒫(𝒟( qs )⁻)):
    ⟦ While m [[qv_m]] Do S0 End ⟧ (rho_s) 
        = ⟦ S0 ;; While m [[qv_m]] Do S0 End ⟧ (MapplyS m true rho_s) 
            + MapplyS m false rho_s.
Proof.
    apply PDenSetOrder_asymm.

    apply OpSem_lub. case. by apply PDenSet_uni_least.
    move => n //=. apply PDenSetOrder_add_split. 
    by apply OpSem_ub. by reflexivity.


    rewrite [⟦ _ ⟧ (MapplyS m _ rho_s)]/OpSem.

    (* We need to transform the [MapplyS m rho_s false] term into a singleton
        chain. *)
    rewrite -(singleton_chain_limit (MapplyS m false rho_s)).
    rewrite add_continuous.
    apply chain_limit_lub => l. rewrite /chain_add /chain_add_obj => //=.
    rewrite -opSemN_while. by apply OpSem_ub.
Qed.


(* The chain of opSemN ch (different from chain_opSemN) *)
Definition opSemN_chain_obj {qs : QvarScope} (S : prog qs) (ch : chain qs) n :=
    fun i => opSemN <{S, ch _[i]}> n.

Lemma opSemN_chain_prop {qs : QvarScope} (S : prog qs) (ch : chain qs) n
    : forall i, opSemN_chain_obj S ch n i ⊑♯ opSemN_chain_obj S ch n i.+1.
Proof. 
    rewrite /opSemN_chain_obj => i. apply PDenSetOrder_opSemN.
    by apply ch.
Qed.

Definition opSemN_chain {qs : QvarScope} (S : prog qs) (ch : chain qs) n :=
    mk_chain (opSemN_chain_prop S ch n).



Theorem opSemN_continuous (qs : QvarScope) (S : prog qs) (ch : chain qs) n:
        opSemN <{S, lim→∞ (ch)}> n = lim→∞ (opSemN_chain S ch n).
Proof.
    elim: n S ch.
    (* induction basis *)
    move => S ch //=. apply PDenSetOrder_asymm.
    by apply PDenSet_uni_least.
    apply chain_limit_lub. rewrite /opSemN_chain /opSemN_chain_obj //=. by reflexivity.

    (* induction step, case on program [S] *)
    move => n IHn. case.
    (* skip *)
    move => ch.
    rewrite /opSemN_chain /opSemN_chain_obj => //=. f_equal. 
    by apply /chain_eqP.
    (* abort *) 
    move => ch //=. apply PDenSetOrder_asymm. 
    by apply PDenSet_uni_least.
    apply chain_limit_lub. rewrite /opSemN_chain /opSemN_chain_obj //=. 
    by reflexivity.
    (* init *)
    move => ch qv //=. rewrite init_continuous. f_equal. 
    apply /chain_eqP => //.
    (* unitary *)
    move => ch qv U //=. rewrite unitary_continuous. f_equal. 
    apply /chain_eqP => //.
    (* if *)
    move => qv_m m S0 S1 ch. rewrite opSemN_if.
    rewrite !mea_continuous !IHn add_continuous. f_equal. apply /chain_eqP => //.
    (* While *)
    move => qv_m m S0 ch. rewrite opSemN_while.
    rewrite !mea_continuous IHn add_continuous. f_equal. apply /chain_eqP => //.
    (* Seq *)
    move => S1 S2 ch. rewrite opSemN_seq.
    rewrite !IHn. f_equal. apply /chain_eqP => //.
    (* atom *)
    move => S0 ch. rewrite opSemN_atom.
    rewrite IHn. f_equal. apply /chain_eqP => //.
    (* parallel *)
    move => S1 S2 ch. rewrite opSemN_parallel.
    rewrite !IHn union_continuous. f_equal. apply /chain_eqP => //.
Qed.



Lemma OpSem_seq {qs : QvarScope} S1 S2 (rho_s : 𝒫(𝒟( qs )⁻)):
    ⟦ S1 ;; S2 ⟧ (rho_s) =  ⟦ S2 ⟧ ( ⟦ S1 ⟧ (rho_s) ).
Proof.
    apply PDenSetOrder_asymm.

    apply OpSem_lub. case. by apply PDenSet_uni_least.
    move => n //=. transitivity (opSemN <{ S2, ⟦ S1 ⟧ (rho_s) }> n).
    apply PDenSetOrder_opSemN. by apply OpSem_ub.
    by apply OpSem_ub.

    apply OpSem_lub => n.
    rewrite [⟦ S1 ⟧(_)]/OpSem. rewrite opSemN_continuous.
    apply chain_limit_lub => i.
    rewrite /opSemN_chain /opSemN_chain_obj //=.
    
    (* using [max i n] steps in [S1 ;; S2] *)
    move : (OpSem_ub (max i n).+1 (S1;;S2) rho_s) => //=.
    case E : (i <= n). 
    { move /leP : E => E. rewrite (max_r _ _ E) => H.
    transitivity (opSemN <{ S2, opSemN <{ S1, rho_s }> n }> n).
    apply PDenSetOrder_opSemN.
    by apply /opSemN_inc /leP.
    by apply H. }
    move /leP /Nat.lt_nge /Nat.lt_le_incl: E => E. rewrite (max_l _ _ E) => H.
    transitivity (opSemN <{ S2, opSemN <{ S1, rho_s }> i }> i).
    by apply /opSemN_inc /leP.
    by apply H.
Qed.    

Lemma OpSem_atom {qs : QvarScope} P (rho_s : 𝒫(𝒟( qs )⁻)):
    ⟦ <<P>> ⟧ (rho_s) =  ⟦ P ⟧ (rho_s).
Proof.

    apply PDenSetOrder_asymm.

    apply OpSem_lub. case => //=. by apply PDenSet_uni_least.
    move => n. by apply (OpSem_ub n).

    apply OpSem_lub => n. rewrite -opSemN_atom. by apply OpSem_ub.
Qed.

Lemma OpSem_para {qs : QvarScope} S1 S2 (rho_s : 𝒫(𝒟( qs )⁻)):
    ⟦ [S1 // S2] ⟧ (rho_s) = 
        ⟦ Step S1 S2 true ⟧ (rho_s) ∪ ⟦ Step S1 S2 false ⟧ (rho_s).
Proof.
    apply PDenSetOrder_asymm.

    apply OpSem_lub. case. by apply PDenSet_uni_least.
    move => n. rewrite opSemN_parallel. 
    apply PDenSetOrder_union_split; by apply OpSem_ub.

    rewrite ![⟦ Step _ _ _ ⟧(rho_s)]/OpSem. 
    rewrite union_continuous. apply chain_limit_lub => l.
    rewrite /chain_union /chain_union_obj /chain_opSemN /chain_obj => //.
    rewrite -opSemN_parallel. by apply OpSem_ub.
Qed.

End QParallelProg.
    




    