From Ranko Require Import TerminalDogma.premises.
From Coq Require Import Classical.
From Coq Require Import PropExtensionality.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import Arith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** Hilbert spaces are the types of quantum variables *)
Axiom Hspace : Type.

(** The scope of quantum variable used in a program. *)
Axiom QvarScope : Type.
Axiom QvScopeType : QvarScope -> Hspace.
Coercion QvScopeType : QvarScope >-> Hspace.

(** Get the type of quantum varibles from the quantum scope.
    Here the quantum variable can refer to 'a bunch of variables' *)
Axiom getQvar : QvarScope -> Type.
Coercion getQvar : QvarScope >-> Sortclass.

(** Empty quantum variable. *)
Axiom em_var : forall qs : QvarScope, qs.

(** The operator to union two quantum varibles *)
Axiom QvarUnion : forall qs : QvarScope, qs -> qs -> qs.
Notation " a [+] b " := (@QvarUnion _ a b ) (at level 10, left associativity).

Axiom QvType : forall qs: QvarScope, qs -> Hspace.
Coercion QvType : getQvar >-> Hspace.

Axiom PDensityOpt : Hspace -> Type.
    
Axiom PDenSet : Hspace -> Type.
(** The universal set of this partial density operator *)
Axiom PDenSet_uni : forall {H}, PDenSet H.

(** Here we have the difference : we need to perform 'union' on the program
    state, but we cannot union two density operators. Therefore density 
    operator sets are needed.*)
Axiom PDenSet_Union : forall {H : Hspace}, PDenSet H -> PDenSet H -> PDenSet H.
Axiom PDenSet_Add : forall {H : Hspace}, PDenSet H -> PDenSet H -> PDenSet H.
Notation " A '∪' B " := (@PDenSet_Union _ A B) (at level 10).
Notation " A + B " := (@PDenSet_Add _ A B).

Axiom PDenSet_Add_uni_l : forall {H : Hspace} (s : PDenSet H), 
    PDenSet_uni + s = PDenSet_uni.

Axiom PDenSet_Add_uni_r : forall {H : Hspace} (s : PDenSet H), 
    s + PDenSet_uni = PDenSet_uni.

Axiom UnitaryOpt : Hspace -> Type.
Axiom MeaOpt : Hspace -> Type.

Axiom InitStt : forall {qs : QvarScope}
                       (qv_init : qs) (rho_s : PDenSet qs), PDenSet qs.
Axiom Uapply : forall (qs : QvarScope)
                      (qv_U : qs) (U : UnitaryOpt qv_U) 
                      (rho_s : PDenSet qs), PDenSet qs.
Arguments Uapply {qs qv_U}.

Axiom Mapply : forall (qs : QvarScope)
                      (qv_M : qs) (m : MeaOpt qv_M) 
                      (rho_s : PDenSet qs) (result : bool), PDenSet qs.
Arguments Mapply {qs qv_M}.

Axiom Mapply_repeat : forall (qs : QvarScope)
                        (qv_M : qs) (m : MeaOpt qv_M) 
                        (rho_s : PDenSet qs) (result : bool), 
                        Mapply m (Mapply m rho_s result) result
                        = Mapply m rho_s result.
                    

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
Notation " 'Skip' " := (@skip_ _).
Notation " 'Abort' " := (@abort_ _).
Notation " qv <- '0' " := (@init_ _ qv) (at level 10).
Notation " qv *= U " := (@unitary_ _ qv U) (at level 10).
Notation " 'If' m [[ qv_m ]] 'Then' S0 'Else' S1 'End' " := (@if_ _ qv_m m S0 S1)
    (at level 90).
Notation " 'While' m [[ qv_m ]] 'Do' S0 'End' " := (@while_ _ qv_m m S0)
    (at level 90).
Notation " S1 ;; S2 " := (@seq_ _ S1 S2) (at level 95, right associativity).
Notation " << P >> " := (@atom_ _ P).
Notation " [ S1 // S2 ] " := (@parallel_ _ S1 S2) (at level 5).

Fixpoint non_parallel {qs : QvarScope} (P : prog qs) : bool :=
    match P with 
    | [S1 // S2] => false
    | If m [[ qv_m ]] Then S0 Else S1 End => non_parallel S0 && non_parallel S1
    | While m [[ qv_m ]] Do S0 End => non_parallel S0
    | S1 ;; S2 => non_parallel S1 && non_parallel S2
    | _ => true
    end.

(**
Inductive non_double_parallel : prog -> Prop :=
| nd_skip : non_double_parallel Skip
| nd_abort : non_double_parallel Abort
| nd_init qv : non_double_parallel (qv <- 0)
| nd_unitary qv U : non_double_parallel (qv *= U)
| nd_if qv_m m S0 S1 : non_double_parallel S0 -> non_double_parallel S1 ->
                        non_double_parallel ([ If m [[ qv_m ]] Then S0 Else S1 End ])
| nd_while qv_m m S0 : non_double_parallel S0 -> 
                        non_double_parallel ([ While m [[ qv_m ]] Do S0 End ])
| nd_seq S1 S2 : non_double_parallel S1 -> non_double_parallel S2 ->
                        non_double_parallel ( S1 ;; S2 )
| nd_atom P : non_double_parallel << P >> 
| nd_parallel S1 S2 : non_parallel S1 -> non_parallel S2 -> 
                        non_double_parallel [ S1 // S2 ]. 

Fixpoint non_db_parallel (P : prog) : bool :=
    match P with
    | [ S1 // S2 ] => non_parallel S1 && non_parallel S2
    | [ If _ [[ _ ]] Then S0 Else S1 End ] => 
        non_db_parallel S0 && non_db_parallel S1
    | [ While _ [[ _ ]] Do S0 End ] => non_db_parallel S0
    | S1 ;; S2 => non_db_parallel S1 && non_db_parallel S2
    | _ => true
    end.
*)

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
Coercion qvar_of_prog : prog >-> getQvar.

(** The configuration of computation *)
Inductive cfg (qs : QvarScope): Type :=
| Srho_pair (S0 : prog qs) (rho_s : PDenSet qs)
| Terminated (rho_s : PDenSet qs).
Notation " <{ S0 , rho_s }> " := (@Srho_pair _ S0 rho_s ).
Notation " <{ '↓' , rho_s }> " := (@Terminated _ rho_s).


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
Fixpoint OpSemN {qs : QvarScope} (c : cfg qs) (n : nat) : PDenSet qs :=
    match c with
    | <{ ↓ , rho_s }> => rho_s
    | <{ P , rho_s }> => 
        match n with
        | 0 => PDenSet_uni
        | n'.+1 => 
            match P with
            | Skip => 
                rho_s
            | Abort => 
                PDenSet_uni
            | qv <- 0 => 
                InitStt qv rho_s
            | qv *= U => 
                Uapply U rho_s
            | If m [[ qv_m ]] Then P0 Else P1 End =>
                (OpSemN <{ P0, Mapply m rho_s true }> n')
                + (OpSemN <{ P1, Mapply m rho_s false }> n')
            | While m [[ qv_m ]] Do P0 End  =>
                (OpSemN <{ P0;; While m [[ qv_m ]] Do P0 End 
                        , Mapply m rho_s true }> n')
                + Mapply m rho_s false
            | S1 ;; S2 => 
                OpSemN <{ S2 , OpSemN <{S1, rho_s}> n' }> n'
            | << P >> => 
                OpSemN <{ P, rho_s }> n'
            | [ S1 // S2 ] => 
                (** Note that here we give a different interpretation of 
                    nested parallel composition *)
                (OpSemN <{ Step S1 S2 true , rho_s }> n')
                ∪ (OpSemN <{ Step S1 S2 false , rho_s }> n')
            end
        end
    end.


Lemma OpSemN_seq_ex {qs : QvarScope} S0 S1 :
        forall rho_s n, exists a b, OpSemN <{ S0 ;; S1, rho_s }> n = 
                @OpSemN qs <{ S1 , OpSemN <{ S0, rho_s}> a }> b.
Proof.
    (** This property does not hold in the finite situation, because S0 can
        have branches of different lengths. *)
Abort.

Lemma OpSemN_seq {qs : QvarScope} S0 S1 :
        forall rho_s n, OpSemN <{ S0 ;; S1, rho_s }> n.+1 = 
                @OpSemN qs <{ S1 , OpSemN <{ S0, rho_s}> n }> n.
Proof. move => rho_s. by case. Qed.


Lemma OpSemN_if {qs : QvarScope} qv_m m S0 S1: 
        forall rho_s n, OpSemN <{ If m [[ qv_m ]] Then S0 Else S1 End , rho_s }> n.+1
                    = OpSemN <{ S0, Mapply m rho_s true }> n
                        + @OpSemN qs <{ S1, Mapply m rho_s false }> n.
Proof. move => rho_s. by case. Qed.

Lemma OpSemN_while {qs : QvarScope} qv_m m S0:
        forall rho_s n, OpSemN <{ While m [[ qv_m ]] Do S0 End , rho_s }> n.+1
                    = OpSemN <{ S0;; While m [[ qv_m ]] Do S0 End , 
                            Mapply m rho_s true }> n
                        + (@Mapply qs qv_m m rho_s false).
Proof. move => rho_s. by case. Qed.

Lemma OpSemN_atom {qs : QvarScope} P :
        forall rho_s n, OpSemN <{ <<P>>, rho_s }> n.+1
                    = @OpSemN qs <{ P, rho_s }> n.
Proof. move => rho_s. by case. Qed.

Lemma OpSemN_parallel {qs : QvarScope} S1 S2 :
        forall rho_s n, OpSemN <{ [ S1 // S2 ], rho_s }> n.+1
                    = (OpSemN <{ Step S1 S2 true , rho_s }> n)
                        ∪ (@OpSemN qs <{ Step S1 S2 false , rho_s }> n).
Proof. move => rho_s. by case. Qed.


(** Arguments about order *)
Axiom PDenSetOrder : forall {H : Hspace}, PDenSet H -> PDenSet H -> Prop.
Notation " A '⊑' B " := (PDenSetOrder A B) (at level 60).


Axiom PDenSetOrder_refl : 
    forall H, Relation_Definitions.reflexive _ (@PDenSetOrder H).
Axiom PDenSetOrder_trans : 
    forall H, Relation_Definitions.transitive _ (@PDenSetOrder H).
Axiom PDenSetOrder_asymm :
    forall H, Relation_Definitions.antisymmetric _ (@PDenSetOrder H).

Add Parametric Relation H : _ (@PDenSetOrder H)
    reflexivity proved by (@PDenSetOrder_refl H)
    transitivity proved by (@PDenSetOrder_trans H) as rel_PDenSetOrder.

Axiom PDenSet_uni_least : 
    forall {H : Hspace} (s : PDenSet H), PDenSet_uni ⊑ s.

Add Parametric Morphism {H : Hspace} : (@PDenSet_Add H)
    with signature (@PDenSetOrder H) ==> (@PDenSetOrder H) 
                    ==> (@PDenSetOrder H) as add_mor_le.
Proof.
Admitted.

Lemma PDenSetOrder_add_split {H : Hspace} :
    forall {rho_s1 rho_s2 rho_s1' rho_s2': PDenSet H}, 
        rho_s1 ⊑ rho_s1' -> rho_s2 ⊑ rho_s2' 
            -> rho_s1 + rho_s2 ⊑ rho_s1' + rho_s2'.
Proof. move => a b c d Hac Hbd. rewrite Hac Hbd. by reflexivity. Qed.

Add Parametric Morphism {H : Hspace} : (@PDenSet_Union H)
    with signature (@PDenSetOrder H) ==> (@PDenSetOrder H) 
                    ==> (@PDenSetOrder H) as union_mor_le.
Proof.
Admitted.

Lemma PDenSetOrder_union_split {H : Hspace} :
    forall {rho_s1 rho_s2 rho_s1' rho_s2': PDenSet H}, 
        rho_s1 ⊑ rho_s1' -> rho_s2 ⊑ rho_s2' 
            -> rho_s1 ∪ rho_s2 ⊑ rho_s1' ∪ rho_s2'.
Proof. move => a b c d Hac Hbd. rewrite Hac Hbd. by reflexivity. Qed.

Axiom PDenSetOrder_Init : 
    forall {qs : QvarScope} r1 r2 (qv : qs), r1 ⊑ r2 -> InitStt qv r1 ⊑ InitStt qv r2.
Axiom PDenSetOrder_U : 
    forall {qs : QvarScope} r1 r2 (qv : qs) (U : UnitaryOpt qv),
        r1 ⊑ r2 -> Uapply U r1 ⊑ Uapply U r2.
Axiom PDenSetOrder_M : 
    forall {qs : QvarScope} r1 r2 (qv_m : qs) (m : MeaOpt qv_m) (result : bool),
        r1 ⊑ r2 -> Mapply m r1 result ⊑ Mapply m r2 result.


(* The relation between OpSemN and order *)
Lemma PDenSetOrder_OpSemN_strong {qs : QvarScope} :
    forall (S0 : prog qs) (r1 r2 : PDenSet qs) n i, 
        i <= n -> r1 ⊑ r2 -> OpSemN <{ S0 , r1 }> i ⊑ OpSemN <{ S0 , r2 }> i.
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
    move => S1 S2. rewrite !OpSemN_parallel. 
    by apply PDenSetOrder_union_split; apply IHn.
Qed.

Lemma PDenSetOrder_OpSemN {qs : QvarScope} :
    forall (S0 : prog qs) (r1 r2 : PDenSet qs) n, 
        r1 ⊑ r2 -> OpSemN <{ S0 , r1 }> n ⊑ OpSemN <{ S0 , r2 }> n.
Proof.
    move => S0 r1 r2 n.
    by apply (@PDenSetOrder_OpSemN_strong qs S0 r1 r2 n n).
Qed.



(** Prove that [OpSemN c i] is increasing when i increases. *)
Lemma OpSemN_inc_strong {qs : QvarScope} : 
    forall (c : cfg qs) n i, i <= n -> OpSemN c i ⊑ OpSemN c i.+1.
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
    move => qv_m m S0 S1 rho_s i Hi. rewrite !OpSemN_if.
    by apply PDenSetOrder_add_split; apply /IHn.

    (* while *)
    move => qv_m m S0 rho_s i Hi. rewrite !OpSemN_while.
    apply PDenSetOrder_add_split. by apply /IHn. by reflexivity.

    (* seq *)
    move => S1 S2 rho_s i Hi. rewrite !OpSemN_seq.
    transitivity (OpSemN <{ S2, OpSemN <{ S1, rho_s }> i.+1 }> i).
    apply PDenSetOrder_OpSemN. (* Here the relation on order and OpSemN is used. *)
    by apply IHn.
    by apply IHn.

    (* atom *)
    move => S0 rho_s i Hi. rewrite !OpSemN_atom.
    by apply IHn.

    (* parallel *)
    move => S1 S2 rho_s i Hi. rewrite !OpSemN_parallel.
    apply PDenSetOrder_union_split; by apply IHn.
Qed.

Lemma OpSemN_inc_step {qs : QvarScope} : 
    forall (c : cfg qs) n, OpSemN c n ⊑ OpSemN c n.+1.
Proof. move => c n. by apply (@OpSemN_inc_strong qs c n n). Qed.

Lemma OpSemN_inc {qs : QvarScope} : 
    forall (c : cfg qs) i n, i <= n -> OpSemN c i ⊑ OpSemN c n.
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
        OpSemN <{ S0, rho_s }> i ⊑ OpSemN <{ S0, rho_s }> (x + i)%nat.
    { move => i. elim. by reflexivity.
        move => n IHn. replace (n.+1 + i)%nat with (n + i).+1; last first.
            by [].
            transitivity (OpSemN <{ S0, rho_s }> (n + i)).
            by apply IHn.
            by apply OpSemN_inc_step. }

    move => i n Hi.
    replace n with (i + (n - i)%nat)%nat; last first.
    by apply subnKC.
    
    replace (i + (n - i))%nat with ((n-i)%nat+i)%nat; last first.
    apply Nat.add_comm.
    apply temp.
Qed.






(** Define the increasing set and least upper bound *)
Record chain (H : Hspace) := mk_chain {
    chain_obj : nat -> PDenSet H;
    chain_prop : forall n, chain_obj n ⊑ chain_obj n.+1;
}.
Notation " ch _[ n ] " := (chain_obj ch n) (at level 40).

(** Convert a singal element into a list *)
Definition singleton_chain_obj {H : Hspace} rho_s : nat -> PDenSet H :=
    fun => rho_s.

Lemma singleton_chain_prop {H : Hspace} (rho_s : PDenSet H) 
    : forall n, singleton_chain_obj rho_s n ⊑ singleton_chain_obj rho_s n.+1.
Proof. rewrite /singleton_chain_obj => n => //=. by reflexivity. Qed.

Definition singleton_chain {H : Hspace} rho_s : chain H :=
    mk_chain (singleton_chain_prop rho_s).

Coercion singleton_chain : PDenSet >-> chain.

(** Prove the loose criterion of chain equivalence *)
Lemma chain_eqP H : forall (ch1 ch2 : chain H),
        ch1 = ch2 <-> chain_obj ch1 = chain_obj ch2.
Proof. split. by move => -> //.
    move => Heq. destruct ch1 as [obj1 p1], ch2 as [obj2 p2]. simpl in Heq.
    move : p1 p2. rewrite Heq => p1 p2. by rewrite (proof_irrelevance _ p1 p2).
Qed.

Axiom chain_limit : forall H (ch : chain H), PDenSet H.
Notation " 'lim→∞' ( ch ) " := (@chain_limit _ ch) (at level 200).
Axiom chain_limit_ub : forall H (ch : chain H) n,
    ch _[n] ⊑ lim→∞ (ch).
Axiom chain_limit_lub : forall H (ch : chain H) rho_ub,
    (forall n, ch _[n] ⊑ rho_ub) -> lim→∞ (ch) ⊑ rho_ub.

Lemma singleton_chain_limit (H : Hspace) (rho_s : PDenSet H) :
    lim→∞ (rho_s) = rho_s.
Proof.
    apply PDenSetOrder_asymm.
    apply chain_limit_lub. 
    rewrite /singleton_chain /singleton_chain_obj => n => //=. by reflexivity.
    have temp := chain_limit_ub rho_s. by apply (temp 0).
Qed.

(** Define the operationa semantics (infinite step) *)
Definition chain_OpSemN {qs : QvarScope} (P : prog qs) rho_s : chain qs :=
    {|  chain_obj := fun n=>OpSemN <{P,rho_s}> n; 
        chain_prop := fun n=>OpSemN_inc_step <{P,rho_s}> n |}.
Lemma chain_OpSemN_n {qs : QvarScope} (P : prog qs) rho_s n :
        chain_OpSemN P rho_s _[n] = OpSemN <{P, rho_s}> n.
Proof. by []. Qed.
    
Definition OpSem {qs : QvarScope} (P : prog qs) rho_s : PDenSet qs :=
    lim→∞ (chain_OpSemN P rho_s).

Notation " '⟦' P '⟧' ( rho_s ) " := (@OpSem _ P rho_s).

Lemma OpSem_ub : forall {qs : QvarScope} n (P : prog qs) rho_s, 
    OpSemN <{P, rho_s}> n ⊑ ⟦ P ⟧ (rho_s).
Proof. 
    rewrite /OpSem => qs n P rho_s. rewrite -chain_OpSemN_n. 
    by apply chain_limit_ub.
Qed.
Arguments OpSem_ub {qs} n P rho_s.

Lemma OpSem_lub : forall {qs : QvarScope} (P : prog qs) rho_s rho_ub, 
    (forall n, OpSemN <{P, rho_s}> n ⊑ rho_ub) -> ⟦ P ⟧ (rho_s) ⊑ rho_ub.
Proof.
    rewrite /OpSem => qs P rho_s rho_ub H. apply chain_limit_lub. by apply H.
Qed.

Lemma OpSem_lubP : forall {qs : QvarScope} (P : prog qs) rho_s rho_ub, 
    (forall n, OpSemN <{P, rho_s}> n ⊑ rho_ub) <-> ⟦ P ⟧ (rho_s) ⊑ rho_ub.
Proof. split. by apply OpSem_lub.
    move => HP n. transitivity (⟦ P ⟧ (rho_s)) => //. 
    by apply OpSem_ub.
Qed.


(** Properties of Operationl Semantics *)

Lemma OpSem_skip {qs : QvarScope} (rho_s : PDenSet qs):
    ⟦ Skip ⟧ (rho_s) = rho_s.
Proof.
    apply PDenSetOrder_asymm.
    apply OpSem_lub. case. by apply PDenSet_uni_least.
    move => n //=. by reflexivity.
    transitivity (OpSemN <{ Skip, rho_s }> 1). by reflexivity.
    by apply OpSem_ub.
Qed.

Lemma OpSem_abort {qs : QvarScope} (rho_s : PDenSet qs):
    ⟦ Abort ⟧ (rho_s) = PDenSet_uni.
Proof.
    apply PDenSetOrder_asymm.
    apply OpSem_lub. case. by apply PDenSet_uni_least.
    move => n //=. by reflexivity.
    transitivity (OpSemN <{ Abort, rho_s }> 1). by reflexivity.
    by apply OpSem_ub.
Qed.

Lemma OpSem_init {qs : QvarScope} qv (rho_s : PDenSet qs):
    ⟦ qv <- 0 ⟧ (rho_s) = InitStt qv rho_s.
Proof.
    apply PDenSetOrder_asymm.
    apply OpSem_lub. case. by apply PDenSet_uni_least.
    move => n //=. by reflexivity.
    transitivity (OpSemN <{ qv <- 0, rho_s }> 1). by reflexivity.
    by apply OpSem_ub.
Qed.

Lemma OpSem_unitary {qs : QvarScope} qv U (rho_s : PDenSet qs):
    ⟦ qv *= U ⟧ (rho_s) = Uapply U rho_s.
Proof.
    apply PDenSetOrder_asymm.
    apply OpSem_lub. case. by apply PDenSet_uni_least.
    move => n //=. by reflexivity.
    transitivity (OpSemN <{ qv *= U, rho_s }> 1). by reflexivity.
    by apply OpSem_ub.
Qed.

(* chain_add *)
Definition chain_add_obj (H : Hspace) (ch_obj1 ch_obj2 : nat -> PDenSet H) :=
    fun n => ch_obj1 n + ch_obj2 n.
Lemma chain_add_obj_prop (H : Hspace) (ch1 ch2 : chain H) :
    let ch := chain_add_obj (chain_obj ch1) (chain_obj ch2) in 
        forall n, ch n ⊑ ch n.+1.
Proof. move => ch n. rewrite /ch /chain_add_obj. apply PDenSetOrder_add_split.
    by apply ch1. by apply ch2.
Qed.

(** Add chain is needed for proving if statement *)
Definition chain_add H (ch1 ch2 : chain H) : chain H :=
    mk_chain (chain_add_obj_prop ch1 ch2).

(** We still need the assumption that addition is continuous *)
Axiom add_continuous : forall H (ch1 ch2 : chain H),
    (lim→∞(ch1)) + (lim→∞(ch2)) = lim→∞ (chain_add ch1 ch2).


(* chain_union *)
Definition chain_union_obj (H : Hspace) (ch1 ch2 : chain H) :=
    fun n => (ch1 _[n]) ∪ (ch2 _[n]).
Lemma chain_union_prop (H : Hspace) (ch1 ch2 : chain H) :
    forall n, chain_union_obj ch1 ch2 n ⊑ chain_union_obj ch1 ch2 n.+1.
Proof. move => n. rewrite /chain_union_obj. apply PDenSetOrder_union_split.
    by apply ch1. by apply ch2.
Qed.

(** Add chain is needed for proving if statement *)
Definition chain_union H (ch1 ch2 : chain H) : chain H :=
    mk_chain (chain_union_prop ch1 ch2).

(** We still need the assumption that addition is continuous *)
Axiom union_continuous : forall H (ch1 ch2 : chain H),
    (lim→∞(ch1)) ∪ (lim→∞(ch2)) = lim→∞ (chain_union ch1 ch2).


Lemma OpSem_if {qs : QvarScope} qv_m m S0 S1 (rho_s : PDenSet qs):
    ⟦ If m [[qv_m]] Then S0 Else S1 End ⟧ (rho_s) 
        = ⟦ S0 ⟧ (Mapply m rho_s true) + ⟦ S1 ⟧ (Mapply m rho_s false).
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
    rewrite ![⟦ _ ⟧ (Mapply m rho_s _)]/OpSem. rewrite add_continuous.
    apply chain_limit_lub => l. rewrite /chain_add /chain_add_obj => //=.
    rewrite -OpSemN_if. by apply OpSem_ub.
Qed.


Lemma OpSem_while {qs : QvarScope} qv_m m S0 (rho_s : PDenSet qs):
    ⟦ While m [[qv_m]] Do S0 End ⟧ (rho_s) 
        = ⟦ S0 ;; While m [[qv_m]] Do S0 End ⟧ (Mapply m rho_s true) 
            + Mapply m rho_s false.
Proof.
    apply PDenSetOrder_asymm.

    apply OpSem_lub. case. by apply PDenSet_uni_least.
    move => n //=. apply PDenSetOrder_add_split. 
    by apply OpSem_ub. by reflexivity.


    rewrite [⟦ _ ⟧ (Mapply m rho_s _)]/OpSem.

    (* We need to transform the [Mapply m rho_s false] term into a singleton
        chain. *)
    rewrite -(singleton_chain_limit (Mapply m rho_s false)).
    rewrite add_continuous.
    apply chain_limit_lub => l. rewrite /chain_add /chain_add_obj => //=.
    rewrite -OpSemN_while. by apply OpSem_ub.
Qed.

(* The chain of InitStt ch *)
Definition InitStt_chain_obj {qs : QvarScope} (qv : qs) (ch : chain qs) :=
    fun i => InitStt qv (ch _[i]).
Lemma InitStt_chain_prop {qs : QvarScope} (qv : qs) (ch : chain qs)
    : forall i, InitStt_chain_obj qv ch i ⊑ InitStt_chain_obj qv ch i.+1.
Proof.
    rewrite /InitStt_chain_obj => i. apply PDenSetOrder_Init. by apply ch.
Qed.

Definition InitStt_chain {qs : QvarScope} (qv : qs) (ch : chain qs) :=
    mk_chain (InitStt_chain_prop qv ch).

(** We still need the assumption that addition is continuous *)
Axiom init_continuous : forall {qs : QvarScope} (qv : qs) (ch : chain qs),
    InitStt qv (lim→∞ (ch)) = lim→∞ (InitStt_chain qv ch).

(* The chain of Uapply U ch *)
Definition Uapply_chain_obj 
    {qs : QvarScope} (qv : qs) (U : UnitaryOpt qv) (ch : chain qs) :=
    fun i => Uapply U (ch _[i]).
Lemma Uapply_chain_prop 
    {qs : QvarScope} (qv : qs) (U : UnitaryOpt qv) (ch : chain qs)
    : forall i, Uapply_chain_obj U ch i ⊑ Uapply_chain_obj U ch i.+1.
Proof.
    rewrite /Uapply_chain_obj => i. apply PDenSetOrder_U. by apply ch.
Qed.

Definition Uapply_chain 
    {qs : QvarScope} (qv : qs) (U : UnitaryOpt qv) (ch : chain qs) :=
    mk_chain (Uapply_chain_prop U ch).

(** We still need the assumption that addition is continuous *)
Axiom unitary_continuous : 
    forall {qs : QvarScope} (qv : qs) (U : UnitaryOpt qv) (ch : chain qs),
    Uapply U (lim→∞ (ch)) = lim→∞ (Uapply_chain U ch).


(* The chain of Mapply M ch result *)
Definition Mapply_chain_obj 
    {qs : QvarScope} (qv : qs) (M : MeaOpt qv) (ch : chain qs) (r : bool) :=
    fun i => Mapply M (ch _[i]) r.
Lemma Mapply_chain_prop 
    {qs : QvarScope} (qv : qs) (M : MeaOpt qv) (ch : chain qs) (r : bool)
    : forall i, Mapply_chain_obj M ch r i ⊑ Mapply_chain_obj M ch r i.+1.
Proof.
    rewrite /Mapply_chain_obj => i. apply PDenSetOrder_M. by apply ch.
Qed.

Definition Mapply_chain 
    {qs : QvarScope} (qv : qs) (M : MeaOpt qv) (ch : chain qs) (r : bool) :=
    mk_chain (Mapply_chain_prop M ch r).

(** We still need the assumption that addition is continuous *)
Axiom mea_continuous : forall {qs : QvarScope} 
    (qv : qs) (M : MeaOpt qv) (ch : chain qs) (r : bool),
    Mapply M (lim→∞ (ch)) r = lim→∞ (Mapply_chain M ch r).


(* The chain of OpSemN ch (different from chain_OpSemN) *)
Definition OpSemN_chain_obj {qs : QvarScope} (S : prog qs) (ch : chain qs) n :=
    fun i => OpSemN <{S, ch _[i]}> n.

Lemma OpSemN_chain_prop {qs : QvarScope} (S : prog qs) (ch : chain qs) n
    : forall i, OpSemN_chain_obj S ch n i ⊑ OpSemN_chain_obj S ch n i.+1.
Proof. 
    rewrite /OpSemN_chain_obj => i. apply PDenSetOrder_OpSemN.
    by apply ch.
Qed.

Definition OpSemN_chain {qs : QvarScope} (S : prog qs) (ch : chain qs) n :=
    mk_chain (OpSemN_chain_prop S ch n).



Theorem OpSemN_continuous (qs : QvarScope) (S : prog qs) (ch : chain qs) n:
        OpSemN <{S, lim→∞ (ch)}> n = lim→∞ (OpSemN_chain S ch n).
Proof.
    elim: n S ch.
    (* induction basis *)
    move => S ch //=. apply PDenSetOrder_asymm.
    by apply PDenSet_uni_least.
    apply chain_limit_lub. rewrite /OpSemN_chain /OpSemN_chain_obj //=. by reflexivity.

    (* induction step, case on program [S] *)
    move => n IHn. case.
    (* skip *)
    move => ch.
    rewrite /OpSemN_chain /OpSemN_chain_obj => //=. f_equal. 
    by apply /chain_eqP.
    (* abort *) 
    move => ch //=. apply PDenSetOrder_asymm. 
    by apply PDenSet_uni_least.
    apply chain_limit_lub. rewrite /OpSemN_chain /OpSemN_chain_obj //=. 
    by reflexivity.
    (* init *)
    move => ch qv //=. rewrite init_continuous. f_equal. 
    apply /chain_eqP => //.
    (* unitary *)
    move => ch qv U //=. rewrite unitary_continuous. f_equal. 
    apply /chain_eqP => //.
    (* if *)
    move => qv_m m S0 S1 ch. rewrite OpSemN_if.
    rewrite !mea_continuous !IHn add_continuous. f_equal. apply /chain_eqP => //.
    (* While *)
    move => qv_m m S0 ch. rewrite OpSemN_while.
    rewrite !mea_continuous IHn add_continuous. f_equal. apply /chain_eqP => //.
    (* Seq *)
    move => S1 S2 ch. rewrite OpSemN_seq.
    rewrite !IHn. f_equal. apply /chain_eqP => //.
    (* atom *)
    move => S0 ch. rewrite OpSemN_atom.
    rewrite IHn. f_equal. apply /chain_eqP => //.
    (* parallel *)
    move => S1 S2 ch. rewrite OpSemN_parallel.
    rewrite !IHn union_continuous. f_equal. apply /chain_eqP => //.
Qed.



Lemma OpSem_seq {qs : QvarScope} S1 S2 (rho_s : PDenSet qs):
    ⟦ S1 ;; S2 ⟧ (rho_s) =  ⟦ S2 ⟧ ( ⟦ S1 ⟧ (rho_s) ).
Proof.
    apply PDenSetOrder_asymm.

    apply OpSem_lub. case. by apply PDenSet_uni_least.
    move => n //=. transitivity (OpSemN <{ S2, ⟦ S1 ⟧ (rho_s) }> n).
    apply PDenSetOrder_OpSemN. by apply OpSem_ub.
    by apply OpSem_ub.

    apply OpSem_lub => n.
    rewrite [⟦ S1 ⟧(_)]/OpSem. rewrite OpSemN_continuous.
    apply chain_limit_lub => i.
    rewrite /OpSemN_chain /OpSemN_chain_obj //=.
    
    (* using [max i n] steps in [S1 ;; S2] *)
    move : (OpSem_ub (max i n).+1 (S1;;S2) rho_s) => //=.
    case E : (i <= n). 
    { move /leP : E => E. rewrite (max_r _ _ E) => H.
    transitivity (OpSemN <{ S2, OpSemN <{ S1, rho_s }> n }> n).
    apply PDenSetOrder_OpSemN.
    by apply /OpSemN_inc /leP.
    by apply H. }
    move /leP /Nat.lt_nge /Nat.lt_le_incl: E => E. rewrite (max_l _ _ E) => H.
    transitivity (OpSemN <{ S2, OpSemN <{ S1, rho_s }> i }> i).
    by apply /OpSemN_inc /leP.
    by apply H.
Qed.    

Lemma OpSem_atom {qs : QvarScope} P (rho_s : PDenSet qs):
    ⟦ <<P>> ⟧ (rho_s) =  ⟦ P ⟧ (rho_s).
Proof.

    apply PDenSetOrder_asymm.

    apply OpSem_lub. case => //=. by apply PDenSet_uni_least.
    move => n. by apply (OpSem_ub n).

    apply OpSem_lub => n. rewrite -OpSemN_atom. by apply OpSem_ub.
Qed.

Lemma OpSem_para {qs : QvarScope} S1 S2 (rho_s : PDenSet qs):
    ⟦ [S1 // S2] ⟧ (rho_s) = 
        ⟦ Step S1 S2 true ⟧ (rho_s) ∪ ⟦ Step S1 S2 false ⟧ (rho_s).
Proof.
    apply PDenSetOrder_asymm.

    apply OpSem_lub. case. by apply PDenSet_uni_least.
    move => n. rewrite OpSemN_parallel. 
    apply PDenSetOrder_union_split; by apply OpSem_ub.

    rewrite ![⟦ Step _ _ _ ⟧(rho_s)]/OpSem. 
    rewrite union_continuous. apply chain_limit_lub => l.
    rewrite /chain_union /chain_union_obj /chain_OpSemN /chain_obj => //.
    rewrite -OpSemN_parallel. by apply OpSem_ub.
Qed.


    




    