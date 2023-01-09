From Ranko Require Import TerminalDogma.premises.
From Coq Require Import Classical.


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
Fixpoint OpSem {qs : QvarScope} (c : cfg qs) (n : nat) : PDenSet qs :=
    match c with
    | <{ ↓ , rho_s }> => rho_s
    | <{ P , rho_s }> => 
        match n with
        | O => PDenSet_uni
        | S n' => 
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
                (OpSem <{ P0, Mapply m rho_s true }> n')
                + (OpSem <{ P1, Mapply m rho_s false }> n')
            | While m [[ qv_m ]] Do P0 End  =>
                (OpSem <{ P0;; While m [[ qv_m ]] Do P0 End 
                        , Mapply m rho_s true }> n')
                + Mapply m rho_s false
            | S1 ;; S2 => 
                OpSem <{ S2 , OpSem <{S1, rho_s}> n' }> n'
            | << P >> => 
                OpSem <{ P, rho_s }> n'
            | [ S1 // S2 ] => 
                (** Note that here we give a different interpretation of 
                    nested parallel composition *)
                (OpSem <{ Step S1 S2 true , rho_s }> n')
                ∪ (OpSem <{ Step S1 S2 false , rho_s }> n')
            end
        end
    end.


Lemma OpSem_seq_ex {qs : QvarScope} S0 S1 :
        forall rho_s n, exists a b, OpSem <{ S0 ;; S1, rho_s }> n = 
                @OpSem qs <{ S1 , OpSem <{ S0, rho_s}> a }> b.
Proof.
    (** This property does not hold in the finite situation, because S0 can
        have branches of different lengths. *)
Abort.
    


Lemma OpSem_if {qs : QvarScope} qv_m m S0 S1: 
        forall rho_s n, OpSem <{ If m [[ qv_m ]] Then S0 Else S1 End , rho_s }> n.+1
                    = OpSem <{ S0, Mapply m rho_s true }> n
                        + @OpSem qs <{ S1, Mapply m rho_s false }> n.
Proof. move => rho_s. by case. Qed.

Lemma OpSem_while {qs : QvarScope} qv_m m S0:
        forall rho_s n, OpSem <{ While m [[ qv_m ]] Do S0 End , rho_s }> n.+1
                    = OpSem <{ S0;; While m [[ qv_m ]] Do S0 End , 
                            Mapply m rho_s true }> n
                        + (@Mapply qs qv_m m rho_s false).
Proof. move => rho_s. by case. Qed.

(** Arguments about order *)
Axiom PDenSetOrder : forall {H : Hspace}, PDenSet H -> PDenSet H -> Prop.
Notation " A '⊑' B " := (PDenSetOrder A B) (at level 60).

Locate reflexive.

Axiom PDenSetOrder_refl : 
    forall H, Relation_Definitions.reflexive _ (@PDenSetOrder H).
Axiom PDenSetOrder_trans : 
    forall H, Relation_Definitions.transitive _ (@PDenSetOrder H).

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

Check InitStt.

Axiom PDenSetOrder_Init : 
    forall {qs : QvarScope} r1 r2 (qv : qs), r1 ⊑ r2 -> InitStt qv r1 ⊑ InitStt qv r2.
Axiom PDenSetOrder_U : 
    forall {qs : QvarScope} r1 r2 (qv : qs) (U : UnitaryOpt qv),
        r1 ⊑ r2 -> Uapply U r1 ⊑ Uapply U r2.
Axiom PDenSetOrder_M : 
    forall {qs : QvarScope} r1 r2 (qv_m : qs) (m : MeaOpt qv_m) (result : bool),
        r1 ⊑ r2 -> Mapply m r1 result ⊑ Mapply m r2 result.

Lemma PDenSetOrder_add_split {H : Hspace} :
    forall {rho_s1 rho_s2 rho_s1' rho_s2': PDenSet H}, 
        rho_s1 ⊑ rho_s1' -> rho_s2 ⊑ rho_s2' 
            -> rho_s1 + rho_s2 ⊑ rho_s1' + rho_s2'.
Proof. move => a b c d Hac Hbd. rewrite Hac Hbd. by reflexivity. Qed.

(* 用这个引理证递增的结论 *)
Lemma PDenSetOrder_OpSem_strong {qs : QvarScope} :
    forall (S0 : prog qs) (r1 r2 : PDenSet qs) n n0, 
        n0 <= n -> r1 ⊑ r2 -> OpSem <{ S0 , r1 }> n0 ⊑ OpSem <{ S0 , r2 }> n0.
Proof.

    move => S0 r1 r2 n n0 Hn0 Hr1r2.
    case : n0 Hn0. move =>_. by apply PDenSet_uni_least.
    (*
    elim : S0 r1 r2 Hr1r2.
    (* skip *)
    by move => r1 r2 Hr1r2 n0 Hn0 => /=.
    (* abort *)
    move => r1 r2 Hr1r2 n0 Hn0 => /=. by reflexivity.
    (* init *)
    move => qv r1 r2 Hr1r2 n0 => //=. by apply PDenSetOrder_Init.
    (* unitary *)
    move => qv r1 r2 Hr1r2 U n => //=. by apply PDenSetOrder_U.
    (* sequential composition first *)
    3: apply SeqLemma.
    (* if *)
    move => qv_m m S0 IHS0 S1 IHS1 r1 r2 Hr1r2 n //=.
    case: n. by reflexivity.
    move => n. apply PDenSetOrder_add_split. 
    apply IHS0. by apply PDenSetOrder_M.
    apply IHS1. by apply PDenSetOrder_M.
    (* while *)
    move => qv_m m S0 IHS0 r1 r2 Hr1r2 n.
    elim: n r1 r2 Hr1r2. move => r1 r2 Hr1r2 //=. by rewrite !PDenSet_Add_uni_l; reflexivity.
    move => n IHn r1 r2 Hr1r2. apply PDenSetOrder_add_split; last first. by apply PDenSetOrder_M.
    apply SeqLemma. apply IHS0.
    *)
Admitted.

Lemma PDenSetOrder_OpSem {qs : QvarScope} :
    forall (S0 : prog qs) (r1 r2 : PDenSet qs) n, 
        r1 ⊑ r2 -> OpSem <{ S0 , r1 }> n ⊑ OpSem <{ S0 , r2 }> n.
Proof.
    move => S0 r1 r2 n.
    by apply (@PDenSetOrder_OpSem_strong qs S0 r1 r2 n n).
Qed.

Lemma OpSem_inc {qs : QvarScope} : 
    forall (c : cfg qs) n, OpSem c n ⊑ OpSem c n.+1.
Proof.
    (** process terminated configurations first *)
    move => []; last first.
    move => rho_s. case => //=; by reflexivity.

    (* induction on program *)
    elim.

    (* skip, abort *)
    1, 2 : by move => rho_s /=; case => //=; [ apply PDenSet_uni_least | reflexivity].
    (* init *)
    move => qv rho_s /=. by case => //=; [ apply PDenSet_uni_least | reflexivity].
    (* unitary *)
    move => qv U rho_s /=. by case => //=; [ apply PDenSet_uni_least | reflexivity].

    (* seq first *)
    3: { move => S1 IHS1 S2 IHS2 rho_s n.
    case: n. by reflexivity.
    move => n. elim S1. 


    }

    (* if *)
    move => qv_m m S0 IHS0 S1 IHS1 rho_s. case.
    by apply PDenSet_uni_least.
    move => n. rewrite !OpSem_if. 
    apply PDenSetOrder_add_split. by apply IHS0. by apply IHS1.

    (* while *)
    move => qv_m m S0 IHS0 rho_s n. move : rho_s. elim: n.
    by move => rho_s; apply PDenSet_uni_least.
    move => n IH rho_s. rewrite !OpSem_while.
    apply PDenSetOrder_add_split; last first. by reflexivity.
    { case n. by reflexivity. 
         } 

    

Lemma composition {qs : QvarScope} :
    forall (rho_s : PDenSet qs) (S1 S2 : prog qs),
        OpSem 