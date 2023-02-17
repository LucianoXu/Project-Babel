(** CentralTactic.v 
    controls the most basic searching settings *)

From mathcomp Require Import all_ssreflect.
Require Import Coq.Unicode.Utf8_core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Display the current goal (conclusion) using [idtac]. *)
Ltac show_goal :=    
    match goal with
    | |- ?G => idtac G
    end.


(** Succeeds if the premise [H] is the only term of that type in the premises. *)
Ltac is_only H :=
    let T := type of H in 
    (assert_fails (generalize dependent H; 
        match goal with | H' : T |- _ => idtac end)).

(** Push all premise to the goal 
    WARNING: this tactic will loop forever in some situations in sections, when
    then premise cannot be cleared after generalization. *)
Ltac all_move_down :=
    repeat match goal with 
    | H : _ |- _ => generalize dependent H 
    end.



(*################################################################################*)
(** central charater *)

(** This tactic will break the premise into atomic small pieces.
    safe tactic, progress guaranteed tactic *)

Ltac precond_break_branch := 
    match goal with
    (** break the implication precondition *)
    | |- False -> _ => move => []
    | |- (_ \/ _) -> _ => move => [|]
    | |- (exists i, _) -> _ => move => []
    | |- (_ /\ _) -> _ => move => []
    | |- True -> _ => move => _
    end.


Ltac terminate := 
    by match goal with
    | H: False |- _ => destruct H
    | H: ?A |- ?A => apply H
    | H1: ?A, H2: ~?A |- _ => destruct (H2 H1)
    | _ => by []
    end.

Create HintDb magic_book.
#[export] Hint Constants Transparent : magic_book.
#[export] Hint Variables Transparent : magic_book.

    
    
(** Succeeds if not both sides of the [and] goal have existential variables. 
    (functional) *)
Ltac check_and_not_both_have_evar :=
    assert_fails (split; instantiate (1 := _)).

    
(** progress guaranteed *)
Ltac central_step
        top_step        (* [ltac], the level-specific tactic 
                                ( without parameters )*)
        split_mode      (* [integer] controls the behaviour of split branch
                                integer:(0) : unsafe split
                                        unsafe, but much quicker
                                integer:(1) : passive split
                                        safe but not incomplete
                                other value : aggressive split
                                        safe and complete, but may be slower
                        *)
        general_apply_depth     
                        (* [Coq nat] constrols the searching depth of general
                                apply branch.*)
        :=

    match goal with
    (** for equality, try to use it in two ways 
        This is a dangerous technique, and we don't use for now. *)
    (*
    | |- _ = _ -> _ => 
        let H := fresh "Heq" in 
            (move => H; try rewrite H; by (search_framework level_step))
            || (move => H; try rewrite -H; by (search_framework level_step))
    *)

    (** Note : this premise break branch cannot be repeated here. *)
    | _ => precond_break_branch
    (** path selecting *)
    (** [and] goal*)
    | |- (_ /\ _) => 
                    tryif guard split_mode = 0 
        (** >>>>>> split_mode: unsafe split *)
                    then
                        split

                    else tryif guard split_mode = 1

        (** >>>>>> split_mode: passive split*)
                    then
                        split; by repeat top_step split_mode general_apply_depth
                    
        (** >>>>>> split_mode: aggressive split *)
                    else
    
        (** If the [and] goal has at least one side without any exsitential 
            variable, we can directly split it. *)
                        (check_and_not_both_have_evar; split)
        (** If the [and] goal has exsitential variables, the tactic must solve 
            the goal after [split], otherwise this [split] action can be unsafe. *)
                    || (split; by repeat top_step split_mode general_apply_depth)
                    || (split; last first; by repeat top_step split_mode general_apply_depth)
                    
    | |- _ <-> _ => unfold iff

    (** TODO #26 *)
    | |- exists i, _ => eexists

    (** [or] goal, complete branch *)
    | |- (_ \/ _) =>
        (left; by repeat top_step split_mode general_apply_depth) 
        || (right; by repeat top_step split_mode general_apply_depth)

    (** [firstorder] as the last resort *)
    (* | _ => progress firstorder *)

    (** try to finish the goal after path searching*)
    | _ => terminate

    | _ => progress autounfold with magic_book

    | |- forall i, _ => intros ?
    
    (** general apply branch

        try to utilize [forall] premises 
        Note that this method is not complete, because we cannot control which
        term to use for instantiating [forall] 
        
        This branch is a little arbitrary indeed. *)
    | H : forall a : ?A, _, Hterm : ?A |- _ => 
        match general_apply_depth with
        | O => idtac
        | S ?n =>   move: (H Hterm); clear H; 
                    by repeat top_step split_mode n
        end


    (*| _ => progress auto with magic_book *)

    end.


Ltac central_step_sealed 
        split_mode 
        general_apply_depth
        :=
    let rec top := central_step_sealed in 
    central_step top split_mode general_apply_depth.

Ltac central_level 
        split_mode 
        general_apply_depth
        := 
    repeat central_step_sealed split_mode general_apply_depth.