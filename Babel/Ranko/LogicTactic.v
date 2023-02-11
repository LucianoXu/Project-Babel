(** LogicTactic.v *)

From mathcomp Require Import all_ssreflect.
Require Import Coq.Unicode.Utf8_core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** This tactic will break the premise into atomic small pieces.
    safe tactic, progress guaranteed tactic *)
Ltac premise_break_branch := 
    match goal with
    (** break the premise *)
    | H: _ /\ _ |- _ => destruct H as [? ?]
    | H: _ \/ _ |- _ => destruct H as [?|?]
    | H: exists _, _ |- _ => destruct H as [? ?]
    | H: True |- _ => clear H

    (** break the implication precondition *)
    | |- False -> _ => move => []
    | |- (_ \/ _) -> _ => move => [|]
    | |- (exists i, _) -> _ => move => []
    | |- (_ /\ _) -> _ => move => []
    | |- forall i, _ => intros ?
    end.


Ltac terminate := 
    by match goal with
    | H: False |- _ => destruct H
    | H: ?A |- ?A => apply H
    | H1: ?A, H2: ~?A |- _ => destruct (H2 H1)
    | _ => by []
    end.


(** Succeeds if not both sides of the [and] goal have existential variables. 
    (functional) *)
Ltac check_and_not_both_have_evar :=
    assert_fails (split; instantiate (1 := _)).

    
(** progress guaranteed *)
Ltac logic_step
        top_step        (* [ltac], the level-specific tactic *)
        split_mode      (* [integer] controls the behaviour of split branch
                                integer:(0) : unsafe split
                                        unsafe, but much quicker
                                integer:(1) : passive split
                                        safe but not incomplete
                                other value : aggressive split
                                        safe and complete, but may be slower
                        *)
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
    | _ => premise_break_branch
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
                        split; by repeat top_step
                    
        (** >>>>>> split_mode: aggressive split *)
                    else
    
        (** If the [and] goal has at least one side without any exsitential 
            variable, we can directly split it. *)
                        (check_and_not_both_have_evar; split)
        (** If the [and] goal has exsitential variables, the tactic must solve 
            the goal after [split], otherwise this [split] action can be unsafe. *)
                    || (split; by repeat top_step)
                    || (split; last first; by repeat top_step)
                    

    (** [or] goal, complete branch *)
    | |- (_ \/ _) =>
        (left; by repeat top_step) 
        || (right; by repeat top_step)

    | |- _ <-> _ => unfold iff

    | |- exists i, _ => eexists

    (** [firstorder] as the last resort *)
    (* | _ => progress firstorder *)

    (** try to finish the goal after path searching*)
    | _ => terminate
    end.
