(** CentralTactic.v *)

(** term explanation:

    safe : The tactic will not turn a provable goal into an unprovable one.

    terminating: if all components are terminating, the tactic will terminate
        in all situations. 

    complete branch: in a [match] ltac expression, branches like
    [ | |- ... ltac_expr; by ... ]
    are called complete branches. That is, if this branch is selected, then it
    must solves the goal. In other words, complete branch cannot make partial
    progress on the goal. Put complete branches before incomplete branches in
    [match] expressions will make the tactic try its best to search for a
    better proof. While on the hand, put incomplete branches in the front will
    make the tactic accept quick but partial progress.
*)

From mathcomp Require Import all_ssreflect.
Require Import Coq.Unicode.Utf8_core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** This tactic will break the premise into atomic small pieces.
    safe tactic*)
Ltac premise_break_step := 
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
    end.

Ltac premise_break := repeat premise_break_step.


Ltac terminate := 
    by multimatch goal with
    | H: False |- _ => destruct H
    | H: ?A |- ?A => apply H
    | H1: ?A, H2: ~?A |- _ => destruct (H2 H1)
    | _ => by []
    end.


(** Succeeds if not both sides of the [and] goal have existential variables. 
    (functional) *)
Ltac check_and_not_both_have_evar :=
    assert_fails (split; instantiate (1 := _)).

(** Succeeds if the premise [H] is the only term of that type in the premises. *)
Ltac is_only H :=
    let T := type of H in 
    (assert_fails (generalize dependent H; 
        match goal with | H' : T |- _ => idtac end)).
    
    
(** This is a traversal and iterative proof search framework.
    It takes in a parameter [tac], which is a tactic. 
    
    It will try to terminate the subgoals with [tac] after selecting a branch.
    (For example, for a [?A \/ ?B] goal.) If the current branch fails, it will
    try other branches. If all branches does not work, it will stop before the 
    branch selecting stage.

    safe tactic *)

Ltac search_framework tac :=
    repeat multimatch goal with
    (** for equality, try to use it in two ways 
        This is a dangerous technique, and we don't use for now. *)
    (*
    | |- _ = _ -> _ => 
        let H := fresh "Heq" in 
            (move => H; try rewrite H; by (search_framework tac))
            || (move => H; try rewrite -H; by (search_framework tac))
    *)

    (** path selecting *)

    (** [and] goal*)
    | |- (_ /\ _) => 
    (** If the [and] goal has at least one side without any exsitential 
        variable, we can directly split it. *)
                    (check_and_not_both_have_evar; split)
    (** If the [and] goal has exsitential variables, the tactic must solve the
        goal after [split], otherwise this [split] action can be unsafe. *)
                    || (split; by search_framework tac)
                    || (split; last first; by search_framework tac)

    (** [or] goal, complete branch *)
    | |- (_ \/ _) => 
        (left; by (search_framework tac)) || (right; by (search_framework tac))

    (** Conduct the tactic of this particualr level. *)
    |  _ => tac

    | |- _ <-> _ => unfold iff

    | |- exists i, _ => eexists


    (** Try to finish equality goal with [eq_refl]. This is mainly for the
        instantiation of existential variables. This is safe since there are no
        other branches*)
    (* | |- ?A = ?B =>
        (is_evar A + is_evar B);
        apply Logic.eq_refl *)

    (** try to finish the goal after path searching*)
    |  _ => terminate
    end.
