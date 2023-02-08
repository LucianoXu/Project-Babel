(** CentralTactic.v *)

(** term explanation:
    safe : The tactic will not turn a provable goal into an unprovable one.
    terminating: if all components are terminating, the tactic will terminate
        in all situations. 
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

    (** break the implication precondition *)
    | |- False -> _ => move => []
    | |- (_ \/ _) -> _ => move => [|]
    | |- (exists i, _) -> _ => move => []
    | |- (_ /\ _) -> _ => move => []
    end.

Ltac premise_break := repeat premise_break_step.


Ltac terminate := 
    by multimatch goal with
    | |- True => by []
    | H: False |- _ => destruct H
    | H: ?A |- ?A => apply H
    | H1: ?A, H2: ~?A |- _ => destruct (H2 H1)
    end.

(** This is a traversal and iterative proof search framework.
    It takes in a parameter [tac], which is a tactic. 
    
    It will try to terminate the subgoals with [tac] after selecting a branch.
    (For example, for a [?A \/ ?B] goal.) If the current branch fails, it will
    try other branches. If all branches does not work, it will stop before the 
    branch selecting stage.

    safe tactic *)

Ltac search_framework tac :=
    repeat multimatch goal with
    (** process the premises *)
    | |- _ => premise_break_step

    (** for equality, try to use it in two ways 
        This is a dangerous technique, and we don't use for now. *)
    (*
    | |- _ = _ -> _ => 
        let H := fresh "Heq" in 
            (move => H; try rewrite H; by (search_framework tac))
            || (move => H; try rewrite -H; by (search_framework tac))
    *)

    (** path selecting *)
    | |- (_ /\ _) => split
    | |- (_ \/ _) => 
        (left; by (search_framework tac)) || (right; by (search_framework tac))

    (** try to finish the goal after path searching*)
    | |- _ => terminate
    | |- _ => tac
    end.

(** for debugging purpose *)
Ltac search_frameworkN tac :=
    do 100 multimatch goal with
    (** process the premises *)
    | |- _ => premise_break_step
    
    (** for equality, try to use it in two ways 
        This is a dangerous technique, and we don't use for now. *)
    (*
    | |- _ = _ -> _ => 
        let H := fresh "Heq" in 
            (move => H; try rewrite H; by (search_framework tac))
            || (move => H; try rewrite -H; by (search_framework tac))
    *)

    (** path selecting *)
    | |- (_ /\ _) => split
    | |- (_ \/ _) => 
        (left; by (search_framework tac)) || (right; by (search_framework tac))

    (** try to finish the goal after path searching*)
    | |- _ => terminate
    | |- _ => tac
    end.
