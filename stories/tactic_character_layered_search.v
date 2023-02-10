(** tactic_character_layered_search.v

    This document describes the methodology of constructing tactics using 
    'layered search framework'. *)

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

(** The basic idea of layered search tactic is base on this fact: theories
    in Coq can be devided into different levels, according to their dependency.
    And each proof goal falls in some theory level. 
    An algorithm to proof this goal, can be like this:

    1.) Make some progress on goal using techniques in the current level.
    2.) If 1 fails, break the goal into the next lower level, and enter the
        step tactic of the lower level.
    3.) Repeat the procedure iteratively.

    ( This is what 'layered' means. )
*)

(** Every particular layered search tactic is constructed inductively accroding
    to the framework described below.

    Assume we have a theory called *Alpha*. We now demonstrate the framework by
    defining the corresponding layered search tactic [Alpha_level].
*)

(** Tip: to better analysis the performance of different branches, we can wrap
    each branch into an individual tactic and invoke it in the step tactic.
    
    Use 
        [Set Ltac Profiling.]
    and 
        [Show Ltac Profile.]
    to see the execution state.

    The branch tactic should be in the following form.
*)

Ltac alpha1_branch 
        (** (Optional arg) 
        top_step Type: [ltac]. The step tactic of top level. *)
        :=
    (** the branch tactic *)
    (** (Optional) End with [by top_step]. *)
    idtac.


(** First we need a step tactic called [Alpha_step], corresponding to the
    one-step progress in level Alpha. *)

Ltac Alpha_step
        top_step
            (** Type: [ltac]. The step tactic of top level. *)

        (** args : some extra arguments *)
        :=
    multimatch goal with

    | _ => idtac
    (** some proof logic of this level 
        Note: if one branch is unsafe, we recommand to postfix the branch with
        [ by repeat top_step ]
        to make the branch safe. *)

    (** (Optional) If we want the tactic to rewort to tactics of lower levels,
        put them here in the following form:

    | _ => Some_step top_step (* argvs*)
        
        ( In some situations we will want such lower steps placed in the middle
        of the current step.)
        *)
    end.


(** Then we wrap this step tactic to get the tactic for this level. *)

Ltac Alpha_level := repeat ltac:(Alpha_step idtac (* argvs *)).


(** Tactic nesting: Assume now we have another theory Beta which is dependent
    on Alpha. We build the layered search tactic [Beta_level] base on the
    existing tactic. *)

Ltac Beta_step
        top_step
        (** args : some extra arguments *)
        :=

    multimatch goal with

    (** some proof logic of this level *)

    (** at last, resort to the lower level step tactic [Alpha_step] 
        If there are multiple base theories, just put them here. *)
    | _ => Alpha_step top_step (* argvs*)
    end.

Ltac Beta_level := repeat ltac:(Beta_step idtac (* argvs *)).





