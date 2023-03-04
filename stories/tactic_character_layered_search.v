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

    progress guaranteed: this tactic will success only if it makes some
    progress.
*)

(** The basic idea of layered search tactic is base on this fact: theories
    in Coq can be devided into different levels, according to their dependency.
    And each proof goal falls in some theory level. 
    An algorithm to proof this goal, can be like this:

    0.) Push all premises to the goal.

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

    Note: sometimes this method is not equivalent to the original one.
*)

Ltac alpha1_branch 
        (** (Optional arg) 
        top_step Type: [ltac]. The step tactic of top level. 
                        (without parameters) *)
        :=
    (** the branch tactic *)
    (** (Optional) End with [by top_step (* argvs *)]. *)
    idtac.


(** First we need a step tactic called [Alpha_step], corresponding to the
    one-step progress in level Alpha. 
        
    Note that the step tactics should be progress guaranteed. *)

Ltac Alpha_step
        top_step
            (** Type: [ltac]. The step tactic of top level. 
                        (without parameters) *)

        (** args : some extra arguments 
                Note : we can use [Variant] to define enumerating arguments. *)
        :=
    match goal with

    | _ => idtac
    (** some proof logic of this level 
        Note: if one branch is unsafe, we recommand to postfix the branch with
        [ by repeat top_step (* argvs *)]
        to make the branch safe. *)

    (** (Optional) If we want the tactic to rewort to tactics of lower levels,
        put them here in the following form:

    | _ => Some_step top_step (* argvs *)
        
        ( In some situations we will want such lower steps placed in the middle
        of the current step.)
        *)
    end.

(** Note: For some complex layers, which are dependent on other layers, we use
    [Alpha_step_PRE] and [Alpha_step_POST] to make this layer easy to be
    reused. *)
    
Ltac Alpha_step_PRE :=
    match goal with
    | _ => idtac
    end.

Ltac Alpha_step_POST :=
    match goal with
    | _ => idtac
    end.

Ltac Alpha_step' :=
    Alpha_step_PRE
    || idtac (** This tactic can be replaced with other step tactics. *)
    || Alpha_step_POST.



(** Then we wrap this step tactic to get the tactic for this level. *)

Ltac Alpha_step_sealed (* args *) := 
    idtac; let rec top_step (* args *) := Alpha_step_sealed in 
        Alpha_step top_step (* arvgs *).


Ltac Alpha_level := 
    repeat Alpha_step_sealed (* argvs *).

(** The "level" tactic can be customed to fit different needs.
    Level tactics will merely operate on existsing premises. *)


(** Tactic nesting: Assume now we have another theory Beta which is dependent
    on Alpha. We build the layered search tactic [Beta_level] base on the
    existing tactic. *)

Ltac Beta_step
        top_step
        (** args : some extra arguments *)
        :=

    match goal with

    (** some proof logic of this level *)

    (** at last, resort to the lower level step tactic [Alpha_step] 
        If there are multiple base theories, just put them here. *)
    | _ => Alpha_step top_step (* argvs*)
    end.

Ltac Beta_step_sealed (* args *) := 
    idtac; let rec top_step := Beta_step_sealed (* args *) in 
        Beta_step top_step (* arvgs *).

Ltac Beta_level := repeat Beta_step_sealed.


(** About axiom specified layers 
    Use hook technique to avoid introducing axioms into the system 
    unintentionally.
*)


(** WORD OF WISDOM 

    - Tactics should avoid operating the premises. Instead, operator the
        pre-condition before moving it up. Also, avoid adding new intermediate
        conclusions to the premises.

    - Avoid the use of [simpl], which may bring unexpected unfolding. Use
        [move => //=.] instead.

    - The most rare cases should be put in the latter part.

    - Use Coq [nat] and [match] in Ltac to do number calculating.

*)




