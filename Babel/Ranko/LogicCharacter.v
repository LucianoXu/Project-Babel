(** LogicCharacter.v *)

From mathcomp Require Import all_ssreflect.
Require Import Coq.Unicode.Utf8_core.

From Babel.Ranko Require Import CentralCharacter.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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


(** Succeeds if not both sides of the [and] goal have existential variables. 
    (functional) *)
Ltac check_and_not_both_have_evar :=
    assert_fails (split; instantiate (1 := _)).

    
(** progress guaranteed *)
Ltac logic_step
        top_step        (* [ltac], the level-specific tactic *)
        split_mode      
        :=

    match goal with
    | _ => central_step top_step
    end.

Ltac logic_step_sealed split_mode :=
    idtac; let rec top := logic_step_sealed in 
        logic_step top split_mode.

Ltac logic_level split_mode :=
    repeat logic_step_sealed split_mode.
