(** CentralCharacter.v *)

From mathcomp Require Import all_ssreflect.
Require Import Coq.Unicode.Utf8_core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Ltac terminate := 
    by multimatch goal with
    | H: False |- _ => destruct H
    | H: ?A |- ?A => apply H
    | H1: ?A, H2: ~?A |- _ => destruct (H2 H1)
    | _ => by []
    end.


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

(** Push all premise to the goal *)
Ltac all_move_down :=
    repeat match goal with 
    | H : _ |- _ => generalize dependent H 
    end.