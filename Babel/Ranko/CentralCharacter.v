(** CentralTactic.v *)

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

(** Push all premise to the goal 
    WARNING: this tactic will loop forever in some situations in sections, when
    then premise cannot be cleared after generalization. *)
Ltac all_move_down :=
    repeat match goal with 
    | H : _ |- _ => generalize dependent H 
    end.



(*################################################################################*)

Create HintDb magic_book.
#[export] Hint Constants Transparent : magic_book.
#[export] Hint Variables Transparent : magic_book.

(** This should be the last resort after all attemps. *)
Ltac central_step
        top_step
        :=
    match goal with
    | _ => progress autounfold with magic_book

    | |- forall i, _ => intros ?
    
    (** try to utilize [forall] premises 
        Note that this method is not complete, because we cannot control which
        term to use for instantiating [forall] 
        
        This branch is a little arbitrary indeed. *)
    | H : forall a : ?A, _, Hterm : ?A |- _ => 
        move: (H Hterm); clear H; 
        by repeat top_step


    (*| _ => progress auto with magic_book *)
    end.

Ltac central_step_sealed :=
    let rec top := central_step_sealed in central_step top.

Ltac central_level := repeat central_step_sealed.