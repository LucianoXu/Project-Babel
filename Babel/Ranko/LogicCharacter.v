(** LogicCharacter.v *)

From mathcomp Require Import all_ssreflect.
Require Import Coq.Unicode.Utf8_core.

From Babel.Ranko Require Import CentralCharacter.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



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
