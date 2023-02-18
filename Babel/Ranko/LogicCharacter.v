(** LogicCharacter.v *)

From mathcomp Require Import all_ssreflect.
Require Import Coq.Unicode.Utf8_core.

From Babel.Ranko Require Import CentralCharacter.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** progress guaranteed *)
Ltac logic_branch
        top_step
        split_mode      
        general_apply_depth
        eexists_mode
        :=

    match goal with
    | H : true = true |- _ => clear H
    | H : false = false |- _ => clear H
    | H : true = _ |- _ => symmetry in H
    | H : false = true |- _ => by inversion H
    | H : false = _ |- _ => symmetry in H

    | |- true = true => by reflexivity
    | |- false = false => by reflexivity
    | |- true = _ => symmetry
    | |- false = true => fail
    | |- false = _ => symmetry
    
    | _ => progress rewrite /is_true
    end.

Ltac logic_step 
        top_step
        split_mode      
        general_apply_depth
        eexists_mode
        :=
    match goal with
    | _ => logic_branch top_step split_mode general_apply_depth eexists_mode
    | _ => central_step top_step split_mode general_apply_depth eexists_mode
    end.
    
Ltac logic_step_sealed 
        split_mode      
        general_apply_depth
        eexists_mode
        :=
    idtac; let rec top := logic_step_sealed in 
        logic_step top split_mode general_apply_depth eexists_mode.

Ltac logic_level 
        split_mode      
        general_apply_depth
        eexists_mode 
        :=
    repeat logic_step_sealed split_mode general_apply_depth eexists_mode.
