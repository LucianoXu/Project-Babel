(** LogicCharacter.v *)

From mathcomp Require Import all_ssreflect.
Require Import Coq.Unicode.Utf8_core.

From Babel Require Import BoolBasic.

From Babel.Ranko Require Import CentralCharacter.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Ltac prop_2_bool_ssr_branch :=
    match goal with
    | _ => rewrite not_true_iff_false
    | _ => rewrite not_false_iff_true
    | _ => rewrite -implb_true_iff
    | _ => rewrite -andb_true_iff
    | _ => rewrite -andb_false_iff
    | _ => rewrite -implb_andb_distrib_r
    end.

Ltac prop_2_bool_ssr := 
    repeat prop_2_bool_ssr_branch.

Ltac bool_2_prop_ssr_branch :=
    match goal with
    | _ => rewrite not_true_iff_false
    | _ => rewrite not_false_iff_true
    | _ => rewrite implb_true_iff
    | _ => rewrite andb_true_iff
    | _ => rewrite andb_false_iff
    | _ => rewrite implb_andb_distrib_r
    end.
Ltac bool_2_prop_ssr := 
    repeat bool_2_prop_ssr_branch.
    

Ltac bool_const_switch_branch :=
    match goal with
    | |- true = true -> _ => move => _
    | |- false = false -> _ => move => _
    | |- true = _ -> _ => let temp := fresh "Htemp" in 
            intros temp; symmetry in temp; move: temp
    | |- false = true -> _ => let temp := fresh "Htemp" in 
            intros temp; by inversion temp
    | |- false = _ -> _ => let temp := fresh "Htemp" in 
            intros temp; symmetry in temp; move: temp

    | |- true = true => by reflexivity
    | |- false = false => by reflexivity
    | |- true = _ => symmetry
    | |- false = true => rewrite true_eq_false_False
    | |- false = _ => symmetry
    end.

(** progress guaranteed *)
Ltac logic_branch
        top_step
        split_mode      
        general_apply_depth
        eexists_mode
        :=
    match goal with
    | _ => bool_2_prop_ssr_branch
    | _ => progress rewrite /is_true
    | _ => bool_const_switch_branch
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
