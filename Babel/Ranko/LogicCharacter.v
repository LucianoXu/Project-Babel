(** LogicCharacter.v *)

From mathcomp Require Import all_ssreflect.
Require Import Coq.Unicode.Utf8_core.

From Babel Require Import BoolBasic LogicFacility.

From Babel.Ranko Require Import CentralCharacter.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Ltac ssr_simpl_branch :=
    match goal with
    | _ => rewrite not_true_iff_false
    | _ => rewrite not_false_iff_true
    | _ => rewrite negb_true_iff
    | _ => rewrite negb_false_iff
    | Ht : ?A = true, Hf : ?A = false |- _ => 
        by rewrite Ht in Hf; inversion Hf
    end.

Ltac prop_2_bool_ssr_branch :=
    match goal with
    | _ => rewrite -implb_true_iff
    | _ => rewrite -andb_true_iff
    | _ => rewrite -andb_false_iff
    | _ => rewrite -orb_true_iff
    | _ => rewrite -orb_false_iff
    | _ => rewrite -implb_andb_distrib_r
    end.

Ltac prop_2_bool_ssr := 
    repeat prop_2_bool_ssr_branch.

Ltac bool_2_prop_ssr_branch :=
    match goal with
    | |- _ ==> _ = true -> _ => rewrite implb_true_iff
    | |- _ ==> _ = true => rewrite implb_true_iff
    | _ => rewrite andb_true_iff
    | _ => rewrite andb_false_iff
    | |- _ ==> _ && _ -> _ => rewrite implb_andb_distrib_r
    | |- _ ==> _ && _ => rewrite implb_andb_distrib_r
    end.

Ltac bool_2_prop_ssr_full_branch :=
    match goal with
    | _ => bool_2_prop_ssr_branch
    | _ => rewrite orb_true_iff
    | _ => rewrite orb_false_iff
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
    | |- false = _ => symmetry
    | |- true = false => rewrite true_eq_false_False
    | |- true = _ => symmetry
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
    | _ => ssr_simpl_branch

    | _ => rewrite iff_True_R
    | _ => rewrite iff_True_L
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
