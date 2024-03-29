(** ranko.v
    Character Synthesis
*)

(** 为她创造了这个世界，又在这个世界中生出她来。 *)


From Babel.Ranko Require Export CentralCharacter 
                                LogicCharacter
                                SetCharacter
                                POrderCharacter.
                                
(** Hooks only, to avoid introducing extra axioms into the system 
    unintentionally.*)
From Babel.Ranko Require Export ExtraCharacterHook.

From Coq Require Import Zify.
From mathcomp Require Import all_ssreflect zify ssrZ.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Ltac ranko_step 
        split_mode 
        general_apply_depth
        eexists_mode
        :=
    idtac; let rec top := 
        ranko_step
    in match goal with

    | _ => porder_step_PRE top split_mode general_apply_depth eexists_mode
    | _ => porder_basic_step_PRE top split_mode general_apply_depth eexists_mode
        | _ => set_step_PRE top split_mode general_apply_depth eexists_mode
            | _ => logic_branch top split_mode general_apply_depth eexists_mode
            | _ => iotaDescription_step ltac:(top split_mode general_apply_depth eexists_mode)
            | _ => extensionality_step ltac:(top split_mode general_apply_depth eexists_mode)
            | _ => allDecidable_step ltac:(top split_mode general_apply_depth eexists_mode)
            | _ => classical_step ltac:(top split_mode general_apply_depth eexists_mode)
            
            | _ => central_step top split_mode general_apply_depth eexists_mode
        | _ => set_step_POST top split_mode general_apply_depth eexists_mode
    | _ => porder_basic_step_POST top split_mode general_apply_depth eexists_mode
    | _ => porder_step_POST top split_mode general_apply_depth eexists_mode
    | H : _ |- _ => by apply H
    end.


(** Don't call her inside a section, as she cannot stop moving down the 
    premises sometimes. *)
Ltac ranko 
        split_mode 
        general_apply_depth 
        eexists_mode
        := 
        repeat ranko_step split_mode general_apply_depth eexists_mode.

Tactic Notation "ranko_step" := ranko_step LAZY 7 LAZY.
Tactic Notation "ranko" := ranko LAZY 7 LAZY.

