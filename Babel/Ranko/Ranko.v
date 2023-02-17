(** ranko.v
    Character Synthesis
*)

(** 为她创造了这个世界，又在这个世界中生出她来。 *)

From Babel.Ranko Require Export CentralCharacter 
                                LogicCharacter
                                SetCharacter
                                POrderCharacter.

From Coq Require Export Zify.
From mathcomp Require Export zify ssrZ.


Ltac ranko_step 
        split_mode 
        general_apply_depth
        :=
    idtac; let rec top := 
        ranko_step
    in match goal with

    (* this branch includes set_step and logic_step *)
    | _ => porder_step top split_mode general_apply_depth

    end.


(** Don't call her inside a section, as she cannot stop moving down the 
    premises sometimes. *)
Ltac ranko split_mode general_apply_depth 
        := repeat ranko_step split_mode general_apply_depth.

Tactic Notation "ranko" 
        integer(split_mode) constr(general_apply_depth)
    := ranko split_mode general_apply_depth.

Tactic Notation "ranko" := ranko 0 7.

