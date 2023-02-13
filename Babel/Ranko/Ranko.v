(** ranko.v
    Character Synthesis
*)

(** 为她创造了这个世界，又在这个世界中生出她来。 *)

From Babel.Ranko Require Export CentralCharacter 
                                LogicCharacter
                                SetCharacter
                                POrderCharacter.

Ltac ranko_step :=
    idtac; let rec top := ranko_step in
    match goal with

    (* this branch includes set_step and logic_step *)
    | _ => porder_step top integer:(0)

    end.


(** Don't call her inside a section, as she cannot stop moving down the 
    premises sometimes. *)
Ltac ranko := repeat ranko_step.

