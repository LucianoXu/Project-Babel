(** AllDecidableCharacter.v 


    >>>>>>>>>>>>>>>>>>>
    Manually import this Character after importing [Ranko] to equip her with
    this AllDecidable character.

    WARNING : importing this Character also means introducing all decidable
    axioms into the logic system.

*)

From mathcomp Require Import all_ssreflect.
Require Import Coq.Unicode.Utf8_core.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Babel Require Import ExtraDogma.AllDecidable.
From Babel.Ranko Require Import ExtraCharacterHook.


Ltac allDecidable_step
        top_step
        ::=
    match goal with
    | H : decide_oracle _ = true |- _ => 
        rewrite decide_oracle_true in H
    | H : decide_oracle _ = false |- _ => 
        rewrite decide_oracle_false in H
    | _ => rewrite decide_oracle_true
    | _ => rewrite decide_oracle_false
    end.

Ltac allDecidable_step_sealed :=
    idtac; let rec top := allDecidable_step_sealed in 
        allDecidable_step top.

Ltac allDecidable_level :=
    repeat allDecidable_step_sealed.