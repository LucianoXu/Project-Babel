(** IotaDescriptionCharacter.v 


    >>>>>>>>>>>>>>>>>>>
    Manually import this Character after importing [Ranko] to equip her with
    this IotaDescription character.

    WARNING : importing this Character also means introducing iota description
    axioms into the logic system.

*)

From mathcomp Require Import all_ssreflect.
Require Import Coq.Unicode.Utf8_core.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Coq Require Import Bool.
From Babel Require Import ExtraDogma.IotaDescription.
From Babel.Ranko Require Import ExtraCharacterHook.


Ltac iotaDescription_step
        top_step
        ::=
    match goal with
    | _ => rewrite iota_eqP

    | |- ι (?i) _ = true -> _ => 
        rewrite (iota_spec (i))

    | |- ι (?i) _ = true => 
        rewrite (iota_spec (i))

    | |- ι (?i) _ = false -> _ => 
        rewrite -Bool.not_true_iff_false /not (iota_spec (i))

    | |- ι (?i) _ = false => 
        rewrite -not_true_iff_false /not
    end.


Ltac iotaDescription_step_sealed :=
    idtac; let rec top := iotaDescription_step_sealed in 
        iotaDescription_step top.

Ltac iotaDescription_level :=
    repeat iotaDescription_step_sealed.