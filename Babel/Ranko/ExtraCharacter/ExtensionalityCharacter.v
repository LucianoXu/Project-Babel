(** ExtensionalityCharacter.v 


    >>>>>>>>>>>>>>>>>>>
    Manually import this Character after importing [Ranko] to equip her with
    this extensionality character.

    WARNING : importing this Character also means introducing extensionality
    axioms into the logic system.

*)

From mathcomp Require Import all_ssreflect.
Require Import Coq.Unicode.Utf8_core.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Babel Require Import ExtraDogma.Extensionality.
From Babel.Ranko Require Import ExtraCharacterHook.


Ltac extensionality_step
        top_step
        ::=
    match goal with
    (** functional extensionality *)
    | _ => apply functional_extensionality
    (** propositional extensionality *)
    | _ => apply propositional_extensionality
    end.

Ltac extensionality_step_sealed :=
    idtac; let rec top := extensionality_step_sealed in 
        extensionality_step top.

Ltac extensionality_level :=
    repeat extensionality_step_sealed.