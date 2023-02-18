(** ClassicalCharacter.v 


    >>>>>>>>>>>>>>>>>>>
    Manually import this Character after importing [Ranko] to equip her with
    this Classical character.

    WARNING : importing this Character also means introducing classical
    axioms into the logic system.

*)

From mathcomp Require Import all_ssreflect.
Require Import Coq.Unicode.Utf8_core.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Babel Require Import ExtraDogma.Classical.
From Babel.Ranko Require Import ExtraCharacterHook.


Ltac classical_step
        top_step
        ::=
    match goal with
    | |- ~ ( _ /\ _ ) -> _ => 
        let temp := fresh "Htemp" in
            intros temp; apply not_and_or in temp; move: temp

    | |- ~ (forall _, _) -> _ => 
        let temp := fresh "Htemp" in
            intros temp; apply not_all_ex_not in temp; move: temp

    | |- ~ (forall _, _) => apply ex_not_not_all
    end. 

Ltac classical_step_sealed :=
    idtac; let rec top := classical_step_sealed in 
        classical_step top.

Ltac classical_level :=
    repeat classical_step_sealed.