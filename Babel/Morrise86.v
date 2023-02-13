Require Import POrder POrderSet TerminalDogma.premises
                                TerminalDogma.Extensionality.
Require Import SetFacility POrderFacility.

Require Import Ranko.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** The type of state. *)
Axiom Stt : Type.


Definition Sta := 𝒫(Stt).



