(** Parity.v *)
From Babel Require Import TerminalDogma 
                          ExtraDogma.Extensionality
                          SetFacility
                          POrderFacility.

From Babel Require Import Ranko
                            ExtensionalityCharacter
                            ClassicalCharacter.

From Babel.MetaLanguage Require Export Notations.

From Coq Require Import Relations Classical.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope Parity_scope.
Open Scope Parity_scope.


(** Parity *)
Notation parity := bool.
Notation FD := true.
Notation BD := false.

Notation " - P " := (~~ P) : Parity_scope.

(** Parity Transformation *)

(*
Definition PTrans (theory : Type) (theory_of : parity -> theory) 
    : parity -> theory :=
        fun 𝑷 => theory_of (- 𝑷).
*)

