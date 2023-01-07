(** Infinity.v *)

From Ranko Require Import TerminalDogma.premises.
From Ranko Require Import TerminalDogma.Isomorphism.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Nat_scope.

Definition finite (T : Type) := exists n:nat, T ≅ [ 1 , n ]N.

Definition countable_inf (T : Type) := T ≅ nat.