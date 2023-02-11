(** NotationRefinements.v *)
From mathcomp Require Import all_ssreflect.
Require Import Coq.Unicode.Utf8_core.
From Coq Require Import Reals.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope Nat_scope.
Declare Scope R_scope.

Notation " [ a , b ]N " := ({x : nat | (a <= x <= b)%nat }) : Nat_scope.
Notation " ( a , b )N " := ({x : nat | (a < x < b)%nat }) : Nat_scope.
Notation " ( a , b ]N " := ({x : nat | (a < x <= b)%nat }) : Nat_scope.
Notation " [ a , b )N " := ({x : nat | (a <= x < b)%nat }) : Nat_scope.
Notation " [ a , ∞ )N " := ({x : nat | (a <= x)%nat }) : Nat_scope.
Notation " ( a , ∞ )N " := ({x : nat | (a < x)%nat }) : Nat_scope.

Notation " [ a , b ]R " := ({x : R | (a <= x <= b)%R }) : R_scope.
Notation " ( a , b )R " := ({x : R | (a < x < b)%R }) : R_scope.
Notation " ( a , b ]R " := ({x : R | (a < x <= b)%R }) : R_scope.
Notation " [ a , b )R " := ({x : R | (a <= x < b)%R }) : R_scope.
Notation " [ a , ∞ )R " := ({x : R | (a <= x)%R }) : R_scope.
Notation " ( a , ∞ )R " := ({x : R | (a < x)%R }) : R_scope.
Notation " ( - ∞ , b ]R " := ({x : R | (x <= b)%R }) : R_scope.
Notation " ( - ∞ , b )R " := ({x : R | (x < b)%R }) : R_scope.
Notation " ( - ∞ , ∞ )R " := (R) (only parsing): R_scope.


Open Scope Nat_scope.
Open Scope R_scope.