(** Sequence.v *)

From Babel Require Import TerminalDogma.
From Babel Require Import TerminalDogma.Infinity.
From Babel Require Import TerminalDogma.Isomorphism.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(*
(** The module to deal with finite or countable infinite sequences. *)

Open Scope Nat_scope.

Record finSeq (T : Type) : Type := build_finSeq {
    finSeq_len : nat;
    finSeq_f :> [1, finSeq_len]N -> T;
}.

Definition infSeq (T : Type) : Type := nat -> T.

Inductive seque (T : Type) : Type :=
| finSeq_obj :> finSeq T -> seque T
| infSeq_obj :> infSeq T -> seque T.

Definition index (T : Type) (s : seque T) : Set := 
    match s with
    | finSeq_obj s => [1, finSeq_len s ]N
    | infSeq_obj _ => nat
    end.

Lemma finSeq_index_eq (T : Type) (s1 s2 : finSeq T) (Heq : index s1 = index s2)
    : finSeq_len s1 = finSeq_len s2.
Abort.

Definition seque2fun (T : Type) (s : seque T) : index s -> T :=
    match s with
    | finSeq_obj s' => s'
    | infSeq_obj s' => s'
    end.

Coercion seque2fun : seque >-> Funclass.


(** finite sequence with length as dependent type *)

Record sequeN (T : Type) (n : nat) := build_sequeN {
    sequeN_obj :> finSeq T;
    sequeN_len : finSeq_len sequeN_obj = n;
}.

(** sequence zip*)

Definition finsSeq_fun_zip (X Y Z: Type) (sx : finSeq X) (sy : finSeq Y) 
    (HdimEq : finSeq_len sx = finSeq_len sy) (f : X -> Y -> Z) : finSeq Z.
Proof.
    refine (@build_finSeq Z (finSeq_len sx) _).
    move => x. apply f. apply (sx x). apply sy. by rewrite -HdimEq.
Defined.


Definition seq_fun_zip (X Y Z: Type) (sx : seque X) (sy : seque Y) 
    (HdimEq : index sx = index sy) (f : X -> Y -> Z) : seque Z.
Proof. rewrite /index in HdimEq. destruct sx, sy. 
    { apply finSeq_obj. refine (@build_finSeq Z (finSeq_len f0) _).
    move => x. apply f. apply (f0 x). apply f1. by rewrite -HdimEq. }
    by destruct (fin_inf_neq HdimEq).
    by symmetry in HdimEq; destruct (fin_inf_neq HdimEq).
    { apply infSeq_obj. move => n. apply f. by apply /i /n. by apply /i0 /n. }
Defined.

Definition sequeN_fun_zip (n : nat) (X Y Z: Type) (sx : sequeN X n)
        (sy : sequeN Y n) (f : X -> Y -> Z) : sequeN Z n.
Proof. 
    have Heqx : finSeq_len sx = n. by apply sx.
    have HeqxI : ([1, n]N:Type) = [1, finSeq_len sx]N. f_equal. by rewrite Heqx.
    have Heqy : finSeq_len sy = n. by apply sy.
    have HeqyI : ([1, n]N:Type) = [1, finSeq_len sy]N. f_equal. by rewrite Heqy.
    set fs := @build_finSeq _ n 
        (fun x => 
            f (sx (transport HeqxI x)) (sy (transport HeqyI x))).
    refine (@build_sequeN _ _ fs _).
    by rewrite /fs => //.
Defined.

Print sequeN_fun_zip.
    
(** sequence fold *)
Definition sequeN_foldl (n : nat) (X Y : Type) (h : Y) (sx : sequeN X n)
    (f : Y -> X -> Y) : Y.
Proof. elim : n sx. by move => x; exact h.
*)
    


