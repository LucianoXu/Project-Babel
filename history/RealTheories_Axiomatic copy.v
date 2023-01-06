Require Export premises.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Ring.
Require Field.

Module Type RealAxiomType.

Parameter ℝ : Set.

Declare Scope ℝ_scope.
Delimit Scope ℝ_scope with ℝ.
Local Open Scope ℝ_scope.

Parameter R0 : ℝ.
Parameter R1 : ℝ.

(** addition and multiplication *)
Parameter Rplus : ℝ -> ℝ -> ℝ.
Parameter Rmult : ℝ -> ℝ -> ℝ.

(** the corresponding inverse elements *)
Parameter Ropp : ℝ -> ℝ.
Parameter Rinv : ℝ -> ℝ.

Infix "+" := Rplus : ℝ_scope.
Infix "*" := Rmult : ℝ_scope.
Notation "- x" := (Ropp x) : ℝ_scope.
Notation "/ x" := (Rinv x) : ℝ_scope.

(** We'd like to be able to convert natural numbers to Rs, thereby allowing
    ourselves to write numbers like 0, 1, 2, 3... *)

Fixpoint N2R (n : nat) : ℝ :=
    match n with
    | O    => R0
    | 1    => R1            
    | S n' => R1 + N2R n'
    end.
Coercion N2R : nat >-> ℝ.

(* ################################################################# *)
(** * The Field Equations *)

Axiom R1_neq_R0 : (1:ℝ) <> (0:ℝ).

(** Addition axioms *)

Axiom Rplus_comm : forall r1 r2 : ℝ, r1 + r2 = r2 + r1.

Axiom Rplus_assoc : forall r1 r2 r3 : ℝ, r1 + r2 + r3 = r1 + (r2 + r3).

Axiom Rplus_opp_r : forall r : ℝ, r + - r = 0.

Axiom Rplus_0_l : forall r : ℝ, 0 + r = r.

(** Multiplicative axioms *)

Axiom Rmult_comm : forall r1 r2:ℝ, r1 * r2 = r2 * r1.

Axiom Rmult_assoc : forall r1 r2 r3:ℝ, r1 * r2 * r3 = r1 * (r2 * r3).

Axiom Rinv_l : forall r:ℝ, r <> 0 -> / r * r = 1.

Axiom Rmult_1_l : forall r:ℝ, 1 * r = r.

Axiom Rmult_plus_distr_l : forall r1 r2 r3:ℝ, r1 * (r2 + r3) = r1 * r2 + r1 * r3.

(* ################################################################# *)
(** * Ordering *)

(** We also impose the standard ordering on real numbers, again by
    means of axioms *)

Parameter Rlt : ℝ -> ℝ -> Prop.

Infix "<" := Rlt : ℝ_scope.

Definition Rgt (r1 r2:ℝ) : Prop := r2 < r1.
Definition Rle (r1 r2:ℝ) : Prop := r1 < r2 \/ r1 = r2.
Definition Rge (r1 r2:ℝ) : Prop := Rgt r1 r2 \/ r1 = r2.

Infix "<=" := Rle : ℝ_scope.
Infix ">=" := Rge : ℝ_scope.
Infix ">" := Rgt : ℝ_scope.

Axiom total_order_T : forall r1 r2 : ℝ, {r1 < r2} + {r1 = r2} + {r1 > r2}.
    
Axiom Rlt_asym : forall r1 r2 : ℝ, r1 < r2 -> ~ r2 < r1.

Axiom Rlt_trans : forall r1 r2 r3 : ℝ, r1 < r2 -> r2 < r3 -> r1 < r3.

Axiom Rplus_lt_compat_l : forall r r1 r2 : ℝ, r1 < r2 -> r + r1 < r + r2.

Axiom Rmult_lt_compat_l : forall r r1 r2 : ℝ, 0 < r -> r1 < r2 -> r * r1 < r * r2.


(* ################################################################# *)
(** * Completeness *)

(** Not every field corresponds to the real numbers:
    Even the rational numbers (a strict subset of the reals) form a
    field. The last thing we need to "complete" the real numbers is
    the _completeness_ axiom. This states that every bounded set of
    real numbers has a least upper bound, which itself is a real
    number.

    As usual, we will express sets as functions of type [R -> Prop],
    indicating whether the given real number is a member of the
    set. *)

Definition is_upper_bound (E:ℝ -> Prop) (m:ℝ) := forall x:ℝ, E x -> x <= m.

Definition bound (E:ℝ -> Prop) := exists m : ℝ, is_upper_bound E m.

Definition is_lub (E:ℝ -> Prop) (m:ℝ) :=
    is_upper_bound E m /\ (forall b:ℝ, is_upper_bound E b -> m <= b).

Axiom
    completeness :
    forall E:ℝ -> Prop,
        bound E -> (exists x : ℝ, E x) -> { m:ℝ | is_lub E m }.
        
(* ################################################################# *)
(** * Computations *)

(* ================================================================= *)
(** ** The exp and log functions *)
Parameter RpowN : ℝ -> nat -> ℝ.
Infix "^" := RpowN : ℝ_scope.

Parameter Rsqrt : ℝ -> ℝ.
Notation "√ x" := (Rsqrt x) (at level 0) : ℝ_scope.


End RealAxiomType.


Module RealTheory (Export RealAxiom : RealAxiomType).

Open Scope ℝ_scope.

(** Other basic operations are given in terms of our declared ones *)

Definition Rminus (r1 r2:ℝ) : ℝ := r1 + - r2.
Definition Rdiv (r1 r2:ℝ) : ℝ := r1 * / r2.

Infix "-" := Rminus : ℝ_scope.
Infix "/" := Rdiv : ℝ_scope.


Lemma Rplus_0_r : forall r : ℝ, r + 0 = r.
Proof.
  (* WORKED IN CLASS *)
  intros r.
  rewrite Rplus_comm.
  apply Rplus_0_l.
Qed.
  
Lemma Rplus_opp_l : forall r, -r + r = 0.
Proof.
  (* WORKED IN CLASS *)
  intros r.
  rewrite Rplus_comm.
  apply Rplus_opp_r.
Qed.

Lemma Ropp_0 : -0 = 0.
Proof.
  rewrite <- (Rplus_0_l (-0)).
  rewrite Rplus_opp_r.
  reflexivity.
Qed.

Lemma Rplus_cancel_l : forall r1 r2 r3, r1 + r2 = r1 + r3 -> r2 = r3.
Proof.
  intros r1 r2 r3 H.
  rewrite <- Rplus_0_l.
  rewrite <- (Rplus_opp_l r1).
  rewrite Rplus_assoc.
  rewrite <- H.
  rewrite <- Rplus_assoc.
  rewrite Rplus_opp_l.
  rewrite Rplus_0_l.
  reflexivity.
Qed.
    
Lemma R0_unique : forall r1 r2, r1 + r2 = r1 -> r2 = 0.
Proof.
  intros r1 r2 H.
  rewrite <- Rplus_0_r in H.
  eapply Rplus_cancel_l.
  apply H.
Qed.  


Lemma Rmult_0_r : forall r, r * 0 = 0.
Proof.
  (* WORKED IN CLASS *)
  intros r.
  apply (@R0_unique (r * 0)).
  rewrite <- Rmult_plus_distr_l.
  rewrite Rplus_0_l.
  reflexivity.
Qed.

Lemma Rmult_plus_distr_r : forall r1 r2 r3:ℝ, (r1 + r2) * r3 = r1 * r3 + r2 * r3.
Proof.
  (* WORKED IN CLASS *)
  intros r1 r2 r3.
  rewrite Rmult_comm.
  rewrite Rmult_plus_distr_l.
  rewrite !(@Rmult_comm r3).
  reflexivity.
Qed.

Lemma Rinv_r : forall r:ℝ, r <> 0 -> r * / r = 1.
Proof.
  (* WORKED IN CLASS *)
  intros. rewrite Rmult_comm.
  apply Rinv_l.
  assumption.
Qed.
  
(* ================================================================= *)
(** ** The Ring and Field tactics *)

(** We can tell Coq that R forms an algebraic _ring_ and _field_. *)

Export Ring.
Export Field.

Lemma R_Ring_Theory : ring_theory R0 R1 Rplus Rmult Rminus Ropp eq.
Proof.
  constructor.
  (* addition *)
  (* left identity *) apply Rplus_0_l.
  (* commutativity *) apply Rplus_comm.
  (* associativity *) intros; rewrite Rplus_assoc; easy.
  (* multiplication *)
  (* left identity *) apply Rmult_1_l.
  (* commutativity *) apply Rmult_comm.
  (* associativity *) intros; rewrite Rmult_assoc; easy.
  (* distributivity *) apply Rmult_plus_distr_r.
  (* sub = opp *) reflexivity.
  (* additive inverse *) apply Rplus_opp_r.
Defined.

Add Ring RRing : R_Ring_Theory.  

Lemma R_Field_Theory : field_theory R0 R1 Rplus Rmult Rminus Ropp Rdiv Rinv eq.
Proof.
  constructor.
  (* ring axioms *) apply R_Ring_Theory.
  (* 0 <> 1 *) apply R1_neq_R0.
  (* div = inv *) reflexivity.
  (* multiplicative inverse *) apply Rinv_l.
Defined.

Add Field RField : R_Field_Theory.

End RealTheory.















