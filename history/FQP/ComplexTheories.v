From Babel Require Export FQP.premises.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


From Babel Require FieldTheories.
From Babel Require RealTheories.



Module Export ComplexTheory.

Export FieldTheories.FieldTheory.
Export RealTheories.RealTheory.

Definition ℂ : Type := R * R.
(** We'll make C opaque so Coq doesn't treat it as a pair. *)
Opaque C.

Declare Scope ℂ_scope.
Delimit Scope ℂ_scope with ℂ.
Bind Scope ℂ_scope with ℂ.
Open Scope ℂ_scope.

(** real part is the first element *)
Definition real : ℂ -> R := fst.
(** imaginary part is the second element *)
Definition imag : ℂ -> R := snd.


Definition R2C (r : R) : ℂ := (r, 0).
Coercion R2C : R >-> ℂ.

(** Define the 'real numbers' in ℂ, and the corresponding transition *)
Definition realc (c : ℂ) := snd c = 0.
(** Given a proof for the reality of c, we get the real part as the real 
    number. *)
Definition realc2R (c : ℂ) (H : realc c) : R := fst c.
Coercion realc2R : realc >-> R.

(** We give names to three generally useful constants *)
Notation i := (0, 1).
Notation "0" := (0:ℂ) : ℂ_scope.
Notation "1" := (1:ℂ) : ℂ_scope.

(** We can define plus component-wise *)

Definition Cplus (c1 c2 : ℂ) : ℂ := (fst c1 + fst c2, snd c1 + snd c2).

(** And then define minus and opp together: *)

Definition Copp (c : ℂ) : ℂ := (- fst c, - snd c).
Definition Cminus (c1 c2 : ℂ) : ℂ := Cplus c1 (Copp c2).

(** Multiplication and division. We'll define division in terms of an inverse. *)

Definition Cmult (c1 c2 : ℂ) : ℂ :=
    (fst c1 * fst c2 - snd c1 * snd c2, fst c1 * snd c2 + snd c1 * fst c2).

Definition Cinv (c : ℂ) : ℂ :=
  (fst c / (fst c ^ 2 + snd c ^ 2), - snd c / (fst c ^ 2 + snd c ^ 2)).

Definition Cdiv (c1 c2 : ℂ) : ℂ := Cmult c1 (Cinv c2).


Definition Cnorm2 (c : ℂ) : R := fst c ^ 2 + snd c ^ 2. 
Definition Cnorm (c : ℂ) : R := √ (Cnorm2 c).
Arguments Cnorm2 c /.
Arguments Cnorm c /.

Infix "+" := Cplus : ℂ_scope.
Notation "- x" := (Copp x) : ℂ_scope.
Infix "-" := Cminus : ℂ_scope.
Infix "*" := Cmult : ℂ_scope.
Notation "/ x" := (Cinv x) : ℂ_scope.
Infix "/" := Cdiv : ℂ_scope.
Notation "⎸ x  ⎸²" := (Cnorm2 x) : ℂ_scope.
Notation "⎸ x  ⎸" := (Cnorm x) : ℂ_scope.
 

(* ################################################################# *)

Lemma c_proj_eq : forall (c1 c2 : ℂ), 
  fst c1 = fst c2 -> snd c1 = snd c2 -> c1 = c2.
Proof. intros. destruct c1, c2. simpl in *. subst. reflexivity. Qed.

Ltac lca := eapply c_proj_eq; simpl; lra.

(* ################################################################# *)
(** * C is a field *)

Open Scope ℂ_scope.

Lemma C1_neq_C0 : 1 <> 0. Proof. intros F. inversion F. lra. Qed.

Lemma Cplus_comm : forall c1 c2 : ℂ, c1 + c2 = c2 + c1. Proof. intros. lca. Qed.
Lemma Cplus_assoc : forall c1 c2 c3 : ℂ, c1 + c2 + c3 = c1 + (c2 + c3).
Proof. intros. lca. Qed.

Lemma Cplus_opp_r : forall c : ℂ, c + - c = 0. Proof. intros. lca. Qed.

Lemma Cplus_0_l : forall c : ℂ, 0 + c = c. Proof. intros. lca. Qed.

Lemma Cmult_comm : forall c1 c2:ℂ, c1 * c2 = c2 * c1. Proof. intros. lca. Qed.

Lemma Cmult_assoc : forall c1 c2 c3:ℂ, c1 * c2 * c3 = c1 * (c2 * c3).
Proof. intros. lca. Qed.

Lemma Cmult_1_l : forall c:ℂ, 1 * c = c. Proof. intros. lca. Qed.

Lemma Cmult_plus_distr_r : forall c1 c2 c3:ℂ, (c1 + c2) * c3 = c1 * c3 + c2 * c3.
Proof. intros. lca. Qed.

Lemma Cinv_l : forall c:ℂ, c <> 0 -> / c * c = 1.
Proof.
  intros.
  eapply c_proj_eq; simpl; unfold Rminus, Rdiv.
  - repeat rewrite <- Ropp_mult_distr_l.
    rewrite Ropp_involutive.
    repeat rewrite Rmult_1_r.
    rewrite (Rmult_comm (fst c)). rewrite Rmult_assoc.
    rewrite (Rmult_comm (snd c) (/ _)). rewrite Rmult_assoc.
    rewrite <- Rmult_plus_distr_l.
    rewrite Rinv_l; try lra.
    contradict H. apply Rplus_sqr_eq_0 in H. lca.
  - repeat rewrite Rmult_1_r.
    rewrite (Rmult_comm (fst c)). rewrite Rmult_assoc.
    rewrite (Rmult_comm (- snd c)). rewrite Rmult_assoc.
    rewrite <- Rmult_plus_distr_l.
    lra.
Qed.       

(** Construct the complex field *)
Definition ℂ_field : field.
Proof. 
  apply (@build_field ℂ 0 1 Cplus Cmult Cminus Copp Cdiv Cinv eq).
  constructor. constructor.
  (* addition *)
  (* left identity *) apply Cplus_0_l.
  (* commutativity *) apply Cplus_comm.
  (* associativity *) intros; rewrite Cplus_assoc; easy.
  (* multiplication *)
  (* left identity *) apply Cmult_1_l.
  (* commutativity *) apply Cmult_comm.
  (* associativity *) intros; rewrite Cmult_assoc; easy.
  (* distributivity *) apply Cmult_plus_distr_r.
  (* sub = opp *) reflexivity.
  (* additive inverse *) apply Cplus_opp_r.  
  (* 0 <> 1 *) apply C1_neq_C0.
  (* div = inv *) reflexivity.
  (* multiplicative inverse *) apply Cinv_l.
Defined.

Add Field CField : (field_proof ℂ_field).  

(** Some additional useful lemmas *)

Lemma Cplus_opp_l : forall c : ℂ, - c + c = 0. Proof. intros. lca. Qed.
Lemma Cplus_0_r : forall c : ℂ, c + 0 = c. Proof. intros. lca. Qed.
Lemma Cmult_0_l : forall c:ℂ, 0 * c = 0. Proof. intros. lca. Qed.
Lemma Cmult_0_r : forall c:ℂ, c * 0 = 0. Proof. intros. lca. Qed.
Lemma Cmult_1_r : forall c:ℂ, c * 1 = c. Proof. intros. lca. Qed.

Lemma Cmult_plus_dist_l : forall c1 c2 c3:ℂ, c1 * (c2 + c3) = c1 * c2 + c1 * c3.
Proof. intros. lca. Qed.
Lemma Cmult_plus_dist_r : forall c1 c2 c3:ℂ, (c1 + c2) * c3 = c1 * c3 + c2 * c3.
Proof. intros. lca. Qed.
    
Lemma Cinv_r : forall c:ℂ, c <> 0 -> c * /c = 1.
Proof. intros. rewrite Cmult_comm. apply Cinv_l. easy. Qed.

Lemma Copp_mult_distr_r : forall c1 c2 : ℂ, - (c1 * c2) = c1 * - c2.
Proof. intros; lca. Qed.
Lemma Copp_mult_distr_l : forall c1 c2 : ℂ, - (c1 * c2) = - c1 * c2.
Proof. intros; lca. Qed.
Lemma Copp_involutive: forall c : ℂ, - - c = c. Proof. intros; lca. Qed.
  
Lemma R2C_neq : forall (r1 r2 : R), r1 <> r2 -> R2C r1 <> R2C r2.
Proof. intros r1 r2 H F. inversion F. easy. Qed.

(* ################################################################# *)
(** * The complex conjugate *)

Definition Cconj (x : ℂ) : ℂ := (fst x, (- snd x)%R).

Notation "a ^*" := (Cconj a) (at level 10) : ℂ_scope.

Lemma Cconj_R : forall r : R, r^* = r.         Proof. intros; lca. Qed.
Lemma Cconj_0 : 0^* = 0.                  Proof. lca. Qed.
Lemma Cconj_opp : forall C, (- C)^* = - (C^*). Proof. reflexivity. Qed.
Lemma Cconj_rad2 : (/ √2)^* = / √2.       Proof. lca. Qed.
Lemma Cconj_involutive : forall c, (c^*)^* = c. Proof. intros; lca. Qed.
Lemma Cconj_plus_distr : forall (x y : ℂ), (x + y)^* = x^* + y^*. Proof. intros; lca. Qed.
Lemma Cconj_mult_distr : forall (x y : ℂ), (x * y)^* = x^* * y^*. Proof. intros; lca. Qed.


Lemma Cconj_mult_norm2 : forall c, c^* * c = ⎸c ⎸².
Proof. move => c. rewrite /Cconj /Cnorm2. by lca. Qed.

(** Note that the type is ℂ in this equation. *)
Lemma mult_Cconj_norm2 : forall c, c * c^* = ⎸c ⎸².
Proof. move => c. rewrite Cmult_comm. by apply Cconj_mult_norm2. Qed.


(* ================================================================= *)
(** ** Solving equations with square roots *)

(* Dealing with square roots is important for quantum computing, 
   so we'll prove a few lemmas and add some automation here. *)

Lemma Csqrt_inv : forall (r : R), 0 < r -> R2C (√ (/ r)) = (/ √ r).
Proof.
  intros r H.
  apply c_proj_eq; simpl.
  field_simplify_eq [(@pow2_sqrt r (or_introl H)) (@sqrt_inv r H)].
  rewrite Rinv_r. reflexivity.
  apply sqrt_neq_0_compat; lra.
  apply sqrt_neq_0_compat; lra.
  field. apply sqrt_neq_0_compat; lra.
Qed.  

Lemma Csqrt2_inv : R2C (√ (/ 2)) = (/ √ 2).
Proof. apply Csqrt_inv; lra. Qed.  

Lemma Csqrt2_square : √2 * √2 = 2. 
Proof.
  eapply c_proj_eq; simpl; try lra.
  rewrite Rmult_0_r Rminus_0_r.
  apply sqrt_def.
  lra.
Qed.

Ltac nonzero :=
  repeat match goal with
  | |- _ /\ _ => split
  end;
  try match goal with
  | |- (?x <> 0)%ℂ  => apply R2C_neq
  end;
  repeat match goal with 
  | |- (√?x <> 0)%R  => apply sqrt_neq_0_compat
  | |- (/?x <> 0)%R  => apply Rinv_neq_0_compat
  end; 
  match goal with 
  | |- (_ <> _)%R        => lra
  | |- (_ < _)%R        => lra
  end.

Ltac R_field_simplify := repeat field_simplify_eq [pow2_sqrt2 sqrt2_inv];
                         try nonzero.
Ltac R_field := R_field_simplify; reflexivity.
Ltac C_field_simplify := repeat field_simplify_eq [Csqrt2_square Csqrt2_inv];
                         try nonzero.
Ltac C_field := C_field_simplify; reflexivity.


End ComplexTheory.