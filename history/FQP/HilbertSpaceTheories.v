From Babel Require Import FQP.premises.
From Babel Require Import TerminalDogma.Sequence.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Require ComplexTheories.
Require VectorSpaceTheories.



Module HilbertSpaceTheory.

Export ComplexTheories.ComplexTheory.
Export VectorSpaceTheories.VectorSpaceTheory.

(** Definition 2.1.2 (complex inner product space) *)
Record CIP_space := build_ipspace {
    Vs :> vspace ℂ_field;
    Vsdot : Vs -> Vs -> ℂ;

    (** dot non-negative *)
    Vsdot_realc : forall u : Vs, realc (Vsdot u u);
    Vsdot_pos_def : forall u : Vs, Vsdot_realc u >= 0; 
    Vsdot_pos_0 : forall u : Vs, ((Vsdot_realc u) = 0%R :> R) <-> u = 𝟎;

    (** dot conjugate *)
    Vsdot_conj : forall u v : Vs, (Vsdot u v)^* = Vsdot v u;

    (** dot linearity *)
    Vsdot_linear : forall (c1 c2 : ℂ) (u v1 v2 : Vs), 
        Vsdot u (Vadd (@Vscal _ Vs c1 v1) (@Vscal _ Vs c2 v2)) = 
        (c1 * (Vsdot u v1) + c2 * (Vsdot u v2))%ℂ;
}.

(** Note : The level for a ∗ b is 30, and we want
        a ∗ u ∙ v to
    to mean
        a ∗ (u ∙ v), 
    so level 35 is appropriate. *)
Notation " u '∙' v " := (Vsdot u v) (at level 35) : Vspace_scope.

(** Dirac Notation *)
Notation " <[ u | v ]> " := (Vsdot u v) : Vspace_scope.

(** orthogonal *)
Definition orthogonal (CIPs : CIP_space) (u v : CIPs) := <[ u | v ]> = 0.
Notation " u '⊥' v " := (orthogonal u v) (at level 20) : Vspace_scope.
(** [] *)

Definition f_norm (CIPs : CIP_space) (u : CIPs) := √ (Vsdot_realc u).
Notation " |[ u ]| " := (f_norm u) : Vspace_scope.

Definition unit_vector (CIPs : CIP_space) (u : CIPs) : Prop := |[ u ]| = 1%R.


(** Definition 2.1.3 *)

Record v_Cauchy_seq (H : CIP_space) := mk_v_Cauchy_seq {
    f_v_seq :> infSeq H;
    seq_conv_proof : 
        forall e : { r : R | r > 0 },
        exists N : nat, forall m n : { n : nat | (n > N)%nat }, 
        |[ (f_v_seq (proj1_sig m)) + (- (f_v_seq (proj1_sig n))) ]| < proj1_sig e;
}.

Definition seq_lim (H : CIP_space) (f : infSeq H) (psi : H) :=
    forall e : { r : R | r > 0 },
    exists N : nat, forall n : { n : nat | (n > N)%nat }, 
    |[ (f (proj1_sig n)) + (- psi) ]| < proj1_sig e.

(** Definition 2.1.4 *)
Record Hilbert_space := build_Hspace {
    H :> CIP_space;
    H_complete : forall s : v_Cauchy_seq H, exists psi, seq_lim s psi;
}.

(** Definition 2.1.5 *)

Definition is_ortho_basis (H : Hilbert_space) (s : Seque H) : Prop :=
    forall i j : index s, s i ⊥ s j.

Record ortho_basis (H : Hilbert_space) := build_ortho_basis {
    ortho_basis_obj :> Seque H;
    ortho_basis_proof : is_ortho_basis ortho_basis_obj;
}.

Definition in_linear_comb (H : Hilbert_space) (s : Seque H) (psi : H) :=
    exists 



End HilbertSpaceTheory.