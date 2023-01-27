
(***********************************)
(** The gadget for abort semantics *)

Lemma rho_s_em_em:

        rho_s = ∅ -> { _ : 𝒟(qs)⁻ | rho_s <> ∅ } = ∅.

Proof.
    move => ->.
    replace (∅ ≠ ∅) with False => //.
    by apply propositional_extensionality.
Qed.

Lemma rho_s_nem_U:

        rho_s <> ∅ -> { _ : 𝒟(qs)⁻ | rho_s <> ∅ } = 𝕌.

Proof.
    move => H.
    replace (rho_s <> ∅) with True => //.
    by apply propositional_extensionality.
Qed.