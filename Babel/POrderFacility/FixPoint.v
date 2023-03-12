(** * FixPoint.v *)

From Babel Require Import TerminalDogma 
                          ExtraDogma.Extensionality
                          SetFacility.

From Babel Require Export POrder.

From Babel Require Import Ranko.POrderCharacter.

From Coq Require Import Relations Arith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



(* the definition of a fixpoint *)
Definition fp (T : poset) (f : T -> T) (x : T) : Prop := f x = x.

(* set of fixpoints *)
Definition fp_s (T : poset) (f : T -> T) : 𝒫(T) := { x | fp f x }.

(* pre-fixpoint *)
Definition pre_fp (T : poset) (f : T -> T) (x : T) : Prop := x ⊑ f x.

(* pre-fixpoint set *)
Definition pre_fp_s (T : poset) (f : T -> T) : 𝒫(T) := { x | pre_fp f x }.

(* post-fixpoint *)
Definition post_fp (T : poset) (f : T -> T) (x : T) : Prop := f x ⊑ x.

(* post-fixpoint set *)
Definition post_fp_s (T : poset) (f : T -> T) : 𝒫(T) := { x | post_fp f x }.

(* fp_in_pre_fp : fp_s f ⊆ pre_fp_s f *)
Lemma fp_in_pre_fp (T : poset) : forall f : T -> T, fp_s f ⊆ pre_fp_s f.
Proof.
    rewrite /subset /fp_s /fp /pre_fp_s /pre_fp => //= f x ->.
    by reflexivity.
Qed.

(* fp_in_post_fp : fp_s f ⊆ post_fp_s f *)
Lemma fp_in_post_fp (T : poset) : forall f : T -> T, fp_s f ⊆ post_fp_s f.
Proof.
    have Hdual := @fp_in_pre_fp (T †po).
    by apply Hdual.
Qed.


(* a is the least fixpoint of f greater than x *)
Definition lfp_x (T : poset) (f : T -> T) (x a : T) := 
    least ({ y | y ∈ fp_s f /\ x ⊑ y }) a.

(* a is the least fixpoint of f *)
Definition lfp (T : poset) (f : T -> T) (a : T) := 
    least (fp_s f) a.
    
(* a is the greatest fixpoint of f smaller than x *)
Definition gfp_x (T : poset) (f : T -> T) (x a : T) := 
    largest ({ y | y ∈ fp_s f /\ y ⊑ x }) a.


(* a is the greatest fixpoint of f *)
Definition gfp (T : poset) (f : T -> T) (a : T) := 
    largest (fp_s f) a.



Lemma monofun_power_chain_mixin (T : cpo) (f : [T ↦ᵐ T]) (s : 𝒫(nat)): 
        Chain.mixin_of ((fun_power f) [<] s [>] (⊔ᶜᵖᵒ (set_em T))).
Proof.
    rewrite /Chain.mixin_of. porder_level.
    clear - f.
    case E: (x1 <= x3).
    - left.
Admitted.

Canonical monofun_power_chain (T : cpo) (f : [T ↦ᵐ T]) (s : 𝒫(nat)) : chain T
    := Chain ((fun_power f) [<] s [>] (⊔ᶜᵖᵒ (set_em T))) 
            (@monofun_power_chain_mixin T f s).


Definition KleeneFp (T : cpo) (f : [T ↦ T]) : T :=
    ⊔ᶜᵖᵒ ((fun_power f) [<] 𝕌 [>] (⊔ᶜᵖᵒ (set_em T))).

Axiom KleeneTheorem :
    forall (T : cpo) (f : [T ↦ T]), lfp f (KleeneFp f).