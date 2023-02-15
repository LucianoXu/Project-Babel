(** * POrderBool.v : Partial order of bool *)


From Babel Require Import TerminalDogma 
                          ExtraDogma.Extensionality
                          ExtraDogma.IotaDescription.


From Coq Require Import Relations Classical Arith.

From Babel Require Export POrderFacility.

From Babel.Ranko Require Import LogicCharacter SetCharacter.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module BoolOrder.
Open Scope NSet_scope.

Definition impl : relation bool := 
    fun x y => x -> y.
#[local] Hint Unfold impl : magic_book.

Lemma impl_refl : reflexive _ impl.
Proof. by rewrite /reflexive /impl. Qed.

Lemma impl_trans : transitive _ impl.
Proof. 
    rewrite /transitive /impl => x y z Hxy Hyz Hx.
    by apply /Hyz /Hxy.
Qed.

Lemma impl_antisym : antisymmetric _ impl.
Proof.
    rewrite /antisymmetric /impl. rewrite /is_true.
    case; case => //= H1 H2. 
    symmetry. by apply H1.
    by apply H2.
Qed.

Definition poset_mixin : Poset.mixin_of bool :=
    Poset.Mixin {|
        ord_refl := impl_refl;
        ord_trans := impl_trans;
        ord_antisym := impl_antisym
    |}.

Canonical poset_type := Poset bool poset_mixin.


(** join *)
Definition pred_join (A : 𝒫(bool)) (b : bool) : Prop :=
    (true ∈ A) <-> b.
#[local] Hint Unfold pred_join : magic_book.

Lemma pred_join_iotaMixin (A : 𝒫(bool)) : Iota.mixin_of (pred_join A).
Proof. rewrite /Iota.mixin_of /pred_join /unique => //=.
    case (classic (true ∈ A)). 
    
    exists true. set_level.
    symmetry. by apply H0.

    exists false. set_level.
    rewrite H0 in H. by destruct x' => //=.
Qed.

Canonical pred_join_iota (A : 𝒫(bool)) := 
    Iota (pred_join A) (pred_join_iotaMixin A).

Definition clattice_join_essence : CLattice.join_essence_of bool.
Proof. 
    refine (@CLattice.JoinEssence _ (fun A => ι(pred_join A)) _) => A.

    rewrite /supremum /least /ub => //=. split.
    rewrite /upper_bound => a Hain Ha //=.
    apply (iota_spec (pred_join A)). by rewrite -Ha.

    rewrite /upper_bound //= => b. rewrite /impl => Ha.
    replace (is_true (ι (pred_join_iota A))) with (true ∈ A).
    2: apply propositional_extensionality; apply (iota_spec (pred_join A)).
    move => HA. by apply (Ha true).
Defined.

Definition AUX_clattice_type := 
    CLattice bool (CLattice.join_essence_to_mixin (clattice_join_essence)).

Definition lattice_mixin : Lattice.mixin_of (Poset.class bool) :=
    Lattice.class [lattice of AUX_clattice_type].

Canonical lattice_type := Lattice bool lattice_mixin.

Definition clattice_mixin : CLattice.mixin_of (Lattice.class bool) :=
    CLattice.class [clattice of AUX_clattice_type].

Canonical clattice_type := CLattice bool clattice_mixin.

Canonical cpo_type : cpo := CPO bool (CPO.class [cpo of [clattice of bool]]).

Module CanonicalStruct.

Canonical poset_type.
Canonical lattice_type.
Canonical cpo_type.
Canonical clattice_type.
#[export] Hint Unfold impl : magic_book.
#[export] Hint Unfold pred_join : magic_book.

End CanonicalStruct.

End BoolOrder.
