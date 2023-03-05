(** porder_tactic_test.v *)

From Babel Require Import TerminalDogma 
                          ExtraDogma.Extensionality.

From Babel Require Export SetFacility POrderFacility.

From Babel Require Import Ranko.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma upper_bound_em (T : poset) : 
    forall a, @upper_bound T ∅ a.
Proof. ranko. Qed.

Lemma lower_bound_em (T : poset): 
    forall a, @lower_bound T ∅ a.
Proof. porder_level. Qed.

(* ub_em : ub(∅) = X *)
Lemma ub_em (T : poset) : @ub T ∅ = 𝕌.
Proof. porder_level. Qed. 

(* lb_em : lb(∅) {=} X *)
Lemma lb_em (T : poset) : @lb T ∅ = 𝕌.
Proof. porder_level. Qed.

Lemma in_lb_ub (T : poset) (A : 𝒫(T)) : A ⊆ lb (ub A).
Proof. porder_level. Qed.

Lemma in_ub_lb (T : poset) (A : 𝒫(T)) : A ⊆ ub (lb A).
Proof. porder_level. Qed.

(** The first relation on poset can actually be "subposet" *)
Add Parametric Morphism {T : poset} : (@ub T)
    with signature (@supset T) ==> (@subset T) as ub_mor_sub.
Proof. porder_level. Qed.


Add Parametric Morphism {T : poset} : (@lb T)
    with signature (@supset T) ==> (@subset T) as lb_mor_sub.
Proof. porder_level. Qed.

(* lar_unique : largest element of A is unique *)
Lemma lar_unique (T : poset) (A : 𝒫(T)) (a b : T)
        (Ha_largest : largest A a) (Hb_largest : largest A b)
        : a = b.
Proof. all_move_down. porder_level. Qed.

(* lea_unique : least element of A is unique *)
Lemma lea_unique (T : poset) (A : 𝒫(T)) (a b : T)
        (Ha_least : least A a) (Hb_least : least A b)
        : a = b.
Proof. all_move_down. porder_level. Qed.

(* lar_in_ub : largest element is an upper bound *)
Lemma lar_in_ub (T : poset) (A : 𝒫(T)) (x : T) : 
    largest A x -> upper_bound A x.
Proof. porder_level. Qed.

(* lea_in_ub : least element is a lower bound *)
Lemma lea_in_lb (T : poset) (A : 𝒫(T)) (x : T) :
    least A x -> lower_bound A x.
Proof. porder_level. Qed.

Lemma uni_lar_upper_boundP (T : poset) (x : T) :
    largest 𝕌 x <-> upper_bound 𝕌 x.
Proof. porder_level. Qed.

Lemma uni_lea_lower_boundP (T : poset) (x : T) :
    least 𝕌 x <-> lower_bound 𝕌 x.
Proof. porder_level. Qed.

(* lar_subset : A ⊆ B -> largest (A) ⊑ largest (B) *)
Lemma lar_subset (T : poset) (A B: 𝒫(T))
    (a b : T) (HAinB : A ⊆ B)
    (Ha_lar : largest A a) (Hb_lar : largest B b) : a ⊑ b.
Proof. all_move_down. porder_level. Qed.

(* lea_subset : A ⊆ B -> least (B) ⊑ least (A) *)
Lemma lea_subset (T : poset) (A B: 𝒫(T))
    (a b : T) (HAinB : A ⊆ B)
    (Ha_lea : least A a) (Hb_lea : least B b) : b ⊑ a.
Proof. all_move_down. porder_level. Qed.
    
(** Another view of supremum (least upper bound). *)
Lemma lubP (T : poset) (A : 𝒫(T)) (x : T) :
    supremum A x <-> (forall' a ∈ A, a ⊑ x) 
                    /\ (forall u, (forall' a ∈ A, a ⊑ u) -> x ⊑ u).
Proof. porder_level. Qed.

(** Another view of infimum (greatest lower bound). *)
Lemma glbP (T : poset) (A : 𝒫(T)) (x : T) :
    infimum A x <-> (forall' a ∈ A, x ⊑ a) 
                    /\ (forall u, (forall' a ∈ A, u ⊑ a) -> u ⊑ x).
Proof. porder_level. Qed.

(* sup_unique : supremum is unique *)
Lemma sup_unique (T : poset) (A : 𝒫(T)) (a b : T)
    (Ha_sup : supremum A a) (Hb_sup : supremum A b)
    : a = b.
Proof. (* porder_level. (time consuming) *) Abort.

(* inf_unique : infimum element of A is unique *)
Lemma inf_unique (T : poset) (A : 𝒫(T)) (a b : T)
    (Ha_inf : infimum A a) (Hb_inf : infimum A b)
    : a = b.
Proof. (* porder_level. (time consuming) *) Abort.

(* lar_is_sup : x = largest A -> x = sup A *)
Lemma lar_is_sup (T : poset) : 
    forall (A : 𝒫(T)) (x : T), largest A x -> supremum A x.
Proof. porder_level. Qed.

(* lea_is_inf : x = least A -> x = inf A *)
Lemma lea_is_inf (T : poset) : 
    forall (A : 𝒫(T)) (x : T), least A x -> infimum A x.
Proof. porder_level. Qed.

(* sup_le_upper_bound : sup A ⊑ some upper bound of A *)
Lemma sup_le_upper_bound (T : poset) :
    forall (A : 𝒫(T)) (a b : T), 
        upper_bound A a -> supremum A b -> b ⊑ a.
Proof. porder_level. Qed.

(* inf_ge_lower_bound : some lower bound of A ⊑ inf A*)
Lemma inf_ge_lower_bound (T : poset) :
    forall (A : 𝒫(T)) (a b : T), 
        lower_bound A a -> infimum A b -> a ⊑ b.
Proof. porder_level. Qed.

(* le_sup : ∀ x ∈ A, x ⊑ ⊔A *)
Lemma le_sup (T : poset) (A : 𝒫(T)) (a : T):
    supremum A a -> forall' x ∈ A, x ⊑ a.
Proof. porder_level. Qed.

(* ge_inf : ∀ x ∈ A, × ⊒ ⊓A *)
Lemma ge_inf (T : poset) (A : 𝒫(T)) (a : T):
    infimum A a -> forall' x ∈ A, a ⊑ x.
Proof. porder_level. Qed.

Lemma sup_em_iff_lea_uni (T : poset) (a : T):
    supremum ∅ a <-> least 𝕌 a.
Proof. porder_level. Qed.

Lemma inf_em_iff_lar_uni (T : poset) (a : T):
    infimum ∅ a <-> largest 𝕌 a.
Proof. porder_level. Qed.

Lemma sup_uni_iff_lar_uni (T : poset) (a : T):
    supremum 𝕌 a <-> largest 𝕌 a.
Proof. porder_level. Qed.

Lemma inf_uni_iff_lea_uni (T : poset) (a : T):
    infimum 𝕌 a <-> least 𝕌 a.
Proof. porder_level. Qed.

(* sup_em : sup ∅ = least X *)
Lemma sup_em (T : poset) (a : T): 
    supremum ∅ a <-> least 𝕌 a.
Proof. porder_level. Qed.

(* inf_em : sup ∅ {=} largest X *)
Lemma inf_em (T : poset) (a : T):
    infimum ∅ a <-> largest 𝕌 a.
Proof. porder_level. Qed.

(* sup_in_is_lar : sup A ∈ A -> sup A = largest A *)
Lemma sup_in_is_lar (T : poset) (A : 𝒫(T)) (a : T)
    (Ha_sup : supremum A a) (Ha_in : a ∈ A) : largest A a.
Proof. all_move_down. porder_level. Qed.

(* inf_in_is_lea : inf A ∈ A -> inf A = least A *)
Lemma inf_in_is_lea (T : poset) (A : 𝒫(T)) (a : T)
    (Ha_inf : infimum A a) (Ha_in : a ∈ A) : least A a.
Proof. all_move_down. porder_level. Qed.

(* sup_subset : A ⊆ B -> sup A ⊑ sup B *)
Lemma sup_subset (T : poset) (A B: 𝒫(T))
    (a b : T) (HAinB : A ⊆ B)
    (Ha_sup : supremum A a) (Hb_sup : supremum B b) : a ⊑ b.
Proof. all_move_down. porder_level. Qed.

(* inf_subset : A ⊆ B -> inf B ⊑ inf A *)
Lemma inf_subset (T : poset) (A B: 𝒫(T))
    (a b : T) (HAinB : A ⊆ B)
    (Ha_inf : infimum A a) (Hb_inf : infimum B b) : b ⊑ a.
Proof. all_move_down. porder_level. Qed.


(* inf_ub_is_sup : the infimum of upper bounds of A is the supremum of A *)
Lemma inf_ub_is_sup (T : poset) (A : 𝒫(T)):
    forall a, infimum (ub A) a -> supremum A a.
Proof. porder_level. Qed.

(* sup_lb_is_inf : the supremum of lower bounds of A is the infimum of A *)
Lemma sup_lb_is_inf (T : poset) (A : 𝒫(T)):
    forall a, supremum (lb A) a -> infimum A a.
Proof. porder_level. Qed.


Lemma CPO_bottom (C : cpo) : least 𝕌 (⊔ᶜᵖᵒ (set_em C)).
Proof. porder_level. Qed.


Module SubsetOrder.
Section OrderDef.

(** inclusion order (subset) *)
Definition poset_mixin (T : Type): Poset.mixin_of 𝒫(T) :=
    Poset.Mixin {|
        ord_refl := subset_refl;
        ord_trans := subset_trans;
        ord_antisym := subset_asymm;
    |}.

Canonical poset_type (T : Type) := Poset 𝒫(T) (poset_mixin T).


(** Directly construction of complete lattice. *)
Definition clattice_essence (T : Type) : CLattice.essence_of 𝒫(T).
Proof.
    constructor.
    refine (@CLattice.JoinEssence _ big_union _).
    porder_level.
    refine (@CLattice.MeetEssence _ big_itsct _).
    porder_level.
Defined.

Definition AUX_clattice_type (T : Type) := CLattice 𝒫(T) 
            (CLattice.essence_to_mixin (clattice_essence T)).


Definition lattice_mixin (T : Type) : Lattice.mixin_of (Poset.class 𝒫(T)) :=
    Lattice.class [lattice of AUX_clattice_type T].

Canonical lattice_type (T : Type) := Lattice 𝒫(T) (lattice_mixin T).

Definition clattice_mixin (T : Type) : CLattice.mixin_of (Lattice.class 𝒫(T)) :=
    CLattice.class [clattice of AUX_clattice_type T].

Canonical clattice_type (T : Type) := CLattice 𝒫(T) (clattice_mixin T).

Canonical cpo_type (T : Type) : cpo := CPO 𝒫(T) (CPO.class [cpo of [clattice of 𝒫(T)]]).

    

(*########################################################################*)
(** prove that certaion operators are continuous *)

(** monotonicity of mapR *)
Definition mapR_monotonicMixin {X Y: Type} (f : X -> Y) : 
    MonotonicFun.mixin_of (f [<]).
Proof. porder_level. Qed.

Canonical mapR_monotonicType {X Y: Type} (f : X -> Y) :=
    MonotonicFun (f [<]) (@mapR_monotonicMixin _ _ f).

(** continuity of mapR *)
Definition mapR_continuousMixin {X Y: Type} (f : X -> Y) :
    ContinuousFun.mixin_of (MonotonicFun.class (f [<])).
Proof. porder_level. Qed.

Canonical mapR_continuousType {X Y: Type} (f : X -> Y) :=
    ContinuousFun (f[<]) (@mapR_continuousMixin _ _ f).

(** monotonicity of bigU *)

Definition bigU_monotonicMixin {X : Type} :
    MonotonicFun.mixin_of (@big_union X).
Proof. porder_level. Qed.

Canonical bigU_monotonicType (X : Type) :=
    MonotonicFun big_union (@bigU_monotonicMixin X).


(** continuity of bigU *)

Definition bigU_continuousMixin {X : Type} :
    ContinuousFun.mixin_of (MonotonicFun.class (@big_union X)).
Proof. porder_level. Qed.

Canonical bigU_continuousType {X : Type} :=
    ContinuousFun big_union (@bigU_continuousMixin X).

End OrderDef.

End SubsetOrder.
    












