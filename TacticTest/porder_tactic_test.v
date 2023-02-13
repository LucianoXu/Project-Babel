(** porder_tactic_test.v *)

From Babel Require Import TerminalDogma.premises 
                          TerminalDogma.Extensionality.

From Babel Require Export POrderFacility.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma upper_bound_em (T : poset) : 
    forall a, @upper_bound T ∅ a.
Proof. POrder_level. Qed.

Lemma lower_bound_em (T : poset): 
    forall a, @lower_bound T ∅ a.
Proof. POrder_level. Qed.

(* ub_em : ub(∅) = X *)
Lemma ub_em (T : poset) : @ub T ∅ = 𝕌.
Proof. POrder_level. Qed. 

(* lb_em : lb(∅) {=} X *)
Lemma lb_em (T : poset) : @lb T ∅ = 𝕌.
Proof. POrder_level. Qed.

Lemma in_lb_ub (T : poset) (A : 𝒫(T)) : A ⊆ lb (ub A).
Proof. POrder_level. Qed.

Lemma in_ub_lb (T : poset) (A : 𝒫(T)) : A ⊆ ub (lb A).
Proof. POrder_level. Qed.

(** The first relation on poset can actually be "subposet" *)
Add Parametric Morphism {T : poset} : (@ub T)
    with signature (@supset T) ==> (@subset T) as ub_mor_sub.
Proof. POrder_level. Qed.


Add Parametric Morphism {T : poset} : (@lb T)
    with signature (@supset T) ==> (@subset T) as lb_mor_sub.
Proof. POrder_level. Qed.

(* lar_unique : largest element of A is unique *)
Lemma lar_unique (T : poset) (A : 𝒫(T)) (a b : T)
        (Ha_largest : largest A a) (Hb_largest : largest A b)
        : a = b.
Proof. POrder_level. Qed.

(* lea_unique : least element of A is unique *)
Lemma lea_unique (T : poset) (A : 𝒫(T)) (a b : T)
        (Ha_least : least A a) (Hb_least : least A b)
        : a = b.
Proof. POrder_level. Qed.

(* lar_in_ub : largest element is an upper bound *)
Lemma lar_in_ub (T : poset) (A : 𝒫(T)) (x : T) : 
    largest A x -> upper_bound A x.
Proof. POrder_level. Qed.

(* lea_in_ub : least element is a lower bound *)
Lemma lea_in_lb (T : poset) (A : 𝒫(T)) (x : T) :
    least A x -> lower_bound A x.
Proof. POrder_level. Qed.

Lemma uni_lar_upper_boundP (T : poset) (x : T) :
    largest 𝕌 x <-> upper_bound 𝕌 x.
Proof. POrder_level. Qed.

Lemma uni_lea_lower_boundP (T : poset) (x : T) :
    least 𝕌 x <-> lower_bound 𝕌 x.
Proof. POrder_level. Qed.

(* lar_subset : A ⊆ B -> largest (A) ⊑ largest (B) *)
Lemma lar_subset (T : poset) (A B: 𝒫(T))
    (a b : T) (HAinB : A ⊆ B)
    (Ha_lar : largest A a) (Hb_lar : largest B b) : a ⊑ b.
Proof. POrder_level. Qed.

(* lea_subset : A ⊆ B -> least (B) ⊑ least (A) *)
Lemma lea_subset (T : poset) (A B: 𝒫(T))
    (a b : T) (HAinB : A ⊆ B)
    (Ha_lea : least A a) (Hb_lea : least B b) : b ⊑ a.
Proof. POrder_level. Qed.
    
(** Another view of supremum (least upper bound). *)
Lemma lubP (T : poset) (A : 𝒫(T)) (x : T) :
    supremum A x <-> (forall' a ∈ A, a ⊑ x) 
                    /\ (forall u, (forall' a ∈ A, a ⊑ u) -> x ⊑ u).
Proof. POrder_level. Qed.

(** Another view of infimum (greatest lower bound). *)
Lemma glbP (T : poset) (A : 𝒫(T)) (x : T) :
    infimum A x <-> (forall' a ∈ A, x ⊑ a) 
                    /\ (forall u, (forall' a ∈ A, u ⊑ a) -> u ⊑ x).
Proof. POrder_level. Qed.

(* sup_unique : supremum is unique *)
Lemma sup_unique (T : poset) (A : 𝒫(T)) (a b : T)
    (Ha_sup : supremum A a) (Hb_sup : supremum A b)
    : a = b.
Proof. (* POrder_level. (time consuming) *) Abort.

(* inf_unique : infimum element of A is unique *)
Lemma inf_unique (T : poset) (A : 𝒫(T)) (a b : T)
    (Ha_inf : infimum A a) (Hb_inf : infimum A b)
    : a = b.
Proof. (* POrder_level. (time consuming) *) Abort.

(* lar_is_sup : x = largest A -> x = sup A *)
Lemma lar_is_sup (T : poset) : 
    forall (A : 𝒫(T)) (x : T), largest A x -> supremum A x.
Proof. POrder_level. Qed.

(* lea_is_inf : x = least A -> x = inf A *)
Lemma lea_is_inf (T : poset) : 
    forall (A : 𝒫(T)) (x : T), least A x -> infimum A x.
Proof. POrder_level. Qed.

(* sup_le_upper_bound : sup A ⊑ some upper bound of A *)
Lemma sup_le_upper_bound (T : poset) :
    forall (A : 𝒫(T)) (a b : T), 
        upper_bound A a -> supremum A b -> b ⊑ a.
Proof. POrder_level. Qed.

(* inf_ge_lower_bound : some lower bound of A ⊑ inf A*)
Lemma inf_ge_lower_bound (T : poset) :
    forall (A : 𝒫(T)) (a b : T), 
        lower_bound A a -> infimum A b -> a ⊑ b.
Proof. POrder_level. Qed.

(* le_sup : ∀ x ∈ A, x ⊑ ⊔A *)
Lemma le_sup (T : poset) (A : 𝒫(T)) (a : T):
    supremum A a -> forall' x ∈ A, x ⊑ a.
Proof. POrder_level. Qed.

(* ge_inf : ∀ x ∈ A, × ⊒ ⊓A *)
Lemma ge_inf (T : poset) (A : 𝒫(T)) (a : T):
    infimum A a -> forall' x ∈ A, a ⊑ x.
Proof. POrder_level. Qed.

Lemma sup_em_iff_lea_uni (T : poset) (a : T):
    supremum ∅ a <-> least 𝕌 a.
Proof. POrder_level. Qed.

Lemma inf_em_iff_lar_uni (T : poset) (a : T):
    infimum ∅ a <-> largest 𝕌 a.
Proof. POrder_level. Qed.

Lemma sup_uni_iff_lar_uni (T : poset) (a : T):
    supremum 𝕌 a <-> largest 𝕌 a.
Proof. POrder_level. Qed.

Lemma inf_uni_iff_lea_uni (T : poset) (a : T):
    infimum 𝕌 a <-> least 𝕌 a.
Proof. POrder_level. Qed.

(* sup_em : sup ∅ = least X *)
Lemma sup_em (T : poset) (a : T): 
    supremum ∅ a <-> least 𝕌 a.
Proof. POrder_level. Qed.

(* inf_em : sup ∅ {=} largest X *)
Lemma inf_em (T : poset) (a : T):
    infimum ∅ a <-> largest 𝕌 a.
Proof. POrder_level. Qed.

(* sup_in_is_lar : sup A ∈ A -> sup A = largest A *)
Lemma sup_in_is_lar (T : poset) (A : 𝒫(T)) (a : T)
    (Ha_sup : supremum A a) (Ha_in : a ∈ A) : largest A a.
Proof. POrder_level. Qed.

(* inf_in_is_lea : inf A ∈ A -> inf A = least A *)
Lemma inf_in_is_lea (T : poset) (A : 𝒫(T)) (a : T)
    (Ha_inf : infimum A a) (Ha_in : a ∈ A) : least A a.
Proof. POrder_level. Qed.

(* sup_subset : A ⊆ B -> sup A ⊑ sup B *)
Lemma sup_subset (T : poset) (A B: 𝒫(T))
    (a b : T) (HAinB : A ⊆ B)
    (Ha_sup : supremum A a) (Hb_sup : supremum B b) : a ⊑ b.
Proof. POrder_level. Qed.

(* inf_subset : A ⊆ B -> inf B ⊑ inf A *)
Lemma inf_subset (T : poset) (A B: 𝒫(T))
    (a b : T) (HAinB : A ⊆ B)
    (Ha_inf : infimum A a) (Hb_inf : infimum B b) : b ⊑ a.
Proof. POrder_level. Qed.


(* inf_ub_is_sup : the infimum of upper bounds of A is the supremum of A *)
Lemma inf_ub_is_sup (T : poset) (A : 𝒫(T)):
    forall a, infimum (ub A) a -> supremum A a.
Proof. POrder_level. Qed.

(* sup_lb_is_inf : the supremum of lower bounds of A is the infimum of A *)
Lemma sup_lb_is_inf (T : poset) (A : 𝒫(T)):
    forall a, supremum (lb A) a -> infimum A a.
Proof. POrder_level. Qed.














