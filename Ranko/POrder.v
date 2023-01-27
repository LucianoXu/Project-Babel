(** * POrder.v : Library for partial orders. *)


From Ranko Require Import TerminalDogma.premises 
                          TerminalDogma.Extensionality
                          NaiveSet.

From Coq Require Import Relations Classical.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** Reserved Notations *)
Declare Scope POrder_scope.
Open Scope POrder_scope.


Reserved Notation " a ⊑ ( p ) b " 
    (at level 60, p at next level, format " a  ⊑ ( p )  b ").
Reserved Notation " a ⊑ b " (at level 60).
Reserved Notation " a ⋢ ( p ) b " 
    (at level 60, p at next level, format " a  ⋢ ( p )  b ").
Reserved Notation " a ⋢ b " (at level 60).

Reserved Notation " f '†r' " (at level 20).
Reserved Notation " P '†po' " (at level 10).

(*
Reserved Notation " L '†L' " (at level 10).
Reserved Notation " cL '†cL' " (at level 10).
*)

Reserved Notation "⊔ A " (at level 40).
Reserved Notation "'cpo⊔' A" (at level 40).


(** get the dual relation *)
Definition dualRel {T : Type} (R1 : relation T) : relation T :=
    fun a b => R1 b a.
Notation " f '†r' " := (dualRel f) : NSet_scope.


Lemma dual_dualRel {T : Type} (R1 : relation T) :
    (R1 †r) †r = R1.
Proof. rewrite /dualRel. by apply functional_extensionality. Qed.




(** Poset, partial-order set.
    Here we consider every order relation to be a poset.

    This definition copies the design of [eqType] in MathComp.
    For [relation], we use the definition in [Coq.Relations].
    For [order], see [Coq.Relation_Definitions] 

    Here is a subtle question: whether the parameter [T] should be a Coq type
    or a [powerset] term. Here we try to combine the both scenarios. For the
    that [T] is a [powerset] term, more tools about sets can be applied.
    *)

Module Poset.

Structure mixin_of T := Mixin { op : relation T; ord : order T op }.
Notation class_of := mixin_of (only parsing).

Section ClassDef.

Structure type := Pack { sort; _ : class_of sort }.

Definition class (cT : type) := 
    let: Pack _ c := cT return class_of (sort cT) in c.

End ClassDef.


Module Exports.

Coercion sort : type >-> Sortclass.
Notation poset := type.
Notation posetMixin := Mixin.
Notation Poset T m := (@Pack T m).

(** Here we conduct the explicit conversion by [T : Type], to allow the
    downgrade of more complex structures, such as cpo and lattices. *)
Notation "[ 'poset' 'of' T ]" := ([get r | sort r ~ T : Type ])
  (at level 0, format "[ 'poset'  'of'  T ]") : POrder_scope.
Notation "[ 'posetMixin' 'of' T ]" := (@class [ poset of T ])
  (at level 0, format "[ 'posetMixin'  'of'  T ]") : POrder_scope.


Definition poset_op T := Poset.op (Poset.class T).
Definition poset_refl (T : type) := ord_refl _ _ (ord (class T)).
Definition poset_trans (T : type) := ord_trans _ _ (ord (class T)).
Definition poset_antisym (T : type) := ord_antisym _ _ (ord (class T)).

Notation " a ⊑ ( p ) b " := (Poset.op (Poset.class p) a b) 
    (only parsing): POrder_scope.
Notation " a ⊑ b " := (Poset.op (Poset.class _) a b) : POrder_scope.

Notation " a ⋢ ( p ) b " := (~ a ⊑ (p) b) 
    (only parsing): POrder_scope.
Notation " a ⋢ b " := (~ a ⊑ b) : POrder_scope.


End Exports.

End Poset.
Export Poset.Exports.

Lemma poset_order (po : poset) : order po (@poset_op po).
Proof. destruct po. destruct m => //=. Qed.


(** dual poset *)

Lemma dual_order {T : Type} (R : relation T) : order _ R -> order _ (R †r).
Proof. rewrite /dualRel => [H]. constructor.
    by apply H. 
    rewrite /transitive => x y z Hxy Hyz. move: Hyz Hxy. by apply H.
    rewrite /antisymmetric => x y Hxy Hyx. by apply H.
Qed.

(** get the dual poset *)
Definition dualPoset (po : poset) : poset :=
    Poset po (posetMixin (dual_order (poset_order po))).
Notation " P '†po' " := (dualPoset P): POrder_scope.



(*###################################################*)
(** ** upper sets and lower sets *)

(* A is an upper_set *)
Definition upper_set (T : poset) (A : 𝒫(T)) : Prop :=
    forall a b, a ∈ A -> a ⊑ b -> b ∈ A.

(* A is an lower_set *)
Definition lower_set (T : poset) (A : 𝒫(T)) : Prop :=
    forall a b, a ∈ A -> b ⊑ a -> b ∈ A.
    
(* the upper set of A *)
Definition up_s (T : poset) (A : 𝒫(T)) := 
    { x | exists' a ∈ A, a ⊑ x }.

(* the lower set of A *)
Definition low_s (T : poset) (A : 𝒫(T)) := 
    { x | exists' a ∈ A, x ⊑ a }.




(*###################################################*)
(** ** upper bound and lower bound *)

(* x is an upper bound of A *)
Definition upper_bound (T : poset) (A : 𝒫(T)) (x : T) :=
    forall' a ∈ A, a ⊑ x.
    
(* x is an lower bound of A *)
Definition lower_bound (T : poset) (A : 𝒫(T)) (x : T) :=
    forall' a ∈ A, x ⊑ a.

(* upper_bound_em : any a is an upper bound of ∅ *)
Lemma upper_bound_em (T : poset) : 
    forall a, @upper_bound T ∅ a.
Proof. rewrite /upper_bound => a b []. Qed.


(* lower_bound_em : any a is an lower bound of ∅ *)
Lemma lower_bound_em (T : poset): 
    forall a, @lower_bound T ∅ a.
Proof.
    have Hdual := @upper_bound_em (T †po).
    by apply Hdual.
Qed.


(* set of all upper bounds *)
Definition ub (T : poset) (A : 𝒫(T)) : 𝒫(T) := 
    { x | upper_bound A x }.

(* set of all lower bounds *)
Definition lb (T : poset) (A : 𝒫(T)) : 𝒫(T) := 
    { x | lower_bound A x}.


(* ub_em : ub(∅) = X *)
Lemma ub_em (T : poset) : @ub T ∅ = 𝕌.
Proof.
    rewrite /ub. apply /seteqP => x //=. split =>//. 
    move => _. by apply upper_bound_em.
Qed. 

(* lb_em : lb(∅) {=} X *)
Lemma lb_em (T : poset) : @lb T ∅ = 𝕌.
Proof.
    have Hdual := ub_em (T †po).
    by apply Hdual.
Qed. 


(* in_lb_ub : a ∈ A -> a ∈ lb (ub (A)) *)
Lemma in_lb_ub (T : poset) (A : 𝒫(T)) : A ⊆ lb (ub A).
Proof.
Abort.

(* in_ub_lb : a ∈ A -> a ∈ ub (lb (A)) *)
Lemma in_ub_lb (T : poset) (A : 𝒫(T)) : A ⊆ ub (lb A).
Proof.
Abort.


(** The first relation on poset can actually be "subposet" *)
Add Parametric Morphism {T : poset} : (@ub T)
    with signature (@supset T) ==> (@subset T) as ub_mor_sub.
Proof.
    rewrite /ub /upper_bound /subset => //= A B HBinA x Hxin.
    move => a Hain. by apply /Hxin /HBinA.
Qed.

Add Parametric Morphism {T : poset} : (@lb T)
    with signature (@supset T) ==> (@subset T) as lb_mor_sub.
Proof.
    have Hdual := @ub_mor_sub (T †po).
    by apply Hdual.
Qed.



(*###################################################*)
(** ** maximum and minimum *)

(** may be to build it as record is better *)

(* x is maximal in A *)
Definition maximal (T : poset) (A : 𝒫(T)) (x : T) :=
    x ∈ A /\ forall' a ∈ A, (a <> x -> x ⋢ a).

(* x is minimal in A *)
Definition minimal (T : poset) (A : 𝒫(T)) (x : T) :=
    x ∈ A /\ forall' a ∈ A, (a <> x -> a ⋢ x).



(*###################################################*)
(** ** largest and least *)

(** maybe we can rewrite largest and least with epsilon operator? *)

(* x is largest in A *)
Definition largest (T : poset) (A : 𝒫(T)) (x : T) :=
    x ∈ A /\ forall' a ∈ A, a ⊑ x.

(* x is least in A *)
Definition least (T : poset) (A : 𝒫(T)) (x : T) :=
    x ∈ A /\ forall' a ∈ A, x ⊑ a.

(*
(* dual_lar_is_lea : x = largest A -> x = least A (in the dual poset) *)
Lemma dual_lar_is_lea (po : poset T) (A : set T) (x : T)
    : largest po A x -> least (po †po) A x.
Proof. auto. Qed.

(* dual_lea_is_lar : x = least A -> x = largest A (in the dual poset) *)
Lemma dual_lea_is_lar (po : poset T) (A : set T) (x : T)
    : least po A x -> largest (po †po) A x.
Proof. auto. Qed.
*)


(* lar_unique : largest element of A is unique *)
Lemma lar_unique (T : poset) (A : 𝒫(T)) (a b : T)
        (Ha_largest : largest A a) (Hb_largest : largest A b)
        : a = b.
Proof.
    apply poset_antisym. 
    apply Hb_largest. by apply Ha_largest.
    apply Ha_largest. by apply Hb_largest.
Qed.

(* lea_unique : least element of A is unique *)
Lemma lea_unique (T : poset) (A : 𝒫(T)) (a b : T)
        (Ha_least : least A a) (Hb_least : least A b)
        : a = b.
Proof.    
    apply poset_antisym. 
    apply Ha_least. by apply Hb_least.
    apply Hb_least. by apply Ha_least.
Qed.


(* lar_in_ub : largest element is an upper bound *)
Lemma lar_in_ub (T : poset) (A : 𝒫(T)) (x : T) : 
    largest A x -> upper_bound A x.
Proof. rewrite /upper_bound /largest.
    move => H. by apply H.
Qed.

(* lea_in_ub : least element is a lower bound *)
Lemma lea_in_lb (T : poset) (A : 𝒫(T)) (x : T) :
    least A x -> lower_bound A x.
Proof.
    have Hdual := @lar_in_ub (T †po).
    by apply Hdual.
Qed.

Lemma uni_lar_upper_boundP (T : poset) (x : T) :
    largest 𝕌 x <-> upper_bound 𝕌 x.
Proof. split. by apply lar_in_ub.
    rewrite /upper_bound /largest => H. by split.
Qed.

Lemma uni_lea_lower_boundP (T : poset) (x : T) :
    least 𝕌 x <-> lower_bound 𝕌 x.
Proof.
    have Hdual := @uni_lar_upper_boundP (T †po).
    by apply Hdual.
Qed.


(* lar_subset : A ⊆ B -> largest (A) ⊑ largest (B) *)
Lemma lar_subset (T : poset) (A B: 𝒫(T))
    (a b : T) (HAinB : A ⊆ B)
    (Ha_lar : largest A a) (Hb_lar : largest B b) : a ⊑ b.
Proof. apply Hb_lar. apply HAinB. by apply Ha_lar. Qed.

(* lea_subset : A ⊆ B -> least (B) ⊑ least (A) *)
Lemma lea_subset (T : poset) (A B: 𝒫(T))
    (a b : T) (HAinB : A ⊆ B)
    (Ha_lea : least A a) (Hb_lea : least B b) : b ⊑ a.
Proof.
    have Hdual := @lar_subset (T †po) A B a b.
    by apply Hdual.
Qed.





(*###################################################*)
(** ** supremum and infimum *)

(** x is the supremum of A. Here supremum is presented as a proposition,
    because the supremum does not always exists. *)
Definition supremum (T : poset) (A : 𝒫(T)) (x : T) := least (ub A) x.

(** x is the infimum of A *)
Definition infimum (T : poset) (A : 𝒫(T)) (x : T) := largest (lb A) x.

(** Another view of supremum (least upper bound). *)
Lemma lubP (T : poset) (A : 𝒫(T)) (x : T) :
    supremum A x <-> (forall' a ∈ A, a ⊑ x) 
                    /\ (forall u, (forall' a ∈ A, a ⊑ u) -> x ⊑ u).
Proof. by rewrite /supremum /least /ub //=. Qed.

(** Another view of infimum (greatest lower bound). *)
Lemma glbP (T : poset) (A : 𝒫(T)) (x : T) :
    infimum A x <-> (forall' a ∈ A, x ⊑ a) 
                    /\ (forall u, (forall' a ∈ A, u ⊑ a) -> u ⊑ x).
Proof.
    have Hdual := @lubP (T †po).
    by apply Hdual.
Qed.

(* sup_unique : supremum is unique *)
Lemma sup_unique (T : poset) (A : 𝒫(T)) (a b : T)
    (Ha_sup : supremum A a) (Hb_sup : supremum A b)
    : a = b.
Proof. by apply (lea_unique Ha_sup Hb_sup). Qed.

(* inf_unique : infimum element of A is unique *)
Lemma inf_unique (T : poset) (A : 𝒫(T)) (a b : T)
    (Ha_inf : infimum A a) (Hb_inf : infimum A b)
    : a = b.
Proof. by apply (lar_unique Ha_inf Hb_inf). Qed.


(* lar_is_sup : x = largest A -> x = sup A *)
Lemma lar_is_sup (T : poset) : 
    forall (A : 𝒫(T)) (x : T), largest A x -> supremum A x.
Proof.
    rewrite /supremum /least => A x [] HxinA H. split => //.
    rewrite /ub => //= b Hb. by apply Hb. 
Qed.

(* lea_is_inf : x = least A -> x = inf A *)
Lemma lea_is_inf (T : poset) : 
    forall (A : 𝒫(T)) (x : T), least A x -> infimum A x.
Proof.
    have Hdual := @lar_is_sup (T †po).
    by apply Hdual.
Qed.

(* sup_le_upper_bound : sup A ⊑ some upper bound of A *)
Lemma sup_le_upper_bound (T : poset) :
    forall (A : 𝒫(T)) (a b : T), 
        upper_bound A a -> supremum A b -> b ⊑ a.
Proof.
    intros A a b Hub Hsup.
    apply Hsup. by apply Hub.
Qed.


(* inf_ge_lower_bound : some lower bound of A ⊑ inf A*)
Lemma inf_ge_lower_bound (T : poset) :
    forall (A : 𝒫(T)) (a b : T), 
        lower_bound A a -> infimum A b -> a ⊑ b.
Proof.
    have Hdual := @sup_le_upper_bound (T †po).
    by apply Hdual.
Qed.
    
(* le_sup : ∀ x ∈ A, x ⊑ ⊔A *)
Lemma le_sup (T : poset) (A : 𝒫(T)) (a : T):
    supremum A a -> forall' x ∈ A, x ⊑ a.
Proof. intros Hsup x HxinA. by apply Hsup. Qed.

(* ge_inf : ∀ x ∈ A, × ⊒ ⊓A *)
Lemma ge_inf (T : poset) (A : 𝒫(T)) (a : T):
    infimum A a -> forall' x ∈ A, a ⊑ x.
Proof.
    have Hdual := @le_sup (T †po).
    by apply Hdual.
Qed.

Lemma sup_em_iff_lea_uni (T : poset) (a : T):
    supremum ∅ a <-> least 𝕌 a.
Proof. rewrite /supremum. by rewrite ub_em. Qed.

Lemma inf_em_iff_lar_uni (T : poset) (a : T):
    infimum ∅ a <-> largest 𝕌 a.
Proof. 
    have Hdual := @sup_em_iff_lea_uni (T †po).
    by apply Hdual.
Qed.

Lemma sup_uni_iff_lar_uni (T : poset) (a : T):
    supremum 𝕌 a <-> largest 𝕌 a.
Proof. split.
    rewrite /supremum /least /ub => //=.
    move => [] H _. by apply uni_lar_upper_boundP.
    by apply lar_is_sup.
Qed.

Lemma inf_uni_iff_lea_uni (T : poset) (a : T):
    infimum 𝕌 a <-> least 𝕌 a.
Proof. 
    have Hdual := @sup_uni_iff_lar_uni (T †po).
    by apply Hdual.
Qed.

(* sup_em : sup ∅ = least X *)
Lemma sup_em (T : poset) (a : T): 
    supremum ∅ a <-> least 𝕌 a.
Proof.
Abort.

(* inf_em : sup ∅ {=} largest X *)
Lemma inf_em (T : poset) (a : T):
    infimum ∅ a <-> largest 𝕌 a.
Proof.
Abort.

(* sup_in_is_lar : sup A ∈ A -> sup A = largest A *)
Lemma sup_in_is_lar (T : poset) (A : 𝒫(T)) (a : T)
    (Ha_sup : supremum A a) (Ha_in : a ∈ A) : largest A a.
Proof.
Abort.

(* inf_in_is_lea : inf A ∈ A -> inf A = least A *)
Lemma inf_in_is_lea (T : poset) (A : 𝒫(T)) (a : T)
    (Ha_inf : infimum A a) (Ha_in : a ∈ A) : least A a.
Proof.
Abort.

(* sup_subset : A ⊆ B -> sup A ⊑ sup B *)
Lemma sup_subset (T : poset) (A B: 𝒫(T))
    (a b : T) (HAinB : A ⊆ B)
    (Ha_sup : supremum A a) (Hb_sup : supremum B b) : a ⊑ b.
Proof.
    have Hubin : ub B ⊆ ub A. by apply ub_mor_sub.
    by apply (lea_subset Hubin). 
Qed.

(* inf_subset : A ⊆ B -> inf B ⊑ inf A *)
Lemma inf_subset (T : poset) (A B: 𝒫(T))
    (a b : T) (HAinB : A ⊆ B)
    (Ha_inf : infimum A a) (Hb_inf : infimum B b) : b ⊑ a.
Proof.
    have Hdual := @sup_subset (T †po) A B a b.
    by apply Hdual.
Qed.


(* inf_ub_is_sup : the infimum of upper bounds of A is the supremum of A *)
Lemma inf_ub_is_sup (T : poset) (A : 𝒫(T)):
    forall a, infimum (ub A) a -> supremum A a.
Proof.
Abort.

(* sup_lb_is_inf : the supremum of lower bounds of A is the infimum of A *)
Lemma sup_lb_is_inf (T : poset) (A : 𝒫(T)):
    forall a, supremum (lb A) a -> infimum A a.
Proof.
Abort.




(*###################################################*)
(** ** chain and CPO *)

Module Chain.

Definition mixin_of (T : poset) (A : 𝒫(T)) :=
    forall' x ∈ A, forall' y ∈ A, (x ⊑ y \/ y ⊑ x).
Notation class_of := mixin_of (only parsing).

Section ClassDef.

Structure type (T : poset) := Pack {
    set : 𝒫(T);
    _ : class_of set;
}.

Definition class (T : poset) (cT : type T) := 
    let: Pack _ c := cT return class_of (set cT) in c.

End ClassDef.

Module Exports.
Coercion set : type >-> powerset.
Arguments class [T] cT.
Notation chain := type.
Notation Chain s m := (@Pack _ s m).
Notation "[ 'chain' 'of' A ]" := ([get c | set c ~ A : 𝒫(_)])
  (at level 0, format "[ 'chain'  'of'  A ]"): POrder_scope.
Notation "[ 'chainMixin' 'of' A ]" := (@class _ [ chain of A ])
  (at level 0, format "[ 'chainMixin'  'of'  A ]"): POrder_scope.
End Exports.

End Chain.
Export Chain.Exports.

(* em_is_chain: empty set is a chain *)
Lemma em_chain_mixin (T : poset) : @Chain.class_of T ∅.
Proof. rewrite /Chain.mixin_of => ? []. Qed.

Canonical em_is_chain (T : poset) := Chain ∅ (@em_chain_mixin T).



(** CPO - existence version 
    The join operator is not necessary. This class only requires the existence
    of supremums. *)
Module CPO_ex.

Definition mixin_of (T : poset) := forall A : chain T, exists y, supremum A y.
Notation class_of := mixin_of (only parsing).

Section ClassDef.

Structure type := Pack {
    sort : poset;
    _ : class_of sort;
}.

Definition class cT := 
    let: Pack _ c := cT return class_of (sort cT) in c.

End ClassDef.

Module Exports.
Coercion sort : type >-> poset.
Notation cpo_ex := type.
Notation CPO_ex t m := (@Pack t m).
Notation "[ 'cpo_ex' 'of' T ]" := ([get c | sort c ~ [poset of T] ])
  (at level 0, format "[ 'cpo_ex'  'of'  T ]") : POrder_scope.
Notation "[ 'cpo_exMixin' 'of' T ]" := (@class [ cpo_ex of T ])
  (at level 0, format "[ 'cpo_exMixin'  'of'  T ]") : POrder_scope.

End Exports.

End CPO_ex.
Export CPO_ex.Exports.



(** **** CPO_ex_bottom: every CPO has the least element *)
Lemma CPO_ex_bottom (C : cpo_ex) : exists x : C, least 𝕌 x.
Proof.
    have Hbot := CPO_ex.class [chain of (set_em C)]. simpl in Hbot.
    destruct Hbot as [y Hy].
    exists y. by apply sup_em_iff_lea_uni.
Qed.



(** CPO (with the join operator) *)
Module CPO.

Structure mixin_of (T : poset) := Mixin {
    join_op : chain T -> T;
    join_prop : forall A : chain T, supremum A (join_op A);
}.
Notation class_of := mixin_of (only parsing).

Section ClassDef.

Structure type := Pack {
    sort : poset;
    _ : class_of sort;
}.

Definition class cT := 
    let: Pack _ c := cT return class_of (sort cT) in c.

End ClassDef.


Notation join_of A := (join_op (@class _) [chain of A : 𝒫(_)]).

Module Exports.
Coercion sort : type >-> poset.
Notation cpo := type.
Notation cpoMixin := Mixin.
Notation CPO t m := (@Pack t m).
Notation "[ 'cpo' 'of' T ]" := ([get c | sort c ~ [poset of T] ])
    (at level 0, format "[ 'cpo'  'of'  T ]") : POrder_scope.
Notation "[ 'cpoMixin' 'of' T ]" := (@class [ cpo_ex of T ])
    (at level 0, format "[ 'cpoMixin'  'of'  T ]") : POrder_scope.
Notation "'cpo⊔' A" := (join_op (@class _) [chain of A]) : 
    POrder_scope.
Notation "⊔ A " := (join_op (@class _) A) 
    (only printing) : POrder_scope.
End Exports.

End CPO.
Export CPO.Exports.


(** **** CPO_bottom: every CPO has the least element *)
Lemma CPO_bottom (C : cpo) : least 𝕌 (cpo⊔ (set_em C)).
Proof.
    apply sup_em_iff_lea_uni.
    have Hbot := CPO.join_prop (CPO.class C).
    by apply Hbot.
Qed.

(*######################################################################*)
(** lattice *)

Module Lattice_ex.

(* po is a lattice *)
Structure mixin_of (T : cpo_ex) := Mixin {
    inf_ex : forall x y : T, (exists i, infimum ({{x, y}}) i);
    sup_ex : forall x y : T, (exists s, supremum ({{x, y}}) s);
}.
Notation class_of := mixin_of (only parsing).

Section ClassDef.

(* lattice (computable) *)
Structure type := Pack {
    sort : cpo_ex;
    _ : class_of sort;
}.

Definition class cT := let: Pack _ c := cT return class_of (sort cT) in c.

End ClassDef.

Module Exports.
Coercion sort : type >-> cpo_ex.
Notation latt_ex := type.
Notation Latt_exMixin := Mixin.
Notation Latt_ex t m := (@Pack t m).

Notation "[ 'latt_ex' 'of' T ]" := ([get r | sort r ~ [cpo_ex of T] ])
  (at level 0, format "[ 'latt_ex'  'of'  T ]") : POrder_scope.
Notation "[ 'latt_exMixin' 'of' T ]" := (@class [latt_ex of T])
  (at level 0, format "[ 'latt_exMixin'  'of'  T ]") : POrder_scope.
End Exports.

End Lattice_ex.
Export Lattice_ex.Exports.


(*###################################################*)
(** ** complete lattice *)

(**
    Notice the difference between 
        "exists a complete join operator"
    and
        "for all subset, the supremum exists".


    Ordinary textbooks define a complete lattice to be the tuple 
    
        CL := (set, rel, join, meet, top, bot)

    containing the (complete) join and meet operator. But this is not always 
    possible in Coq, because not all join or meet operators are calculable, 
    and uncalculable functions cannot be defined in Coq.

    This difference corresponds to the different views of description.
*)


Module CLattice_ex.

Structure mixin_of (T : latt_ex) := Mixin {
    inf_ex : forall A : 𝒫(T), exists i, infimum A i;
    sup_ex : forall A : 𝒫(T), exists s, supremum A s;
}.
Notation class_of := mixin_of (only parsing).

Section ClassDef.

Structure type := Pack {
    sort : latt_ex;
    _ : class_of sort
}.

Definition class cT := let: Pack _ c := cT return class_of (sort cT) in c.

End ClassDef.

Module Exports.
Coercion sort : type >-> latt_ex.
Notation clatt_ex := type.
Notation Clatt_exMixin := Mixin.
Notation Clatt_ex T m := (@Pack T m).

Notation "[ 'clatt_ex' 'of' T ]" := ([get r | sort r ~ [ latt_ex of T ]])
    (at level 0, format "[ 'clatt_ex'  'of'  T ]") : POrder_scope.
Notation "[ 'clatt_exMixin' 'of' T ]" := (@class [clatt_ex of T])
    (at level 0, format "[ 'clatt_exMixin'  'of'  T ]") : POrder_scope.
End Exports.

End CLattice_ex.
Export CLattice_ex.Exports.




(*###################################################*)
(** ** function in poset *)

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
    by apply poset_refl.
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

(** monotonic *)
Module MonotonicFun.

Definition mixin_of (T T' : poset) (f : T -> T') :=
    forall x y : T, x ⊑ y -> f x ⊑ f y.
Notation class_of := mixin_of (only parsing).

Section ClassDef.

Structure type (T T' : poset) := Pack {
    obj : T -> T';
    _ : class_of obj;
}.

Definition class T T' (cT : type T T') := 
    let: Pack _ c := cT return class_of (obj cT) in c.

End ClassDef.

Module Exports.
Coercion obj : type >-> Funclass.
Notation monotonicfun := type.

(** The special notation for monotonic function. *)
Notation "[ A ↦ᵐ B ]" := (type [poset of A] [poset of B]) 
    (at level 0, format "[ A  ↦ᵐ  B ]"): POrder_scope.

Notation MonotonicFun T m := (@Pack _ _ T m).
Notation "[ 'monotonicfun' 'of' T ]" := ([get f | obj f ~ (T : _ -> _) ])
    (at level 0, format "[ 'monotonicfun'  'of'  T ]") : POrder_scope.
Notation "[ 'monotonicMixin' 'of' T ]" := (class [ monotonicfun of T ])
    (at level 0, format "[ 'monotonicMixin'  'of'  T ]") : POrder_scope.
End Exports.
    
End MonotonicFun.
Export MonotonicFun.Exports.


Lemma monotonic_mapR_chainMixin 
    (T T' : poset) (f : monotonicfun T T') (c : chain T) :
    Chain.mixin_of (f [<] c).
Proof.
    rewrite /Chain.mixin_of => x [a [Hain Hxeq]] y [b [Hbin Hyeq]].
    rewrite -Hxeq -Hyeq.
    case (Chain.class c a Hain b Hbin) => H; 
    [left | right]; by apply (MonotonicFun.class f).
Qed.

(** We make this a canonical structure, so we will get [f [<] c] as a chain if
    [f] is monotonic and [c] is a chain. *)
Canonical monotonic_chain (T T' : poset) (f : monotonicfun T T') (c : chain T) 
    : chain T' :=
    Chain (f [<] c) (@monotonic_mapR_chainMixin _ _ f c).







(* continuous *)
Module ContinuousFun.

Definition mixin_of (T T' : cpo) (f : monotonicfun T T') :=
    forall c : chain T, 
        f (cpo⊔ c) = cpo⊔ (f [<] c).
Notation class_of := mixin_of (only parsing).

Section ClassDef.

Structure type (T T' : cpo) := Pack {
    obj : monotonicfun T T';
    _ : class_of obj;
}.

Definition class T T' (cT : type T T') := 
    let: Pack _ c := cT return class_of (obj cT) in c.

End ClassDef.

Module Exports.
Coercion obj : type >-> monotonicfun.
Notation continuousfun := type.

(** The special notation for continuous function. *)
Notation "[ A ↦ B ]" := (type [cpo of A] [cpo of B]) 
    (at level 0, format "[ A  ↦  B ]"): POrder_scope.

Notation ContinuousFun T m := (@Pack _ _ T m).
Notation "[ 'continuousfun' 'of' T ]" := ([get f | obj f ~ [monotonicfun of T] ])
    (at level 0, format "[ 'continuousfun'  'of'  T ]") : POrder_scope.
Notation "[ 'continuousMixin' 'of' T ]" := (class [ continuousfun of T ])
    (at level 0, format "[ 'continuousMixin'  'of'  T ]") : POrder_scope.
End Exports.
    
End ContinuousFun.
Export ContinuousFun.Exports.


