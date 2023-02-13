(** * POrder.v : Library for partial orders. *)


From Babel Require Import TerminalDogma.premises 
                          TerminalDogma.Extensionality.

From Babel Require Export SetFacility.

From Coq Require Import Relations Classical.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** Reserved Notations *)
Declare Scope POrder_scope.
Open Scope POrder_scope.


Reserved Notation " a ⊑ b " (at level 60).
Reserved Notation " a ⊒ b " (at level 60).
Reserved Notation " a ⋢ b " (at level 60).

Reserved Notation " f '†r' " (at level 20).
Reserved Notation " P '†po' " (at level 10).


Reserved Notation " L '†L' " (at level 10).
Reserved Notation " cL '†cL' " (at level 10).

Reserved Notation "⊔ᶜᵖᵒ" (at level 40).
Reserved Notation "⊔ˡ" (at level 40).
Reserved Notation "⊓ˡ" (at level 40).
Reserved Notation "⊔ᶜˡ" (at level 40).
Reserved Notation "⊓ᶜˡ" (at level 40).

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
Section ClassDef.

Structure mixin_of (T : Type) := Mixin { op : relation T; ord : order T op }.
Definition class_of := mixin_of.

Structure type := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (cT : type).

Definition class := 
    let: Pack _ c := cT return class_of cT in c.
Definition pack := Pack.

End ClassDef.


Module Exports.
#[reversible] Coercion sort : type >-> Sortclass.

Notation poset := type.
Notation Poset T m := (@pack T m).

Notation "[ 'poset' 'of' T ]" := (T : poset)
  (at level 0, format "[ 'poset'  'of'  T ]") : POrder_scope.

Notation poset_op T := (op (class T)).
Definition poset_order (T : type) := ord (class T).
Definition poset_refl (T : type) := ord_refl _ _ (ord (class T)).
Definition poset_trans (T : type) := ord_trans _ _ (ord (class T)).
Definition poset_antisym (T : type) := ord_antisym _ _ (ord (class T)).

Notation " a ⊑ b " := (op (class _) a b) : POrder_scope.
Notation " a ⊒ b " := (op (class _) b a) (only parsing): POrder_scope.

Notation " a ⋢ b " := (~ a ⊑ b) : POrder_scope.

End Exports.

End Poset.
Export Poset.Exports.

Add Parametric Relation (po : poset): _ (@Poset.op _ (Poset.class po))
    reflexivity proved by (@poset_refl po)
    transitivity proved by (@poset_trans po)
    as poset_le_rel.

(** dual poset *)

Lemma dual_order {T : Type} (R : relation T) : order _ R -> order _ (R †r).
Proof. rewrite /dualRel => [H]. constructor.
    by apply H. 
    rewrite /transitive => x y z Hxy Hyz. move: Hyz Hxy. by apply H.
    rewrite /antisymmetric => x y Hxy Hyx. by apply H.
Qed.

(** get the dual poset *)
Definition dualPoset (po : poset) : poset :=
    Poset po (Poset.Mixin (dual_order (poset_order po))).
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
Admitted.




(*###################################################*)
(** ** chain *)

Module Chain.
Section ClassDef.

Definition mixin_of (T : poset) (A : 𝒫(T)) :=
    forall' x ∈ A, forall' y ∈ A, (x ⊑ y \/ y ⊑ x).
Definition class_of := mixin_of.


Structure type (T : poset) := Pack {
    set : 𝒫(T);
    _ : class_of set;
}.

Local Coercion set : type >-> powerset.

Variables (T : poset) (cT : type T).

Definition class (T : poset) (cT : type T) := 
    let: Pack _ c := cT return class_of cT in c.

Definition pack := Pack.

End ClassDef.

Module Exports.
#[reversible] Coercion set : type >-> powerset.
Arguments class [T] _.

Notation chain := type.
Notation Chain s m := (@pack _ s m).
Notation "[ 'chain' 'of' A ]" := ([get c | set c ~ A])
  (at level 0, format "[ 'chain'  'of'  A ]"): POrder_scope.
End Exports.

End Chain.
Export Chain.Exports.

(* em_is_chain: empty set is a chain *)
Lemma em_chain_mixin (T : poset) : @Chain.class_of T ∅.
Proof. rewrite /Chain.mixin_of => ? []. Qed.

Canonical em_is_chain (T : poset) := Chain ∅ (@em_chain_mixin T).


(*###################################################*)
(** CPO (with the join operator) *)
Module CPO.
Section ClassDef.

Record mixin_of (T0 : Type) (b : Poset.class_of T0)
                (T := Poset T0 b) := Mixin {
    join_of : chain T -> T;
    join_prop : forall A : chain T, supremum A (join_of A);
}.

#[projections(primitive)]
Record class_of (T : Type) := Class {
    base : Poset.class_of T;
    mixin : mixin_of base;
}.

Local Coercion base : class_of >-> Poset.class_of.
Local Coercion mixin : class_of >-> mixin_of.

Structure type := Pack {
    sort : Type;
    _ : class_of sort;
}.


Variables (T : Type) (cT : type).

Definition class := 
    let: Pack _ c := cT return class_of (sort cT) in c.

Definition pack b (m : mixin_of b) : type := Pack (@Class T b m).

Definition poset := Poset (sort cT) class.

Definition join_op : chain poset -> poset := join_of class.

End ClassDef.

Module Exports.

#[reversible] Coercion base : class_of >-> Poset.class_of.
#[reversible] Coercion mixin : class_of >-> mixin_of.
(*
#[reversible] Coercion sort : type >-> Sortclass.
*)
#[reversible] Coercion poset : type >-> Poset.type.
Canonical poset.

Notation cpo := type.
Notation CPO t m := (@pack t _ m).
Notation "[ 'cpo' 'of' T ]" := (T : cpo)
    (at level 0, format "[ 'cpo'  'of'  T ]") : POrder_scope.
Notation "⊔ᶜᵖᵒ" := join_op : POrder_scope.
End Exports.

End CPO.
Export CPO.Exports.


(** **** CPO_bottom: every CPO has the least element *)
Lemma CPO_bottom (C : cpo) : least 𝕌 (⊔ᶜᵖᵒ (set_em C)).
Proof.
    apply sup_em_iff_lea_uni.
    have Hbot := CPO.join_prop (CPO.class C).
    by apply Hbot.
Qed.

(*######################################################################*)
(** lattice *)

Module Lattice.
Section ClassDef.

Record mixin_of (T0 : Type) (b : Poset.class_of T0)
                (T := Poset T0 b) := Mixin {
    join_of : T0 -> T0 -> T0;
    join_prop : forall x y : T, supremum ({{x, y}}) (join_of x y);
    meet_of : T0 -> T0 -> T0;
    meet_prop : forall x y : T, infimum ({{x, y}}) (meet_of x y);
}.

#[projections(primitive)]
Record class_of (T : Type) := Class {
    base : Poset.class_of T;
    mixin : mixin_of base;
}.

Local Coercion base : class_of >-> Poset.class_of.
Local Coercion mixin : class_of >->  mixin_of.

Structure type := Pack {
    sort : Type;
    _ : class_of sort;
}.

Variable (T : Type) (cT : type).

Definition class := let: Pack _ c := cT return class_of (sort cT) in c.

Definition pack b m : type := Pack (@Class T b m).

Definition poset := Poset (sort cT) class.

Definition join_op := join_of class.
Definition meet_op := meet_of class.

End ClassDef.


Module Exports.
#[reversible] Coercion base : class_of >-> Poset.class_of.
#[reversible] Coercion mixin : class_of >-> mixin_of.
(** we remove the direct coercion to force Coq going through all base classes
    one by one.

#[reversible] Coercion sort : type >-> Sortclass.
*)
#[reversible] Coercion poset : type >-> Poset.type.
Canonical poset.

Notation lattice := type.
Notation Lattice t m := (@pack t _ m).

Notation "[ 'lattice' 'of' T ]" := (T : lattice)
  (at level 0, format "[ 'lattice'  'of'  T ]") : POrder_scope.
Notation "⊔ˡ" := join_op : POrder_scope.
Notation "⊓ˡ" := meet_op : POrder_scope.
End Exports.

End Lattice.
Export Lattice.Exports.


(** dual lattice canonical structure *)
Definition dual_lattice_mixin (T : lattice) : Lattice.class_of (T †po).
Proof.
    eapply Lattice.Class.
    refine (@Lattice.Mixin (T †po) (Poset.class (T †po)) 
            (@Lattice.meet_op T) _ (@Lattice.join_op T) _) => x y.
    by apply (Lattice.meet_prop (Lattice.class T)).
    by apply (Lattice.join_prop (Lattice.class T)).
Defined.

Canonical dual_lattice (T : lattice) := Lattice _ (dual_lattice_mixin T).
Notation " L '†L' " := (dual_lattice L) : POrder_scope.
    



(*###################################################*)
(** ** complete lattice *)

Module CLattice.
Section ClassDef.

(** Essential requirement
    Breaking the mixin into [essence_of] and the consistency requirements makes
    it easier to build CLattice directly.
    *)
Structure join_essence_of (T : poset) := JoinEssence {
    join_of : 𝒫(T) -> T;
    join_prop : forall A : 𝒫(T), supremum A (join_of A);
}.
Structure meet_essence_of (T : poset) := MeetEssence {
    meet_of : 𝒫(T) -> T;
    meet_prop : forall A : 𝒫(T), infimum A (meet_of A);
}.

Structure essence_of (T : poset) := Essence {
    join_half : join_essence_of T;
    meet_half : meet_essence_of T;
    (** we don't put top and bottom here, since they can be derived.*)
}.
Local Coercion join_half : essence_of >-> join_essence_of.
Local Coercion meet_half : essence_of >-> meet_essence_of.

Record mixin_of (T0 : Type) (b : Lattice.class_of T0) 
                    (T := Lattice T0 b) := Mixin {
    essence : essence_of T;
    (** we don't put top and bottom here, since they can be derived.*)
    join_consistent : forall (x y : T), (⊔ˡ x y) = join_of essence ({{x, y}});
    meet_consistent : forall (x y : T), (⊓ˡ x y) = meet_of essence ({{x, y}}); 
}.

Local Coercion essence : mixin_of >-> essence_of.

#[projections(primitive)]
Record class_of (T : Type) := Class {
    base : Lattice.class_of T;
    mixin : mixin_of base;
}.

Local Coercion base : class_of >-> Lattice.class_of.
Local Coercion mixin : class_of >-> mixin_of.

Structure type := Pack {
    sort : Type;
    _ : class_of sort;
}.

Variables (T : Type) (cT : type).

Definition class := let: Pack _ c := cT return class_of (sort cT) in c.

Definition pack b m : type := Pack (@Class T b m).

Definition lattice := Lattice (sort cT) class.


Definition cpo_mixin : CPO.mixin_of (Lattice.class lattice).
Proof.
    refine (@CPO.Mixin _ _ (join_of class) _).
    move => c. by apply join_prop.
Defined.

Definition cpo := CPO _ cpo_mixin.

Definition join_op := join_of (essence class).
Definition meet_op := meet_of (essence class).

End ClassDef.

(** From half essence to full essence. *)
Definition join_half_to_essence (T : poset) 
    : join_essence_of T -> essence_of T.
Proof.
    move => je. constructor. by apply je.
    set meet_of := fun A => (join_of je) (lb A).
    refine (@MeetEssence _ meet_of _) => A.
    apply sup_lb_is_inf.
    by apply (join_prop je).
Defined.


(** EXPERIMENTAL
    Build CLattice directly from [essence_of]. *)

Definition essence_to_lattice_mixin
    (T : poset) (e : essence_of T ) : Lattice.mixin_of (Poset.class T) :=
    {|
      Lattice.join_of := λ x y : T, join_of (join_half e) ({{x, y}});
      Lattice.join_prop := λ x y : T, join_prop (join_half e) ({{x, y}});
      Lattice.meet_of := λ x y : T, meet_of (meet_half e) ({{x, y}});
      Lattice.meet_prop := λ x y : T, meet_prop (meet_half e) ({{x, y}})
    |}.

Definition essence_to_lattice (T : poset) (e : essence_of T) :=
    Lattice _ (essence_to_lattice_mixin e).

(** This function allows us to build [mixin_of] from [essence_of] directly.*)
Definition essence_to_mixin
    (T : poset) (e : essence_of T) : 
        mixin_of (Lattice.class (essence_to_lattice e)).
Proof.
    econstructor.
    (** consistency of join *)
    move => x y. apply (sup_unique (A := {{x, y}})). 
    by apply Lattice.join_prop. by apply join_prop.
    (** consistency of meet *)
    move => x y. apply (inf_unique (A := {{x, y}})). 
    by apply Lattice.meet_prop. by apply meet_prop.
    Unshelve. by destruct T.
Defined.

(** Build [mixin_of] from [join_essence_of]. 
    WARNING: using this technique will cause the other half to be hard to use.
*)
Definition join_essence_to_mixin (T : poset) (je : join_essence_of T) :=
    essence_to_mixin (join_half_to_essence je).

Module Exports.
#[reversible] Coercion join_half : essence_of >-> join_essence_of.
#[reversible] Coercion meet_half : essence_of >-> meet_essence_of.
#[reversible] Coercion essence : mixin_of >-> essence_of.
#[reversible] Coercion base : class_of >-> Lattice.class_of.
#[reversible] Coercion mixin : class_of >-> mixin_of.
#[reversible] Coercion cpo : type >-> CPO.type.
Canonical cpo.
#[reversible] Coercion lattice : type >-> Lattice.type.
Canonical lattice.

Notation clattice := type.
Notation CLattice T m := (@pack T _ m).

Notation "[ 'clattice' 'of' T ]" := (T : clattice)
    (at level 0, format "[ 'clattice'  'of'  T ]") : POrder_scope.
Notation "⊔ᶜˡ" := join_op : POrder_scope.
Notation "⊓ᶜˡ" := meet_op : POrder_scope.

End Exports.

End CLattice.
Export CLattice.Exports.



(** dual lattice canonical structure *)
Definition dual_clattice_essence (T : clattice) : CLattice.essence_of (T †L).
Proof. 

    refine (@CLattice.Essence (T †L) _ _ ).
    refine (@CLattice.JoinEssence (T †L) 
                (CLattice.meet_of (CLattice.class T)) _).
    by apply (CLattice.meet_prop(CLattice.class T)).
    refine (@CLattice.MeetEssence (T †L) 
                (CLattice.join_of (CLattice.class T)) _).
    by apply (CLattice.join_prop(CLattice.class T)).
Defined.

Definition dual_clattice_mixin (T : clattice) : 
    CLattice.mixin_of (Lattice.class (T †L)).
Proof.
    refine (@CLattice.Mixin _ _ (dual_clattice_essence T) _ _) => x y.
    by apply (@CLattice.meet_consistent _ (Lattice.class T)).
    by apply (@CLattice.join_consistent _ (Lattice.class T)).
Defined.

Canonical dual_clattice (T : clattice) := CLattice _ (dual_clattice_mixin T).
Notation " L '†cL' " := (dual_clattice L) : POrder_scope.
    

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


(*###########################################################################*)
(** monotonic *)
Module MonotonicFun.
Section ClassDef.

Definition mixin_of (T T' : poset) (f : T -> T') :=
    forall x y : T, x ⊑ y -> f x ⊑ f y.
Definition class_of := mixin_of.


Structure type (T T' : poset) := Pack {
    obj : T -> T';
    _ : class_of obj;
}.

Variable (T T' : poset) (cT : type T T').

Definition class := let: Pack _ c := cT return class_of (obj cT) in c.

Definition pack := Pack.

End ClassDef.

Module Exports.
#[reversible] Coercion obj : type >-> Funclass.
Notation monotonicfun := type.

(** The special notation for monotonic function. *)
Notation "[ A ↦ᵐ B ]" := (type [poset of A] [poset of B]) 
    (at level 0, format "[ A  ↦ᵐ  B ]"): POrder_scope.

Notation MonotonicFun T m := (@pack _ _ T m).
Notation "[ 'monotonicfun' 'of' T ]" := (T : type _ _ )
    (at level 0, format "[ 'monotonicfun'  'of'  T ]") : POrder_scope.
End Exports.
    
End MonotonicFun.
Export MonotonicFun.Exports.


Lemma monotonic_mapR_chainMixin 
    (T T' : poset) (f : monotonicfun T T') (c : chain T) :
    Chain.mixin_of (f [<] c).
Proof.
    rewrite /Chain.mixin_of => x [a [Hain Hxeq]] y [b [Hbin Hyeq]].
    rewrite Hxeq Hyeq.
    case (Chain.class c a Hain b Hbin) => H; 
    [left | right]; by apply (MonotonicFun.class f).
Qed.

(** We make this a canonical structure, so we will get [f [<] c] as a chain if
    [f] is monotonic and [c] is a chain. *)
Canonical monotonic_mapR_chain (T T' : poset) (f : monotonicfun T T') (c : chain T) 
    : chain T' :=
    Chain (f [<] c) (@monotonic_mapR_chainMixin _ _ f c).


(** The equivalence of monotonicfun. *)
Lemma monotonicfun_eqP (T T' : poset) (f g : monotonicfun T T') :
    f = g <-> (f : T -> T') = (g : T -> T').
Proof. split.
    by move => ->.
    destruct f as [objf  cf], g as [objg cg] => //= Hobjeq.
    move: cf cg. rewrite Hobjeq => cf cg. f_equal.
    by apply proof_irrelevance.
Qed.


(* continuous *)
Module ContinuousFun.

Section ClassDef.

(** We must build the mixin of monotonic function first, because [f [<] c] must
    be a chain. *)
Definition mixin_of (T T' : cpo) (f0 : T -> T')
            (bf : MonotonicFun.class_of f0) (f := MonotonicFun f0 bf) :=
    forall c : chain T, f (⊔ᶜᵖᵒ c) = ⊔ᶜᵖᵒ (f [<] c).

#[projections(primitive)]
Record class_of (T T' : cpo) (f : T -> T'):= Class {
    base : MonotonicFun.class_of f;
    mixin : mixin_of base;
}.

Local Coercion base : class_of >-> MonotonicFun.class_of.
Local Coercion mixin : class_of >-> mixin_of.

Structure type (T T' : cpo) := Pack {
    obj : T -> T';
    _ : class_of obj;
}.

Variable (T T' : cpo) (f : T -> T') (cT : type T T').

Definition class := let: Pack _ c := cT return class_of (obj cT) in c.

Definition pack b m := @Pack _ _ _ (@Class T T' f b m).

Definition monotonicfun := MonotonicFun _ class.
End ClassDef.

Module Exports.
#[reversible] Coercion base : class_of >-> MonotonicFun.class_of.
#[reversible] Coercion mixin : class_of >-> mixin_of.

#[reversible] Coercion monotonicfun : type >-> MonotonicFun.type.
Canonical monotonicfun.

Notation continuousfun := type.

(** The special notation for continuous function. *)
Notation "[ A ↦ B ]" := (type [cpo of A] [cpo of B]) 
    (at level 0, format "[ A  ↦  B ]"): POrder_scope.
Notation ContinuousFun T m := (@pack _ _ T _ m).
Notation "[ 'continuousfun' 'of' T ]" := (T : type _ _)
    (at level 0, format "[ 'continuousfun'  'of'  T ]") : POrder_scope.
End Exports.
    
End ContinuousFun.
Export ContinuousFun.Exports.


