(** * POrder.v : Library for partial orders. *)


From Ranko Require Import TerminalDogma.premises 
                          TerminalDogma.Extensionality
                          NaiveSet.


From Coq Require Import Classical Relation_Definitions.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** Reserved Notations *)
Declare Scope POrder_scope.
Open Scope POrder_scope.

Reserved Notation " f '=r' ( X ) g " (at level 50).
Reserved Notation " a '⊑' ( p )  b " (at level 60, format " a  '⊑' ( p )  b ").
Reserved Notation " A '=po' B " (at level 60).
Reserved Notation " A '⊆po' B " (at level 60).
Reserved Notation " f '†r' " (at level 20).
Reserved Notation " P '†po' " (at level 10).

Reserved Notation " L1 '=L' L2 " (at level 60).
Reserved Notation " L '†L' " (at level 10).
Reserved Notation " cL1 '=cL' cL2 " (at level 60).
Reserved Notation " L1 '⊆cL' L2 " (at level 60).
Reserved Notation " cL '†cL' " (at level 10).


(** relation, this definition copies the design of [eqType] in MathComp.
    for [order], see [Coq.Relation_Definitions] 
    *)

Module OrderRel.

Structure mixin_of T R := Mixin { _ : order T R }.
Notation class_of := mixin_of (only parsing).

Section ClassDef.

Structure type T := Pack { o_rel; _ : @class_of T o_rel }.

Definition class (T : Type) (cT : type T) := 
    let: Pack _ c := cT return class_of (o_rel cT) in c.

End ClassDef.

Module Exports.
Coercion o_rel : type >-> relation.
Notation orderRel := type.
Notation orderRelMixin := Mixin.
Notation OrderRel T m := (@Pack _ T m).
Notation "[ 'orderRelMixin' 'of' T ]" := (class _ : mixin_of T)
  (at level 0, format "[ 'orderRelMixin'  'of'  T ]") : POrder_scope.
Notation "[ 'orderRel' 'of' T ]" := ([get r | rel r ~ T ])
  (at level 0, format "[ 'orderRel'  'of'  T ]") : POrder_scope.
End Exports.

End OrderRel.
Export OrderRel.Exports.


Lemma orderRel_eqP (T : Type) (R1 R2 : orderRel T) :
    R1 = R2 <-> (R1 : relation _) = (R2 : relation _).
Proof. split. by move=> ->.
    move => H. destruct R1 as [r1 [Hr1]], R2 as [r2 [Hr2]] => //=.
    simpl in H. move: Hr1 Hr2. rewrite H => Hr1 Hr2.
    f_equal. f_equal. by apply proof_irrelevance.
Qed.








Record poset (T : Type) := mk_poset {
    po_rel : relation T;
    po_order : order _ po_rel;
}.
Notation " [poset 'of' R ] " := ([get x | po_rel x ~ R])
    (format "[poset  'of'  R ]") : POrder_scope.

Notation " a '⊑' ( p ) b " := (po_rel p a b) : POrder_scope.

Lemma poseteqP (T : Type) (A B : poset T) : A = B <-> po_rel A = po_rel B.
Proof. split. by move => ->.
    destruct A as [ra oa], B as [rb ob] => //= => H.
    move : oa ob. rewrite H => oa ob. f_equal. by apply proof_irrelevance.
Qed.






Lemma le_order: order _ le. Admitted.

Definition poset_le : poset nat :=
    mk_poset le_order.

Canonical Structure poset_le.

Compute [poset of le].

Check (1 ⊑([poset of le]) 2).


Check (test_refl le).

Definition test (T : Type) (a : poset T) := po_order a.

Check (test nat).


Lemma sub


Definition subposet (A B : poset) :=
    (A ⊆ B) /\ ((po_rel A) =r (A) (po_rel B)).
Notation " A '⊆po' B " := (subposet A B).

Lemma subposet_eq (P Q: poset) : P =po Q <-> P ⊆po Q /\ Q ⊆po P.
Proof.
    unfold subposet. split.
    { intros HPeqQ. destruct HPeqQ as [Hseteq Hreleq]. 
    split. split. by rewrite Hseteq.
    by []. split. by rewrite Hseteq. rewrite <-Hseteq. by symmetry. }
    { intros [[HPinQset HPinQrel] [HQinPset HQinPrel]].
     split. apply subset_eq. by split. by[]. }
Qed.

Lemma subposet_refl : reflexive _ subposet.
Proof. unfold reflexive, subposet. intros P. by split. Qed.


Lemma subposet_trans : transitive _ subposet.
Proof.
    unfold transitive, subposet. 
    intros P Q R [HPinQset HPinQrel] [HQinRset HQinRrel].
    split. by transitivity Q.  transitivity (po_rel Q).
    by []. by apply releq_mor_subset with (Y := Q).
Qed.



Section get_subposet.

(* Rrefl_subset : r reflexive on X -> A ⊆ X -> r reflexive on A *)
Lemma Rrefl_subset (X : set T) : forall r, Rrefl X r -> forall' A ⊆ X, Rrefl A r.
Proof.
    unfold Rrefl. intros r Hr_refl A HAinX t HtinA. apply Hr_refl. apply HAinX. apply HtinA.
Qed.

(* Rtrans_subset : r transitive on X -> A ⊆ X -> r transitive on A *)
Lemma Rtrans_subset (X : set T) : forall r, Rtrans X r -> forall' A ⊆ X, Rtrans A r.
Proof.
    unfold Rtrans. intros ??????????. by apply H; apply H0.
Qed.

(* Rasymm_subset : r anti-symmetric on X -> A ⊆ X -> r anti-symmetric on A *)
Lemma Rasymm_subset (X : set T) : forall r, Rasymm X r -> forall' A ⊆ X, Rasymm A r.
Proof.
    unfold Rasymm. intros ????????. by apply H; apply H0.
Qed.

(* the subposet *)
Definition sub_poset (po : poset) (A : set T) (HAinX : A ⊆ po) : poset :=
    mk_poset (Rrefl_subset po HAinX) 
        (Rtrans_subset po HAinX) (Rasymm_subset po HAinX).

(* verify the properties defined by subposets *)
Lemma sub_poset_sub (po : poset) (A : set T) (HAinX : A ⊆ po_set po) :
    sub_poset po HAinX ⊆po po.
Proof. unfold sub_poset, subposet. simpl. by split. Qed.
    
End get_subposet.


(* the dual relation*)
Definition dual_rel (r : relation T) : relation T := (fun a b : T => r b a).
Notation " f '†r' " := (dual_rel f).

(* dual_rel_inv : x ⊑ y -> x ⊑ y (in the dual relation) *)
Lemma dual_rel_inv {x y : T} {r : relation T} (Hxley : r x y)
        : (r †r) y x.
Proof. apply Hxley. Qed.


Lemma dual_dual_releq (X : set T) (f : relation T) : f †r †r =r(X) f.
Proof. unfold dual_rel, releq. by intros. Qed.


(* The dual relation preserves reflexivity, transivity and anti-symmetricity. *)

(* dual_rel_Rrefl : Rrefl X r -> Rrefl X (r †) *)
Lemma dual_rel_Rrefl (X : set T) (r : relation T) : Rrefl X r -> Rrefl X (r †r).
Proof. unfold Rrefl, dual_rel. by intros ?. Qed.

(* dual_rel_Rtrans : Rtrans X r -> Rtrans X (r †) *)
Lemma dual_rel_Rtrans (X : set T) (r : relation T) : Rtrans X r -> Rtrans X (r †r).
Proof. unfold Rtrans, dual_rel. intros. by apply H with (y := y). Qed.

(* dual_rel_Rasymm : Rasymm X r -> Rasymm X (r †) *)
Lemma dual_rel_Rasymm (X : set T) (r : relation T) : Rasymm X r -> Rasymm X (r †r).
Proof. unfold Rasymm, dual_rel. intros. by apply H. Qed.

(** the dual poset 
    This acts as a important proof technique in poset. *)
Definition dual_poset (po : poset) : poset :=
    mk_poset (dual_rel_Rrefl po) 
        (dual_rel_Rtrans po) (dual_rel_Rasymm po).
Notation " P '†po' " := (dual_poset P).

Lemma dual_dual_poseteq (po : poset) : po †po †po =po po.
Proof.
    unfold dual_poset, poseteq. simpl. split. by[]. by apply dual_dual_releq.
Qed.

End PosetDef.

Notation " a '⊑' ( p ) b " := (po_rel p a b).
Notation " f '†r' " := (dual_rel f).
Notation " A '=po' B " := (poseteq A B).
Notation " A '⊆po' B " := (subposet A B).
Notation " P '†po' " := (dual_poset P).

Add Parametric Morphism {T : Type} {X : set T}: (@dual_rel T)
    with signature (@releq T X) ==> (@releq T X) as dual_rel_mor_eq.
Proof.
    intros r l Hreql.
    unfold dual_rel, releq. intros. by apply Hreql. 
Qed.    

Add Parametric Relation {T : Type} : (poset T) (@poseteq T)
  reflexivity proved by (@poseteq_refl T)
  symmetry proved by (@poseteq_symm T)
  transitivity proved by (@poseteq_trans T)
  as eq_poset_rel.

Add Parametric Morphism {T : Type} : (@po_set T)
    with signature (@poseteq T) ==> (@seteq T) as po_set_mor_eq.
Proof. intros P Q HPeqQ. by destruct HPeqQ. Qed.

Add Parametric Relation {T : Type} : (poset T) (@subposet T)
  reflexivity proved by (@subposet_refl T)
  transitivity proved by (@subposet_trans T)
  as sub_poset_rel.

Add Parametric Morphism {T : Type} : (@subposet T)
    with signature (@poseteq T) ==> (@poseteq T) ==> iff as subposet_mor_eq.
Proof.
    intros P Q HPeqQ R S HReqS. 
    rewrite subposet_eq in HPeqQ. rewrite subposet_eq in HReqS.
    destruct HPeqQ as [HPinQ HQinP]. destruct HReqS as [HRinS HSinR].
    split. 
    intros. transitivity P. by []. by transitivity R.
    intros. transitivity Q. by []. by transitivity S.
Qed.

Add Parametric Morphism {T : Type} : (@dual_poset T)
    with signature (@subposet T) ==> (@subposet T) as dual_poset_mor_sub.
Proof.
    unfold subposet, dual_poset. simpl. intros P Q [HPinQset HPinQrel].
    split. by[]. by apply dual_rel_mor_eq.
Qed.

Add Parametric Morphism {T : Type} : (@dual_poset T)
    with signature (@poseteq T) ==> (@poseteq T) as dual_poset_mor_eq.
Proof.
    intros P Q HPeqQ. unfold poseteq, dual_poset; simpl.
    split. apply HPeqQ. destruct HPeqQ. rewrite H0. reflexivity.
Qed.

Section Poset_Upper_Lower_Set.

Variable (T : Type).

(* A is an upper_set *)
Definition upper_set (po : poset T) (A : set T) : Prop :=
    A ⊆ po /\ forall' a ∈ po, forall' b ∈ po, (a ∈ A -> (po_rel po) a b -> b ∈ A).

(* A is an lower_set *)
Definition lower_set (po : poset T) (A : set T) : Prop :=
    A ⊆ po /\ forall' a ∈ po, forall' b ∈ po, (a ∈ A -> (po_rel po) b a -> b ∈ A).
    
(* the upper set of A *)
Definition up_s (po : poset T) (A : set T) := 
    { x : x ∈ po /\ exists' a ∈ A, (po_rel po) a x }.

(* up_s_in_X : upper set of A ⊆ X*)
Lemma up_s_in_X (po : poset T) (A : set T) : up_s po A ⊆ po.
Proof. unfold subset. intros. apply H. Qed.

(* the lower set of A *)
Definition low_s (po : poset T) (A : set T) := 
    { x : x ∈ po /\ exists' a ∈ A, (po_rel po) x a }.

(* low_s_in_X : lower set of A ⊆ X*)
Lemma low_s_in_X (po : poset T) (A : set T) : low_s po A ⊆ po.
Proof. unfold subset. intros. apply H. Qed.

End Poset_Upper_Lower_Set.

Add Parametric Morphism {T : Type} : (@upper_set T)
    with signature (@poseteq T) ==> (@seteq T) ==> iff as upper_set_mor_eq.
Proof.
    intros P Q HPeqQ A B HAeqB. unfold upper_set. split.

    { intros. split. rewrite <-HAeqB. destruct HPeqQ. rewrite <-H0. apply H.
    intros. apply HAeqB. destruct H. apply H4 with (a := a). by apply HPeqQ.
    by apply HPeqQ. by apply HAeqB. apply HPeqQ. 
    by apply HPeqQ. by apply HPeqQ. by[]. } 

    { intros. split. rewrite HAeqB. destruct HPeqQ. rewrite H0. apply H.
        intros. apply HAeqB. destruct H. apply H4 with (a := a). by apply HPeqQ.
        by apply HPeqQ. by apply HAeqB. by apply HPeqQ. }
Qed. 


Add Parametric Morphism {T : Type} : (@lower_set T)
    with signature (@poseteq T) ==> (@seteq T) ==> iff as lower_set_mor_eq.
Proof.
    intros P Q. intros.
    assert (Hdual := @upper_set_mor_eq T (dual_poset P) (dual_poset Q)).
    apply Hdual. by apply dual_poset_mor_eq. by [].
Qed. 



Section Poset_Upper_Lower_Bound.

Variable (T : Type).

(* x is an upper bound of A *)
Definition upper_bound (po : poset T) (A : set T) (x : T) :=
    A ⊆ po /\ x ∈ po /\ forall' a ∈ A, (po_rel po) a x.
    
(* x is an lower bound of A *)
Definition lower_bound (po : poset T) (A : set T) (x : T) :=
    A ⊆ po /\ x ∈ po /\ forall' a ∈ A, (po_rel po) x a.

(* upper_bound_em : any a is an upper bound of ∅ *)
Lemma upper_bound_em (po : poset T) : 
    forall' a ∈ po, upper_bound po ∅ a.
Proof.
    intros. unfold upper_bound. split. apply em_subset. split.
    apply H. intros. destruct H0.
Qed.


(* lower_bound_em : any a is an lower bound of ∅ *)
Lemma lower_bound_em (po : poset T) : 
    forall' a ∈ po, lower_bound po ∅ a.
Proof.
    assert (Hdual := upper_bound_em (dual_poset po)).
    by apply Hdual.
Qed.

(* le_upper_bound : ∀ x ∈ A, x ⊑ some upper bound of A *)
Lemma le_upper_bound (po : poset T) (A : set T) :
    forall x, upper_bound po A x -> forall' y ∈ A, (po_rel po) y x.
Proof.
    intros x Hup y Hyin.
    by apply Hup.
Qed.

(* ge_lower_bound : ∀ x ∈ A, some lower bound of A ⊑ x *)
Lemma ge_lower_bound (po : poset T) (A : set T) :
    forall x, lower_bound po A x -> forall' y ∈ A, (po_rel po) x y.
Proof.
    assert (Hdual := @le_upper_bound (dual_poset po)).
    by apply Hdual.
Qed.

(** This is also an important morphism (but seems not allowed in Coq) 
    upper_bound (poset T) (set T) (T) :
    subposet ==> supset ==> smaller_than ==> implication *)
Lemma upper_bound_mor_imp (po1 po2 : poset T) (H1in2 : po1 ⊆po po2)
    (A B : set T) (HAinB : A ⊆ B) 
    (a b : T) (Hbin : b ∈ po_set po2)
    (Haleb : po_rel po2 a b) : upper_bound po1 B a -> upper_bound po2 A b.
Proof.
    unfold upper_bound. intros HubBa. destruct H1in2 as [H1in2set H1in2rel].
    split. rewrite HAinB. transitivity (po_set po1). apply HubBa. by[].
    split. by[]. intros c Hcin.
    apply (rel_Rtrans po2) with (y := a). 
    apply H1in2set. apply HubBa. by apply HAinB.
    apply H1in2set. by apply HubBa. by[]. 
    apply H1in2rel. apply HubBa. by apply HAinB. apply HubBa.
    apply HubBa. by apply HAinB. by [].
Qed.

Lemma lower_bound_mor_imp (po1 po2 : poset T) (H1in2 : po1 ⊆po po2)
    (A B : set T) (HAinB : A ⊆ B) 
    (a b: T) (Hbin : b ∈ po_set po2)
    (Haleb : po_rel po2 b a) : lower_bound po1 B a -> lower_bound po2 A b.
Proof.
    assert (Hdual := @upper_bound_mor_imp (dual_poset po1) (dual_poset po2)).
    apply Hdual. by apply dual_poset_mor_sub. by[]. apply Hbin. apply Haleb.
Qed.

End Poset_Upper_Lower_Bound.

Add Parametric Morphism {T : Type} : (@upper_bound T)
    with signature (@poseteq T) ==> (@seteq T) ==> eq ==> iff as upper_bound_mor_eq.
Proof.
    intros P Q HPeqQ A B HAeqB x.
    unfold upper_bound. destruct HPeqQ as [Hseteq Hreleq]. 
    split.
    { intros. split. rewrite <-HAeqB. rewrite <-Hseteq. apply H.
        split. apply Hseteq. apply H. intros a Hain. 
        apply Hreleq. apply H. by apply HAeqB. by apply H. apply H.
        by rewrite HAeqB. }
    { intros. split. rewrite HAeqB. rewrite Hseteq. apply H.
        split. apply Hseteq. apply H. intros a Hain. 
        apply Hreleq. rewrite Hseteq. rewrite HAeqB in Hain. by apply H.
        rewrite Hseteq. apply H. apply H. by rewrite <-HAeqB.  }
Qed.

Add Parametric Morphism {T : Type} : (@lower_bound T)
    with signature (@poseteq T) ==> (@seteq T) ==> eq ==> iff as lower_bound_mor_eq.
Proof.
    intros P Q. intros.
    assert (Hdual := @upper_bound_mor_eq _ (dual_poset P) (dual_poset Q)).
    apply Hdual. by apply dual_poset_mor_eq. by []. by [].
Qed. 


Section Poset_Bound_Set.

Variable (T : Type).

(* set of all upper bounds *)
Definition ub (po : poset T) (A : set T) : set T := 
    { x : upper_bound po A x }.

(* set of all lower bounds *)
Definition lb (po : poset T) (A : set T) : set T := 
    { x : lower_bound po A x}.


(* ub_em : ub(∅) {=} X *)
Lemma ub_em (po : poset T) : ub po ∅ {=} po.
Proof.
    apply subset_eq; unfold ub; unfold subset; unfold upper_bound. split.
    - intros. destruct H. destruct H0. apply H0.
    - intros. simpl. split. apply em_subset. split. apply H. intros. destruct H0. 
Qed. 

(* lb_em : lb(∅) {=} X *)
Lemma lb_em (po : poset T) : lb po ∅ {=} po.
Proof.
    assert (Hdual := ub_em (dual_poset po)).
    by apply Hdual.
Qed. 

(* ub_in_X : ub(A) ⊆ X *)
Lemma ub_in_X (po : poset T) (A : set T) : ub po A ⊆ po.
Proof.
    unfold ub. unfold upper_bound. unfold subset. simpl. 
    intros. destruct H. destruct H0. apply H0. 
Qed.

(* lb_in_X : lb(A) ⊆ X *)
Lemma lb_in_X (po : poset T) (A : set T) : lb po A ⊆ po.
Proof.
    assert (Hdual := @ub_in_X (dual_poset po)).
    by apply Hdual.
Qed.

(* in_lb_ub : a ∈ A -> a ∈ lb (ub (A)) *)
Lemma in_lb_ub (po : poset T) (A : set T) (HAinX : A ⊆ po): 
    forall' a ∈ A, a ∈ lb po (ub po A).
Proof.
    intros a HainA. unfold lb, ub, lower_bound, upper_bound. simpl. split.
    - unfold subset. simpl. intros. apply H.
    - split. apply HAinX. apply HainA. intros. apply H. apply HainA.
Qed.

(* in_ub_lb : a ∈ A -> a ∈ ub (lb (A)) *)
Lemma in_ub_lb (po : poset T) (A : set T) (HAinX : A ⊆ po): 
    forall' a ∈ A, a ∈ ub po (lb po A).
Proof.
    assert (Hdual := in_lb_ub (dual_poset po)).
    by apply Hdual.
Qed.

End Poset_Bound_Set.


Add Parametric Morphism {T : Type} : (@ub T)
    with signature (@subposet T) ==> (@supset T) ==> (@subset T) as ub_mor_sub.
Proof.
    intros P Q HPinQ A B HAinB.
    unfold ub, subset. simpl. intros x. intros. 
    apply upper_bound_mor_imp with (po1 := P) (B := A) (a := x). 
    by[]. apply HAinB. apply HPinQ. apply H. apply rel_Rrefl. apply HPinQ. apply H.
    by [].
Qed.

Add Parametric Morphism {T : Type} : (@lb T)
    with signature (@subposet T) ==> (@supset T) ==> (@subset T) as lb_mor_sub.
Proof.
    intros P Q. intros.
    assert (Hdual := @ub_mor_sub _ (dual_poset P) (dual_poset Q)).
    apply Hdual. by apply dual_poset_mor_sub. by [].
Qed.

Add Parametric Morphism {T : Type} : (@ub T)
    with signature (@poseteq T) ==> (@seteq T) ==> (@seteq T) as ub_mor_eq.
Proof.
    intros P Q HPeqQ A B HAeqB. apply subset_eq. split; apply ub_mor_sub.
    rewrite HPeqQ. reflexivity. rewrite <-sub_sup_set. by rewrite HAeqB.
    rewrite HPeqQ. reflexivity. rewrite <-sub_sup_set. by rewrite HAeqB.
Qed.

Add Parametric Morphism {T: Type} : (@lb T)
    with signature (@poseteq T) ==> (@seteq T) ==> (@seteq T) as lb_mor_eq.
Proof.
    intros P Q. intros.
    assert (Hdual := @ub_mor_eq _ (dual_poset P) (dual_poset Q)).
    apply Hdual. by apply dual_poset_mor_eq. by[].
Qed.



Section Poset_Max_Min.

Variable (T : Type).

(* x is maximal in A *)
Definition maximal (po : poset T) (A : set T) (x : T) :=
    A ⊆ po /\ x ∈ A /\ forall' a ∈ A, (a <> x -> ~ (po_rel po) a x).

(* x is minimal in A *)
Definition minimal (po : poset T) (A : set T) (x : T) :=
    A ⊆ po /\ x ∈ A /\ forall' a ∈ A, (a <> x -> ~ (po_rel po) x a).

End Poset_Max_Min.




Section Poset_Largest_Least.

Variable (T : Type).

(* x is largest in A *)
Definition largest (po : poset T) (A : set T) (x : T) :=
    A ⊆ po /\ x ∈ A /\ forall' a ∈ A, (po_rel po) a x.

(* x is least in A *)
Definition least (po : poset T) (A : set T) (x : T) :=
    A ⊆ po /\ x ∈ A /\ forall' a ∈ A, (po_rel po)x a.

(* dual_lar_is_lea : x = largest A -> x = least A (in the dual poset) *)
Lemma dual_lar_is_lea (po : poset T) (A : set T) (x : T)
    : largest po A x -> least (po †po) A x.
Proof. auto. Qed.

(* dual_lea_is_lar : x = least A -> x = largest A (in the dual poset) *)
Lemma dual_lea_is_lar (po : poset T) (A : set T) (x : T)
    : least po A x -> largest (po †po) A x.
Proof. auto. Qed.



(* lar_unique : largest element of A is unique *)
Lemma lar_unique (po : poset T) (A : set T) (a b : T)
        (Ha_largest : largest po A a) (Hb_largest : largest po A b)
        : a = b.
Proof.
    apply (rel_Rasymm po);
    destruct Ha_largest as [HAinX [HainA Halar]];
    destruct Hb_largest as [HBinX [HbinB Hblar]]; try apply A.
    apply HAinX. apply HainA. apply HBinX. apply HbinB.
    apply Hblar. apply HainA. apply Halar. apply HbinB.
Qed.

(* lea_unique : least element of A is unique *)
Lemma lea_unique (po : poset T) (A : set T) (a b : T)
        (Ha_least : least po A a) (Hb_least : least po A b)
        : a = b.
Proof.    
    assert (Hdual := @lar_unique (dual_poset po) A).
    by apply Hdual.
Qed.

(* lar_in_ub : largest element is an upper bound *)
Lemma lar_in_ub (po : poset T) :
    forall (A : set T) (x : T), largest po A x -> upper_bound po A x.
Proof.
    intros A x [HAinX [HxinA Hxlar]].
    unfold upper_bound. split. apply HAinX. split. apply HAinX. apply HxinA.
    apply Hxlar.
Qed.

(* lea_in_ub : least element is a lower bound *)
Lemma lea_in_lb (po : poset T) :
    forall (A : set T) (x : T), least po A x -> lower_bound po A x.
Proof.
    assert (Hdual := @lar_in_ub (dual_poset po)).
    by apply Hdual.
Qed.

Lemma lar_subpo_mor (po1 po2 : poset T) (H1in2 : po1 ⊆po po2)
    (A : set T) (a : T) : largest po1 A a -> largest po2 A a.
Proof.
    unfold largest. intros Hlar1.
    split. transitivity (po_set po1). by apply Hlar1. by apply H1in2.
    split. apply Hlar1. intros b Hbin. apply H1in2. by apply Hlar1.
    apply Hlar1. by apply Hlar1. by apply Hlar1.
Qed.

Lemma lea_subpo_mor (po1 po2 : poset T) (H1in2 : po1 ⊆po po2)
    (A : set T) (a : T) : least po1 A a -> least po2 A a.
Proof.
    assert (Hdual := @lar_subpo_mor (dual_poset po1) (dual_poset po2)).
    apply Hdual. by apply dual_poset_mor_sub.
Qed.

(* lar_subset : A ⊆ B -> largest (A) ⊑ largest (B) *)
Lemma lar_subset (po : poset T) {A B: set T}
    {a b : T} (HAinB : A ⊆ B)
    (Ha_lar : largest po A a) (Hb_lar : largest po B b) : (po_rel po) a b.
Proof.
    destruct Ha_lar as [HAinX [HainA Ha_lar]].
    destruct Hb_lar as [HBinX [HbinB Hb_lar]].
    apply Hb_lar. apply HAinB. apply HainA.
Qed.

(* lea_subset : A ⊆ B -> least (B) ⊑ least (A) *)
Lemma lea_subset (po : poset T) {A B: set T}
    {a b : T} (HAinB : A ⊆ B)
    (Ha_lea : least po A a) (Hb_lea : least po B b) : (po_rel po) b a.
Proof.
    assert (Hdual := @lar_subset (dual_poset po) A B a b).
    by apply Hdual.
Qed.

(* lea_point_up_s : a = least ( up_s { a } )*)
Lemma lea_point_up_s (po : poset T) (a : T) (HainX : a ∈ po) :
    least po (up_s po ({{ a }})) a.
Proof.
    unfold least. unfold up_s. simpl. split.
    unfold subset. simpl. intros. apply H. split. split. apply HainX.
    exists a. split. by left. by apply (rel_Rrefl po).
    intros. destruct H as [? [? [[? | ?] ?]]]. rewrite <- H0. apply H1. destruct H0.
Qed. 

(* lar_point_low_s : a = largest ( low_s { a } )*)
Lemma lar_point_low_s (po : poset T) (a : T) (HainX : a ∈ po) : 
    largest po (low_s po ({{ a }})) a.
Proof.
    assert (Hdual := @lea_point_up_s (dual_poset po)).
    by apply Hdual.
Qed. 

End Poset_Largest_Least.


Add Parametric Morphism {T : Type} : (@largest T)
    with signature (@poseteq T) ==> (@seteq T) ==> eq ==> iff as lar_mor_eq.
Proof.
    intros P Q HPeqQ A B HAeqB x. unfold largest. split.
    { intros Hlarx. split. rewrite <-HAeqB. rewrite <-HPeqQ. apply Hlarx.
        split. apply HAeqB. apply Hlarx. intros a Hain. apply HPeqQ. 
        apply Hlarx. by apply HAeqB. apply Hlarx. by apply Hlarx.
        apply Hlarx. by rewrite HAeqB. }
    { intros Hlarx. split. rewrite HAeqB. rewrite HPeqQ. apply Hlarx.
        split. apply HAeqB. apply Hlarx. intros a Hain. apply HPeqQ.
        rewrite HPeqQ. apply Hlarx. by rewrite <-HAeqB. rewrite HPeqQ.
            apply Hlarx. by apply Hlarx. apply Hlarx. by apply HAeqB. }
Qed.
        
Add Parametric Morphism {T : Type} : (@least T)
    with signature (@poseteq T) ==> (@seteq T) ==> eq ==> iff as lea_mor_eq.
Proof.
    intros P Q. intros.
    assert (Hdual := @lar_mor_eq _ (dual_poset P) (dual_poset Q)).
    apply Hdual. by apply dual_poset_mor_eq. by[]. by[]. 
Qed.

Section Poset_Sup_Inf.

Variable (T : Type).

(** x is the supremum of A. Here supremum is presented as a proposition,
    because the supremum does not always exists. *)
Definition supremum (po : poset T) (A : set T) (x : T) := least po (ub po A) x.

(* x is the infimum of A *)
Definition infimum (po : poset T) (A : set T) (x : T) := largest po (lb po A) x.

(* sup_unique : supremum is unique *)
Lemma sup_unique {po : poset T} {A : set T} {a b : T}
    (Ha_sup : supremum po A a) (Hb_sup : supremum po A b)
    : a = b.
Proof.
    apply (lea_unique (po := po) (A := ub po A)).
    apply Ha_sup. apply Hb_sup.
Qed.

(* inf_unique : infimum element of A is unique *)
Lemma inf_unique {po : poset T} {A : set T} {a b : T}
    (Ha_inf : infimum po A a) (Hb_inf : infimum po A b)
    : a = b.
Proof.
    assert (Hdual := @sup_unique (dual_poset po) A a b).
    by apply Hdual.
Qed.


(* lar_is_sup : x = largest A -> x = sup A *)
Lemma lar_is_sup (po : poset T) : 
    forall (A : set T) (x : T), largest po A x -> supremum po A x.
Proof.
    intros A x. split.
    apply ub_in_X. split. apply lar_in_ub. apply H.
    intros a Hainub. apply Hainub. apply H.
Qed.

(* lea_is_inf : x = least A -> x = inf A *)
Lemma lea_is_inf (po : poset T) : 
    forall (A : set T) (x : T), least po A x -> infimum po A x.
Proof.
    assert (Hdual := @lar_is_sup (dual_poset po)).
    by apply Hdual.
Qed.

(* sup_le_upper_bound : sup A ⊑ some upper bound of A *)
Lemma sup_le_upper_bound (po : poset T) :
    forall (A : set T) (a b : T), 
        upper_bound po A a -> supremum po A b -> (po_rel po) b a.
Proof.
    intros A a b Hub Hsup.
    apply Hsup. apply Hub.
Qed.


(* inf_ge_lower_bound : some lower bound of A ⊑ inf A*)
Lemma inf_ge_lower_bound (po : poset T) :
    forall (A : set T) (a b : T), 
        lower_bound po A a -> infimum po A b -> (po_rel po) a b.
Proof.
    intros A a b Hlb Hinf.
    apply Hinf. apply Hlb.
Qed.
    
(* le_sup : ∀ x ∈ A, x ⊑ ⊔A *)
Lemma le_sup (po : poset T) (A : set T) (a : T):
    supremum po A a -> forall' x ∈ A, (po_rel po) x a.
Proof. intros Hsup. intros x HxinA. by apply Hsup. Qed.

(* ge_inf : ∀ x ∈ A, × ⊒ ⊓A *)
Lemma ge_inf (po : poset T) (A : set T) (a : T):
    infimum po A a -> forall' x ∈ A, (po_rel po) a x.
Proof.
    assert (Hdual := @le_sup (dual_poset po)).
    by apply Hdual.
Qed.

(* sup_em : sup ∅ {=} least X *)
Lemma sup_em (po : poset T) (a : T): 
    supremum po ∅ a <-> least po po a.
Proof.
    split.
    { intros Hsup. destruct Hsup. split. by apply subset_refl. split.
    apply H0. intros. apply H0. by apply upper_bound_em. }
    { intros Hlea. destruct Hlea. split. by apply ub_in_X. split.
    rewrite ub_em. by apply H0. intros b Hbin. apply H0. by apply Hbin. }
Qed.

(* inf_em : sup ∅ {=} largest X *)
Lemma inf_em (po : poset T) (a : T):
    infimum po ∅ a <-> largest po po a.
Proof.
    assert (Hdual := @sup_em (dual_poset po)).
    by apply Hdual.
Qed.

(* sup_in_is_lar : sup A ∈ A -> sup A = largest A *)
Lemma sup_in_is_lar (po : poset T) (A : set T) {a : T} 
    (Ha_sup : supremum po A a) (Ha_in : a ∈ A) : largest po A a.
Proof.
    split. apply Ha_sup. split. apply Ha_in. intros b HbinA. by apply Ha_sup.
Qed.

(* inf_in_is_lea : inf A ∈ A -> inf A = least A *)
Lemma inf_in_is_lea (po : poset T) (A : set T) {a : T}
    (Ha_inf : infimum po A a) (Ha_in : a ∈ A) : least po A a.
Proof.
    assert (Hdual := @sup_in_is_lar (dual_poset po)).
    apply Hdual. apply Ha_inf. by[].
Qed.

(* sup_subset : A ⊆ B -> sup A ⊑ sup B *)
Lemma sup_subset {po : poset T} {A B: set T}
    {a b : T} (HAinB : A ⊆ B)
    (Ha_sup : supremum po A a) (Hb_sup : supremum po B b) : (po_rel po) a b.
Proof.
    assert (Hubin : ub po B ⊆ ub po A). 
    { apply ub_mor_sub. reflexivity. apply HAinB. } 
    apply (lea_subset Hubin). 
    apply Hb_sup. apply Ha_sup.
Qed.

(* inf_subset : A ⊆ B -> inf B ⊑ inf A *)
Lemma inf_subset {po : poset T} {A B: set T}
    {a b : T} (HAinB : A ⊆ B)
    (Ha_inf : infimum po A a) (Hb_inf : infimum po B b) : (po_rel po) b a.
Proof.
    assert (Hdual := @sup_subset (dual_poset po) A B a b).
    by apply Hdual.
Qed.


(* inf_ub_is_sup : the infimum of upper bounds of A is the supremum of A *)
Lemma inf_ub_is_sup (po : poset T) :
    forall' A ⊆ po_set po, forall a, infimum po (ub po A) a -> supremum po A a.
Proof.
    intros A HAinX a Hinf. destruct Hinf. destruct H0. split. apply ub_in_X.
    split.  split. apply HAinX. split. apply H0. intros ??.
    apply H1. by apply in_lb_ub.
    apply H0.
Qed.

(* sup_lb_is_inf : the supremum of lower bounds of A is the infimum of A *)
Lemma sup_lb_is_inf (po : poset T) :
    forall' A ⊆ po_set po, forall a, supremum po (lb po A) a -> infimum po A a.
Proof.
    assert (Hdual := @inf_ub_is_sup (dual_poset po)).
    by apply Hdual.
Qed.

(* up_s_sup_is_ub : the upper set of the supremum of A are the upper bounds of A *)
Lemma up_s_sup_is_ub (po : poset T) (a : T) (A : set T) (Hsup : supremum po A a)
    : up_s po ({{ a }}) {=} ub po A.
Proof.
    split; simpl in *.
    intros. unfold upper_bound. split. apply Hsup. split. apply H. intros. destruct H.
    destruct H1. destruct H1. destruct H1. rewrite H1 in H2. 
    assert (H' : po_rel po a0 a). { by apply Hsup. } 
    assert (Ha0inX : a0 ∈ po_set po ). { apply Hsup. apply H0. }
    assert (HainX : a ∈ po_set po). { apply Hsup. }
    apply (rel_Rtrans po _ Ha0inX _ HainX _ H).
    apply H'. apply H2. by apply le_sup with (A := A).

    intros Hubx. split. apply Hubx. exists a. split. auto. 
    by apply sup_le_upper_bound with (A := A).
Qed.

(* low_s_inf_is_lb : the lower set of the infimum of A are the lower bounds of A *)
Lemma low_s_inf_is_lb (po : poset T) (a : T) (A : set T) (Hinf : infimum po A a)
    : low_s po ({{ a }}) {=} lb po A.
Proof.
    assert (Hdual := @up_s_sup_is_ub (dual_poset po) a A).
    apply Hdual. apply Hinf.
Qed.


(** This does not always hold. Consider the case of empty set. *)
(*
Lemma sup_subpo_mor (po1 po2 : poset T) (H1in2 : po1 ⊆po po2)
    (A : set T) (a : T) : supremum po1 A a -> supremum po2 A a.
Proof.
Qed.
*)  
    

End Poset_Sup_Inf.

Add Parametric Morphism {T : Type} : (@supremum T)
    with signature (@poseteq T) ==> (@seteq T) ==> eq ==> iff as sup_mor_eq.
Proof.
    intros P Q HPeqQ A B HAeqB x. unfold supremum.
    apply lea_mor_eq. by[]. by apply ub_mor_eq. reflexivity.
Qed.

Add Parametric Morphism {T : Type} : (@infimum T)
    with signature (@poseteq T) ==> (@seteq T) ==> eq ==> iff as inf_mor_eq.
Proof.
    intros P Q. intros.
    assert (Hdual := @sup_mor_eq _ (dual_poset P) (dual_poset Q)).
    apply Hdual. by apply dual_poset_mor_eq. by []. by [].
Qed.


Section Poset_SpecialSet.

Variable (T : Type).

(* bi_ele_compare : x ⊑ y -> ∀ a b ∈ { x , y }, a ⊑ b \/ b ⊑ a*)
Lemma bi_ele_compare (po : poset T) : 
    let X := po_set po in
    let r := po_rel po in
    forall' x ∈ X, forall' y ∈ X, 
    (r x y -> forall' a ∈ {{ x , y }}, forall' b ∈ {{ x , y }},
        (r a b \/ r b a)).
Proof.
    intros X r x HxinX y HyinX Hxley a Hain b Hbin.
    destruct Hain. destruct Hbin. left. rewrite H H0. apply (rel_Rrefl po). apply HxinX.
    destruct H0. left. rewrite H H0. apply Hxley. destruct H0.
    destruct H. destruct Hbin. right. rewrite H H0. apply Hxley.
    destruct H0. left. rewrite H H0. apply (rel_Rrefl po). apply HyinX. destruct H0.
    destruct H.
Qed.

Lemma bi_ele_lea (po : poset T):
    forall' x ∈ po, forall' y ∈ po, forall' z ∈ po,
        (po_rel po z x -> po_rel po z y -> z ∈ {{x, y}} -> least po ({{x, y}}) z).
Proof.
    intros x Hxin y Hyin z Hzin Hzx Hzy Hzin'.
    split. by apply bi_ele_in. split. by[]. intros a Hain. destruct Hain.
    by rewrite H. destruct H. by rewrite H. by destruct H.
Qed.

Lemma bi_ele_lar (po : poset T):
    forall' x ∈ po, forall' y ∈ po, forall' z ∈ po,
        (po_rel po x z -> po_rel po y z -> z ∈ {{x, y}} -> largest po ({{x, y}}) z).
Proof.
    intros x Hxin y Hyin z Hzin Hxz Hyz Hzin'.
    split. by apply bi_ele_in. split. by[]. intros a Hain. destruct Hain.
    by rewrite H. destruct H. by rewrite H. by destruct H.
Qed.


End Poset_SpecialSet.




Section IntervalSet.

Variable (T : Type).

(* interval_set : { x : a ⊑ x ⊑ b } *)
Record itv_set := mk_itv_set {
    po_itv_set : poset T;
    itv_set_set :> set T;
    a_itv : T;
    b_itv : T;
    ainX_itv : a_itv ∈ po_itv_set;
    binX_itv : b_itv ∈ po_itv_set;
    aleb_itv : po_rel po_itv_set a_itv b_itv;
    itv_set_prop : itv_set_set {=} 
        { x : x ∈ po_itv_set /\ 
        po_rel po_itv_set a_itv x /\ po_rel po_itv_set x b_itv};
}.

(*
Definition itv_set (po : poset T) {a b : T} 
    (HainX : a ∈ po) (HbinX : b ∈ po) (Haleb : po_rel po a b) := 
    { x : x ∈ po /\ po_rel po a x /\ po_rel po x b}.
*)

(* interval_subset : { x : a ⊑ x ⊑ b } ⊆ X *)
Lemma itv_subset (iset : itv_set) : iset ⊆ po_itv_set iset.
Proof.
    simpl. destruct iset; unfold subset; simpl. intros x Hx. 
    rewrite itv_set_prop0 in Hx. by destruct Hx.
Qed.

Lemma itv_lar (iset : itv_set) : largest (po_itv_set iset) iset (b_itv iset).
Proof.
    unfold largest; simpl. split. by apply itv_subset.
    split. apply iset. simpl. split. apply iset. split. apply iset. 
    apply rel_Rrefl. apply iset.
    intros a Hain. by apply iset.
Qed.

Lemma itv_lea (iset : itv_set) : least (po_itv_set iset) iset (a_itv iset).
Proof.
    unfold least; simpl. split. by apply itv_subset.
    split. apply iset. simpl. split. apply iset. split. 
    apply rel_Rrefl. apply iset. by apply iset.
    intros a Hain. by apply iset.
Qed.


(* itv_sup : b = sup { x : a ⊑ x ⊑ b } *)
Lemma itv_sup (iset : itv_set) : supremum (po_itv_set iset) iset (b_itv iset).
Proof.
    apply lar_is_sup. apply itv_lar.
Qed.

(* itv_inf : a = inf { x : a ⊑ x ⊑ b } *)
Lemma itv_inf (iset : itv_set) : infimum (po_itv_set iset) iset (a_itv iset).
Proof.
    apply lea_is_inf. apply itv_lea.
Qed.

(*
(* itv_dual_eq : the interval set in a poset = the interval set in the dual poset *)
Lemma itv_dual_eq (po : poset T) {a b : T} 
    (HainX : a ∈ po_set po) (HbinX : b ∈ po_set po) (Haleb : po_rel po a b):
    itv_set (po †po) HbinX HainX (dual_rel_inv Haleb) {=} itv_set po HainX HbinX Haleb.
Proof.
    destruct po.
    unfold dual_poset. unfold itv_set. simpl. split. 
    intros. simpl. split. apply H. split. apply H. apply H.
    intros. simpl. split. apply H. split. apply H. apply H.
Qed.

Lemma itv_dual_dual_eq (po : poset T) {a b : T} 
    (HainX : a ∈ po_set po) (HbinX : b ∈ po_set po) (Haleb : po_rel po a b):
    itv_set po HainX HbinX Haleb {=} itv_set (po †po †po) HainX HbinX Haleb.
Proof.
    unfold itv_set, seteq, predeq. simpl. intros.
    assert (Heq1 : ((po_rel po) †r †r) a x <-> po_rel po a x).
    { split; intros; assumption. }
    rewrite Heq1.
    assert (Heq2 : ((po_rel po) †r †r) x b <-> po_rel po x b).
    { split; intros; assumption. }
    rewrite Heq2. reflexivity.
Qed.
*)

End IntervalSet.



Section CPO.

Variable (T : Type).

(* being a Chain *)
Definition chain (po : poset T) (C : set T) :=  
    C ⊆ po /\ forall' x ∈ C, forall' y ∈ C, (po_rel po x y \/ po_rel po y x).

(* CPO *)
Record CPO := mk_CPO {
    CPO_po :> poset T;
    CPO_join : set T -> T;
    CPO_prop :> forall A : set T, chain CPO_po A -> supremum CPO_po A (CPO_join A);
}.

(* em_is_chain: empty set is a chain *)
Lemma em_is_chain (po : poset T) : chain po ∅.
Proof. unfold chain. split. apply em_subset. simpl. intros. destruct H. Qed. 




(** **** CPO_bottom: every CPO has the least element *)

(** The construction *)
Definition CPO_bottom (C : CPO) : T := CPO_join C ∅.

(** proof for the construction *)
Lemma CPO_bottom_pf (C : CPO) : least C C (CPO_bottom C).
Proof.
    destruct C. assert (Hem := CPO_prop0 _ (em_is_chain CPO_po0)). simpl in *.
    unfold supremum in Hem. by rewrite ub_em in Hem.
Qed.
    
(** lemma for existence *)
Lemma CPO_bottom_ex (C : CPO) : exists x, least C C x.
Proof.
    exists (CPO_bottom C). by apply CPO_bottom_pf.
Qed.

End CPO.


Section Lattice_Operator.

Variable (T : Type).

(* semi-lattice *)

(* equivalence of lattice operators *)
Definition lattop_eq (X : set T) (f g : T -> T -> T) :=
    forall' x ∈ X, forall' y ∈ X, f x y = g x y.

Lemma lattop_eq_refl (X : set T): reflexive _ (lattop_eq X).
Proof. unfold reflexive, lattop_eq. by intros. Qed.


Lemma lattop_eq_symm (X : set T): symmetric _ (lattop_eq X).
Proof. unfold symmetric, lattop_eq. intros f g Hfg. symmetry. by apply Hfg. Qed.


Lemma lattop_eq_trans (X : set T): transitive _ (lattop_eq X).
Proof. 
    unfold transitive, lattop_eq. intros f g h Hfg Hgh x Hxin y Hyin.
    rewrite <-Hgh. by apply Hfg. by []. by [].
Qed.


End Lattice_Operator.

Add Parametric Relation {T : Type} {X : set T} : (T -> T -> T) (lattop_eq X)
    reflexivity proved by (@lattop_eq_refl _ X)
    symmetry proved by (@lattop_eq_symm _ X)
    transitivity proved by (@lattop_eq_trans _ X)
    as eq_lattop_rel.

Section Lattice.

Variable (T : Type).

(* f is the join operator *)
Definition latt_join (po : poset T) (f : T -> T -> T) :=
    forall' x ∈ po, forall' y ∈ po, supremum po ({{ x, y }}) (f x y).

(** join operator is a function between sets *)
Lemma join_setfun (po : poset T) (f : T -> T -> T) (Hjoin : latt_join po f) :
    setfun_A_B_A f po po.
Proof. 
    unfold setfun_A_B_A. intros a Hain b Hbin.
    unfold latt_join in Hjoin. by apply (Hjoin a Hain b Hbin).
Qed.

(* f is the meet operator*)
Definition latt_meet (po : poset T) (f : T -> T -> T) :=
    forall' x ∈ po, forall' y ∈ po, infimum po ({{ x, y }}) (f x y).

(** meet operator is a function between sets *)
Lemma meet_setfun (po : poset T) (f : T -> T -> T) (Hmeet : latt_meet po f) :
    setfun_A_B_A f po po.
Proof. 
    unfold setfun_A_B_A. intros a Hain b Hbin.
    unfold latt_meet in Hmeet. by apply (Hmeet a Hain b Hbin).
Qed.

(**
    Notice the difference between 
        "exists a join operator"
    and
        "for all finite subset, the supremum exists".
*)

(* po is a lattice (not computable) *)
Definition lattice (po : poset T) :=
    forall' x ∈ po, forall' y ∈ po, 
    ((exists i, infimum po ({{x, y}}) i) /\ (exists s, supremum po ({{x, y}}) s)).

(* lattice (computable) *)
Record latt := mk_latt {
    latt_po :> poset T;
    meet_op : T -> T -> T;
    meet_prop :> latt_meet latt_po meet_op;
    join_op : T -> T -> T;
    join_prop :> latt_join latt_po join_op;
}.

(** it turns out the according to the definition here, the lattice can be empty... *)

(** The definition of lattice satisfies the required property. *)
Lemma latt_is_lattice (L : latt) : lattice L.
Proof.
    unfold lattice. intros x Hxin y Hyin.
    split. exists (meet_op L x y). by apply L. exists (join_op L x y). by apply L.
Qed.


(* the equivalence between lattices*)
Definition latteq (A B : latt) :=
    (A =po B) /\ (lattop_eq A (meet_op A) (meet_op B))
        /\ (lattop_eq A (join_op A) (join_op B)).
Notation " L1 '=L' L2 " := (latteq L1 L2).


(* dual_latt_join : latt_meet po f -> latt_join (dual_poset po) f *)
Lemma dual_latt_join (po : poset T) (f : T -> T -> T)
    : latt_meet po f -> latt_join (po †po) f.
Proof. auto. Qed.


(* dual_latt_meet : latt_join po f -> latt_meet (dual_poset po) f *)
Lemma dual_latt_meet (po : poset T) (f : T -> T -> T)
    : latt_join po f -> latt_meet (po †po) f.
Proof. auto. Qed.

(* the dual lattice *)
Definition dual_latt (L : latt) : latt :=
    mk_latt (dual_latt_meet (join_prop L)) (dual_latt_join (meet_prop L)).
Notation " L '†L' " := (dual_latt L).

Lemma dual_dual_latteq (L : latt) : L †L †L =L L.
Proof.
    destruct L.
    unfold dual_latt, latteq; simpl. split.
    apply dual_dual_poseteq. split; reflexivity.
Qed.

End Lattice.

Notation " L1 '=L' L2 " := (latteq L1 L2).


Section CLattice_Operator.

Variable (T : Type).


(* equivalence of complete lattice operators *)
Definition clattop_eq (X : set T) (f g : set T -> T) :=
    forall' Y ⊆ X, f Y = g Y.


Lemma clattop_eq_refl (X : set T): reflexive _ (clattop_eq X).
Proof. unfold reflexive, lattop_eq. by intros. Qed.


Lemma clattop_eq_symm (X : set T): symmetric _ (clattop_eq X).
Proof. 
    unfold symmetric, lattop_eq. intros f g Hfg. 
    unfold clattop_eq. symmetry. by apply Hfg. 
Qed.


Lemma clattop_eq_trans (X : set T): transitive _ (clattop_eq X).
Proof. 
    unfold transitive, lattop_eq. intros f g h Hfg Hgh A HAinX.
    unfold clattop_eq in Hfg, Hgh.
    rewrite <-Hgh. by rewrite Hfg. by [].
Qed.

End CLattice_Operator.

Add Parametric Relation {T : Type} {X : set T}: (set T -> T) (clattop_eq X)
    reflexivity proved by (@clattop_eq_refl T X)
    symmetry proved by (@clattop_eq_symm T X)
    transitivity proved by (@clattop_eq_trans T X)
    as eq_clattop_rel.


Section Complete_Lattice.

Variable (T : Type).
Hypothesis (H_LEM : LEM).

(* f is the complete join operator *)
Definition clatt_join (po : poset T) (f : set T -> T) :=
    forall' A ⊆ po, supremum po A (f A).

(* f is the complete meet operator *)
Definition clatt_meet (po : poset T) (f : set T -> T) :=
    forall' A ⊆ po, infimum po A (f A).


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

*)

(* po is a complete lattice (not computable) *)
Definition complete_lattice (po : poset T) :=
    forall' A ⊆ po, ((exists i, infimum po A i) /\ (exists s, supremum po A s)).

(** Here is an intermediate definition ... 
(* po is a complete lattice (computable) *)
Definition complete_lattice' (po : poset T) :=
    (exists f_meet : set T -> T, (forall' A ⊆ po, infimum po A (f_meet A)))
    /\ (exists f_join : set T -> T, (forall' A ⊆ po, supremum po A (f_join A))).
*)

(* complete lattice (computable) *)
Record clatt := mk_complatt {
    clatt_po :> poset T;
    cmeet_op : set T -> T;
    cmeet_prop :> clatt_meet clatt_po cmeet_op;
    cjoin_op : set T -> T;
    cjoin_prop :> clatt_join clatt_po cjoin_op;
    clatt_bot : T;
    clatt_bot_prop :> least clatt_po (po_set clatt_po) clatt_bot;
    clatt_top : T;
    clatt_top_prop :> largest clatt_po (po_set clatt_po) clatt_top;
}.

(* comp_latt_prop : "comp_latt" satisfies "complete lattice" property *)
Lemma clatt_is_complete_lattice (cL : clatt) : complete_lattice cL.
Proof. 
    destruct cL; simpl. split. 
    exists (cmeet_op0 A). by apply cmeet_prop0. 
    exists (cjoin_op0 A). by apply cjoin_prop0.
Qed.


Definition clatteq (cL1 cL2 : clatt) := 
    (cL1 =po cL2) 
        /\ (clattop_eq cL1 (cmeet_op cL1) (cmeet_op cL2))
        /\ (clattop_eq cL1 (cjoin_op cL1) (cjoin_op cL2)).
Notation " L1 '=cL' L2 " := (clatteq L1 L2).

Definition subclatt (cL1 cL2 : clatt) :=
    (cL1 ⊆po cL2)
        /\ (clattop_eq cL1 (cmeet_op cL1) (cmeet_op cL2))
        /\ (clattop_eq cL1 (cjoin_op cL1) (cjoin_op cL2)).
Notation " L1 '⊆cL' L2 " := (subclatt L1 L2).

(* dual_clatt_join : clatt_meet po f -> clatt_join (dual_poset po) f *)
Lemma dual_clatt_join (po : poset T) (f : set T -> T)
    : clatt_meet po f -> clatt_join (dual_poset po) f.
Proof. auto. Qed.


(* dual_clatt_meet : clatt_join po f -> clatt_meet (dual_poset po) f *)
Lemma dual_clatt_meet (po : poset T) (f : set T -> T)
    : clatt_join po f -> clatt_meet (dual_poset po) f.
Proof. auto. Qed.


(* the dual complete lattice *)
Definition dual_clatt (cL : clatt) : clatt :=
    mk_complatt (dual_clatt_meet (cjoin_prop cL)) (dual_clatt_join (cmeet_prop cL))
                (dual_lar_is_lea (clatt_top_prop cL))
                (dual_lea_is_lar (clatt_bot_prop cL)).
Notation " cL '†cL' " := (dual_clatt cL).
                

(** The construction and proof of the transformation cmeet and cjoin operators. *)
Lemma cmeet_2_cjoin (po : poset T) (f : set T -> T) : 
    clatt_meet po f -> clatt_join po (fun S => f (ub po S)).
Proof.
    intros Hcmeet.
    unfold clatt_join. unfold clatt_meet in Hcmeet.
    intros A HAinX. apply inf_ub_is_sup. apply HAinX. apply Hcmeet. apply ub_in_X.
Qed.

Lemma cjoin_2_cmeet (po : poset T) (f : set T -> T) :
    clatt_join po f -> clatt_meet po (fun S => f (lb po S)).
Proof.
    intros Hcjoin.
    unfold clatt_meet. unfold clatt_join in Hcjoin.
    intros A HAinX. apply sup_lb_is_inf. apply HAinX. apply Hcjoin. apply lb_in_X.
Qed.


(* clatt_meet_join_ex_ff : complete meet exists <-> complete join exists *)
Theorem clatt_meet_join_ex_iff (po : poset T): 
    (exists f, clatt_meet po f) <-> (exists f, clatt_join po f).
Proof.
    split.
    intros [f Hf]. exists (fun S => f (ub po S)). by apply cmeet_2_cjoin.
    intros [f Hf]. exists (fun S => f (lb po S)). by apply cjoin_2_cmeet.
Qed.

(** Construction and proof from the complete join (meet) operator to the top
    (bottom) element. *)
Lemma cjoin_2_top (po : poset T) (f : set T -> T) (Hcjoin : clatt_join po f) :
    largest po po (f po).
Proof.
    unfold largest. split. apply subset_refl. split. apply Hcjoin. apply subset_refl.
    intros. apply Hcjoin. apply subset_refl. apply H.
Qed.

Lemma cmeet_2_bot (po : poset T) (f : set T -> T) (Hcmeet : clatt_meet po f) :
    least po po (f po).
Proof.
    unfold least. split. apply subset_refl. split. apply Hcmeet. apply subset_refl.
    intros. apply Hcmeet. apply subset_refl. apply H.
Qed.
(** The existence version. *)
(* cjoin_2_top_ex : complete join exists -> largest element exists *)
Lemma cjoin_2_top_ex (po : poset T) :
    (exists f, clatt_join po f) -> (exists x, largest po po x).
Proof.
    intros [f Hf]. exists (f po). by apply cjoin_2_top.
Qed. 
        
(* cmeet_2_bot_ex : complete meet exists -> least element exists *)
Lemma cmeet_2_bot_ex (po : poset T) :
    (exists f, clatt_meet po f) -> (exists x, least po (po_set po) x).
Proof.
    intros [f Hf]. exists (f po). by apply cmeet_2_bot.
Qed.

(* sup_clatt_ub_is_top : in a complete lattice, the supremum of the upper bounds of A is the top element *)
Lemma sup_clatt_ub_is_top (cL : clatt) (A : set T) (HAinX : A ⊆ cL): 
    forall a, supremum cL (ub cL A) a -> largest cL cL a.
Proof.
    intros a HsupubAa. split. by apply subset_refl. split. by apply HsupubAa.
    intros b HbinX. destruct cL. simpl in *. 
    assert (Halar : a = clatt_top0).
    { apply (rel_Rasymm clatt_po0). apply HsupubAa. apply clatt_top_prop0.

        apply clatt_top_prop0. apply HsupubAa.
        apply HsupubAa. simpl. apply upper_bound_mor_imp 
            with (po1 := clatt_po0) (B := po_set clatt_po0) (a := clatt_top0).
        reflexivity. by[]. apply clatt_top_prop0. apply rel_Rrefl. apply clatt_top_prop0.
        apply clatt_top_prop0. }
    rewrite Halar. by apply clatt_top_prop0.
Qed.

(* inf_clatt_lb_is_bot : in a complete lattice, the infimum of the lower bounds of A is the bot element *)
Lemma inf_clatt_lb_is_bot (cL : clatt) (A : set T) (HAinX : A ⊆ cL): 
    forall a, infimum cL (lb cL A) a -> least cL cL a.
Proof.
    assert (Hdual := sup_clatt_ub_is_top (dual_clatt cL)).
    apply Hdual. apply HAinX.
Qed.

End Complete_Lattice.

Notation " L1 '=cL' L2 " := (clatteq L1 L2).
Notation " cL '†cL' " := (dual_clatt cL).
Notation " L1 '⊆cL' L2 " := (subclatt L1 L2).


Section CLattice_Special.

Variable (T : Type).

(** support lemma *)
Lemma finset_foldr_larger (L : latt T) (l : list T) (A : set T) (HAinL : A ⊆ L) 
    (HlinL : l2s l ⊆ L) (HleqA : l2s l {=} A) (a : T) (HainA : a ∈ A) : 
    forall' b ∈ A, (po_rel L) b (fold_right (join_op L) a l).
Proof.
    intros b Hbin. induction l. 
    simpl in *. rewrite <-HleqA in HainA. destruct HainA.
    simpl in *. apply le_sup with (A := {{a0, fold_right (join_op L) a l}}).
    apply L. apply HlinL. by simpl; auto. apply foldr_ls_in_set. 
    transitivity ({{a0}} ∪ l2s l). by apply union_sub_r. by[]. apply join_setfun.
    by apply L.
Abort.
    

(** in any lattice, a nonempty finite set has the supremum and infimum element *)
Lemma latt_finset_sup (L : latt T) (l : list T) (A : set T) (HAinL : A ⊆ L) 
    (Hnem : set_nonempty A) (Hl2A : l2s l {=} A) (a : T) (HainA : a ∈ A) : 
    supremum L A (fold_right (join_op L) a l).
Proof.
    split. by apply ub_in_X. split. 
    split. by[]. split. apply foldr_ls_in_set. by rewrite Hl2A. 
    apply join_setfun. by apply L. by apply HAinL.
    intros b Hbin. induction l.
    { simpl in *. symmetry in Hl2A. destruct (set_nem_em Hnem Hl2A). }
Abort.

(* TODO #11 #10 *)
(*
Lemma fin_meet_bot (po : poset T) (m_op : T -> T -> T) (H_meet : latt_meet po m_op)
        (A : set T) (HAinpo : A ⊆ po) :
        set_nonempty A -> set_finite A -> exists x, least po A x.
Proof.
    intros [a Hain] [l Hl]. 
    (** fold the list starting from a (actually arbitrary starting point is fine)*)
    exists (fold_left m_op l a).
    generalize dependent A.
    induction l.
    { intros. rewrite Hl in Hain. destruct Hain. }
    { intros. simpl in *. 
    assert (HA_next_eq : A -- ({{a0}} -- list_2_set l) {=} list_2_set l).
        { rewrite Hl. rewrite union_comm. by apply union_diff_eq. }
    assert (HA_next_in :  A -- ({{a0}} -- list_2_set l) ⊆ po).
        { transitivity A. by apply diff_subset. by []. }

    destruct (H_LEM (a ∈ A -- ({{a0}} -- list_2_set l))) as [Hain_next | Hain_next_n].

    { assert (Hlea := IHl  (A -- ({{a0}} -- list_2_set l)) 
            HA_next_in Hain_next HA_next_eq). 
        split. by[]. split. 


     }
 
Theorem fin_latt_is_comp (L : latt T) : 
    set_nonempty L -> set_finite L -> complete_lattice L.
Proof.
    intros [a Hain] HLfin. inversion HLfin as [l Hl].

    (** get the bottom element *)
    set Llea := fold_left (meet_op L) l a.
    (** the complete meet part *)
    assert (Inf : forall' A ⊆ L, ∃ i : T, infimum L A i).
    { intros A HAinL. assert (Afin := subset_finite H_LEM HAinL HLfin).
        destruct Afin as [l_a Hl_a]. induction l_a.
        (** if A is empty set, we need to construct and prove the bottom element *)
        { simpl in Hl_a. exists Llea. rewrite Hl_a. unfold infimum. rewrite lb_em.
        unfold Llea. generalize dependent L. induction l.
        - intros. rewrite Hl in Hain. destruct Hain.
        - intros. simpl in *.  }
    }
    split. generalize dependent A.

Abort.
*)




Lemma cmeet_bi_ele_set (cL : clatt T) (a b : T) (Haleb : po_rel (clatt_po cL) a b)
    (Hsetin : ({{ a, b }}) ⊆ cL) : cmeet_op cL ({{ a, b }}) = a.
Proof.
    destruct cL. simpl in *. 
    apply inf_unique with (po := clatt_po0) (A := {{a, b}}).
    { apply cmeet_prop0. apply Hsetin. }
    { split. apply lb_in_X. split. split. apply Hsetin.
        split. apply Hsetin. simpl. auto. intros c Hcin. destruct Hcin.
        rewrite H. apply rel_Rrefl. apply Hsetin. by simpl; auto. destruct H.
        by rewrite H. destruct H. intros c Hcin. destruct Hcin. apply H0. simpl; auto. }
Qed.

Lemma cjoin_bi_ele_set (cL : clatt T) (a b : T) (Hageb : po_rel (clatt_po cL) b a)
    (Hsetin : ({{ a, b }}) ⊆ cL) : cjoin_op cL ({{ a, b }}) = a.
Proof.
    destruct cL. simpl in *. 
    apply sup_unique with (po := clatt_po0) (A := {{a, b}}).
    { apply cjoin_prop0. apply Hsetin. }
    { split. apply ub_in_X. split. split. apply Hsetin.
        split. apply Hsetin. simpl. auto. intros c Hcin. destruct Hcin.
        rewrite H. apply rel_Rrefl. apply Hsetin. by simpl; auto. destruct H.
        by rewrite H. destruct H. intros c Hcin. destruct Hcin. apply H0. simpl; auto. }
Qed.


End CLattice_Special.


(** TODO #12  *)
(*

Section DerivedLattice.

Variable (T : Type).

Print itv_set.

(* itv_cmeet : the cmeet operator limited on an interval is still cmeet *)
Lemma itv_cmeet 
    (cL : clatt T) 
    (a : T) (HainX : a ∈ (po_set (clatt_po cL))) 
    (b : T) (HbinX : b ∈ (po_set (clatt_po cL))) 
    (Haleb : (po_rel (clatt_po cL)) a b)
    (subpo : poset T) (Hsubpo : subpo ⊆po clatt_po cL)
    (Hseteq : po_set subpo {=} @itv_set _ (clatt_po cL) a b HainX HbinX Haleb) :
    let cmeet_op' := fun (A : set T) => (cmeet_op cL) ({{cmeet_op cL A, b}}) in
    clatt_meet subpo cmeet_op'.
Proof. 
    set po := clatt_po cL.
    set r := po_rel po.
    set X := po_set po.

    intros. inversion Hsubpo as [Hsetsub Hreleq].
    set s_itv := itv_set po HainX HbinX Haleb.
    assert (Hs_itv_in : s_itv ⊆ X). { apply itv_subset. }
    destruct cL. simpl in *.
    intros A HAin. 
    assert (HAinX : A ⊆ X). 
    { apply (subset_trans HAin). rewrite Hseteq. apply itv_subset. }
    assert (Hmeet_bi_in : {{cmeet_op0 A, b}} ⊆ X).
    { unfold subset. simpl. intros x Hx. destruct Hx. rewrite H. by apply cmeet_prop0.
        destruct H. by rewrite H. destruct H. }

    assert (HcmeetAinsubpo : set_nonempty A -> cmeet_op0 A ∈ subpo).
    {   
        intros [x Hxin].
        rewrite Hseteq. simpl. split. apply cmeet_prop0. apply HAinX.
        split. 
        { apply inf_ge_lower_bound with (A := A).
        apply lower_bound_mor_imp with (po1 := clatt_po0) (B := subpo) (a := a).
        reflexivity. by[]. by[]. apply rel_Rrefl. by[]. rewrite Hseteq.
        apply itv_inf. by apply cmeet_prop0. }
        { apply rel_Rtrans with (y := x). by apply cmeet_prop0. by apply HAinX.
            by []. by apply cmeet_prop0. apply le_sup with (A := subpo).
            rewrite Hseteq. by apply itv_sup. by apply HAin. }
    }

    assert (HcmeetAin : cmeet_op' A ∈ s_itv).
    { simpl. split. unfold cmeet_op'. by apply cmeet_prop0. split.

        apply cmeet_prop0. by []. simpl. unfold lower_bound. split. by [].
        split. by []. intros x Hxin. destruct Hxin. rewrite H.
        { apply (rel_Rtrans po) with (y := (cmeet_op0 s_itv)).
            by []. apply cmeet_prop0. apply itv_subset. by apply cmeet_prop0.

            assert (Haeq : a = cmeet_op0 s_itv). 
            { apply inf_unique with (po := po) (A := s_itv). apply itv_inf. apply cmeet_prop0.
                apply itv_subset. }
            rewrite Haeq. apply (rel_Rrefl po). apply cmeet_prop0.
            apply itv_subset.
            apply inf_subset with (po := po) (A := A) (B := s_itv).
            apply (subset_trans HAin). by rewrite Hseteq.
            apply cmeet_prop0. apply HAinX. apply cmeet_prop0. apply itv_subset.
        }
        destruct H. by rewrite H. destruct H.

        (* one more time *)
        apply cmeet_prop0. by []. simpl. auto.
    }
    
    assert (HcmeetAle : set_nonempty A -> cmeet_op0 ({{cmeet_op0 A, b}}) = cmeet_op0 A).
    {   intros [x Hxin].
        assert (Hle_b : r (cmeet_op0 A) b).
        { apply (rel_Rtrans po) with (y := x).
        by apply cmeet_prop0. by apply HAinX. by[]. by apply cmeet_prop0.
        assert (Hxinitv : x ∈ s_itv). 
        { unfold s_itv. unfold po. rewrite <- Hseteq. by apply HAin. }
        apply Hxinitv.
        }
        apply inf_unique with (po := po) (A := ({{cmeet_op0 A, b}})).
        by apply cmeet_prop0. apply lea_is_inf. unfold least. split.
        by []. split. simpl. auto. intros c Hcin. destruct Hcin.
        rewrite H. apply (rel_Rrefl po). by apply cmeet_prop0. destruct H.
        by rewrite H. destruct H.
    }

    { split. unfold subset. intros x Hxin. apply Hxin.
        split. simpl. split. by []. split. rewrite Hseteq. apply HcmeetAin.
        intros x Hxin. unfold cmeet_op'. 

        rewrite HcmeetAle. apply Hreleq. 
        apply HcmeetAinsubpo. by exists x.
        by apply HAin.

        apply cmeet_prop0.
        by apply (subset_trans HAin).  by[]. by exists x.
        intros c Hcin.
        apply inf_ge_lower_bound with (po := subpo) (A := A). apply Hcin.
        split.
        unfold subset. intros. apply H. split. simpl. split.
        by []. split. rewrite Hseteq. apply HcmeetAin.
        intros. unfold cmeet_op'. rewrite HcmeetAle. apply Hreleq.
        apply HcmeetAinsubpo. by exists a0. by apply HAin.
        by apply cmeet_prop0. by exists a0.

        intros. apply Hreleq. by apply H. rewrite Hseteq. apply HcmeetAin.
        apply inf_ge_lower_bound with (po := po) (A := {{cmeet_op0 A, b}}).
        unfold lower_bound. split.  by[]. split. apply Hs_itv_in.
        destruct H. rewrite Hseteq in H0. by apply H0.
        intros a1 Ha1in.
        destruct Ha1in. rewrite H0. apply cmeet_prop0. by[]. 
        assert (Hlbin : lb subpo A ⊆ lb clatt_po0 A).
        { by apply lb_mor_sub. }
        by apply Hlbin.
        
        destruct H0. rewrite H0. apply le_sup with (A := s_itv).
        apply itv_sup. assert (Hlbin : lb subpo A ⊆ s_itv). 
        { unfold s_itv. unfold po. rewrite <-Hseteq. apply lb_in_X. }
        apply Hlbin. by apply H. 
        by destruct H0.
        
        apply cmeet_prop0. by[].
    }
Qed.

(* TODO #5 *)
(* itv_cjoin : the cjoin operator limited on an interval is still cjoin *)
Lemma itv_cjoin 
    (cL : comp_latt T)
    (a : T) (HainX : a ∈ (po_set (clatt_po cL))) 
    (b : T) (HbinX : b ∈ (po_set (clatt_po cL))) 
    (Haleb : (po_rel (clatt_po cL)) a b)
    (subpo : poset T) (Hsubpo : subpo ⊆po clatt_po cL)
    (Hseteq : po_set subpo {=} @itv_set _ (clatt_po cL) a b HainX HbinX Haleb) :
    let cjoin_op' := fun (A : set T) => (cjoin_op cL) ({{cjoin_op cL A, a}}) in
    clatt_join subpo cjoin_op'.
Proof.
    
    assert (HainX_dual : a ∈ (po_set (clatt_po (cL †cL)))).
    { apply HainX. }
    assert (HbinX_dual : b ∈ (po_set (clatt_po (cL †cL)))).
    { apply HbinX. }
    assert (Hblea_dual : po_rel (clatt_po (cL †cL)) b a).
    { apply Haleb. }
    assert (Hsubpo_dual : subpo †po ⊆po clatt_po (cL †cL)).
    { by apply dual_poset_mor_sub. }
    assert (Hseteq_dual : po_set (subpo †po)
        {=} itv_set (clatt_po (cL †cL)) HbinX_dual HainX_dual Hblea_dual).
    { rewrite <-itv_dual_eq. destruct cL. simpl in *.
        rewrite <-itv_dual_dual_eq. apply Hseteq. }

    assert (Hdual := @itv_cmeet (cL †cL) b HbinX_dual a HainX_dual Hblea_dual 
        (subpo †po) Hsubpo_dual Hseteq_dual).
    
    apply Hdual.

Qed.


(* itv_bot : a is the bottom element in { x : a ⊑ x ⊑ b } *)
Lemma itv_bot 
    (cL : comp_latt T)
    (a : T) (HainX : a ∈ (po_set (clatt_po cL))) 
    (b : T) (HbinX : b ∈ (po_set (clatt_po cL))) 
    (Haleb : (po_rel (clatt_po cL)) a b)
    (subpo : poset T) (Hsubpo : subpo ⊆po clatt_po cL)
    (Hseteq : po_set subpo {=} @itv_set _ (clatt_po cL) a b HainX HbinX Haleb) :
    least subpo (po_set subpo) a.
Proof.

    intros. inversion Hsubpo as [Hsetsub Hreleq].
    assert (Hainitv : a ∈ po_set subpo). 
    { apply Hseteq. split. by[]. split. by apply rel_Rrefl. by[]. }
    split. apply subset_refl.
    split. by[]. 
    intros. apply Hreleq. by[]. by[].
    apply ge_inf with (A := po_set subpo).
    rewrite Hseteq. by apply itv_inf. by[]. 
Qed.


(* itv_top : b is the top element in { x : a ⊑ x ⊑ b } *)
Lemma itv_top 
    (cL : comp_latt T)
    (a : T) (HainX : a ∈ (po_set (clatt_po cL))) 
    (b : T) (HbinX : b ∈ (po_set (clatt_po cL))) 
    (Haleb : (po_rel (clatt_po cL)) a b)
    (subpo : poset T) (Hsubpo : subpo ⊆po clatt_po cL)
    (Hseteq : po_set subpo {=} @itv_set _ (clatt_po cL) a b HainX HbinX Haleb) :
    largest subpo (po_set subpo) b.
Proof.
    assert (HainX_dual : a ∈ (po_set (clatt_po (cL †cL)))).
    { apply HainX. }
    assert (HbinX_dual : b ∈ (po_set (clatt_po (cL †cL)))).
    { apply HbinX. }
    assert (Hblea_dual : po_rel (clatt_po (cL †cL)) b a).
    { apply Haleb. }
    assert (Hsubpo_dual : subpo †po ⊆po clatt_po (cL †cL)).
    { by apply dual_poset_mor_sub. }
    assert (Hseteq_dual : po_set (subpo †po)
        {=} itv_set (clatt_po (cL †cL)) HbinX_dual HainX_dual Hblea_dual).
    { rewrite <-itv_dual_eq. destruct cL. simpl in *.
        rewrite <-itv_dual_dual_eq. apply Hseteq. }

    assert (Hdual := @itv_bot (cL †cL) b HbinX_dual a HainX_dual Hblea_dual 
        (subpo †po) Hsubpo_dual Hseteq_dual).
    
    apply Hdual.
Qed.

(* clatt_interval : the interval in a complete lattice also forms a complete lattice *)
Definition clatt_interval 
    (cL : comp_latt T)
    (a : T) (HainX : a ∈ po_set (clatt_po cL)) 
    (b : T) (HbinX : b ∈ po_set (clatt_po cL)) 
    (Haleb : po_rel (clatt_po cL) a b) 
    (subpo : poset T) (Hsubpo : subpo ⊆po clatt_po cL)
    (Hseteq : po_set subpo {=} @itv_set _ (clatt_po cL) a b HainX HbinX Haleb)
    : comp_latt T := 
    mk_complatt (itv_cmeet cL Hsubpo Hseteq) (itv_cjoin cL Hsubpo Hseteq)
        (itv_bot cL Hsubpo Hseteq) (itv_top cL Hsubpo Hseteq).

End DerivedLattice.



Section PosetFunction.

(* We don't set T as the variable, because here we may have functions
    between different Types. *)

(* the definition of a fixpoint *)
Definition fp (T : Type) (X : set T) (f : T -> T) (x : T) := x ∈ X /\ f x = x.

(* set of fixpoints *)
Definition fp_s (T : Type) (X : set T) (f : T -> T) := { x : fp X f x }.

(* fp_s_in_X : fp_s f ⊆ X *)
Lemma fp_s_in_X (T : Type) (X : set T) : forall f, fp_s X f ⊆ X.
Proof.
    unfold fp_s, fp. unfold subset. simpl. intros. apply H.
Qed.

(* pre-fixpoint *)
Definition pre_fp (T : Type) (po : poset T) (f : T -> T) (x : T) := 
    let X := po_set po in
    x ∈ X /\ f x ∈ X /\ po_rel po x (f x).

(* pre-fixpoint set *)
Definition pre_fp_s (T : Type) (po : poset T) (f : T -> T) := 
    { x : pre_fp po f x }.

(* pre_fp_s_in_X : pre_fp_s f ⊆ X *)
Lemma pre_fp_s_in_X (T : Type) (po : poset T) : forall f, pre_fp_s po f ⊆ po_set po.
Proof.
    unfold pre_fp_s. unfold subset. simpl. intros. apply H.
Qed.

(* post-fixpoint *)
Definition post_fp (T : Type) (po : poset T) (f : T -> T) (x : T) := 
    let X := po_set po in
    x ∈ X /\ f x ∈ X /\ po_rel po (f x) x.

(* post-fixpoint set *)
Definition post_fp_s (T : Type) (po : poset T) (f : T -> T) := 
    { x : post_fp po f x }.

(* post_fp_s_in_X : post_fp_s f ⊆ X *)
Lemma post_fp_s_in_X (T : Type) (po : poset T) : forall f, post_fp_s po f ⊆ po_set po.
Proof.
    assert (Hdual := @pre_fp_s_in_X _ (dual_poset po)).
    by apply Hdual.
Qed.

(* fp_in_pre_fp : fp_s f ⊆ pre_fp_s f *)
Lemma fp_in_pre_fp (T : Type) (po : poset T) : forall f, fp_s (po_set po) f ⊆ pre_fp_s po f.
Proof.
    intros f. unfold subset. simpl. intros x Hxin.
    unfold pre_fp. split. apply Hxin. split. destruct Hxin. rewrite H0. apply H.
    destruct Hxin. rewrite H0. apply (rel_Rrefl po). apply H.
Qed.

(* fp_in_post_fp : fp_s f ⊆ post_fp_s f *)
Lemma fp_in_post_fp (T : Type) (po : poset T) : forall f, fp_s (po_set po) f ⊆ post_fp_s po f.
Proof.
    assert (Hdual := @fp_in_pre_fp _ (dual_poset po)).
    by apply Hdual.
Qed.


(* a is the least fixpoint of f greater than x *)
Definition lfp_x (T : Type) (po : poset T) (f : T -> T) (x a : T) := 
    least po ({ y : y ∈ fp_s (po_set po) f /\ po_rel po x y }) a.

(* a is the least fixpoint of f *)
Definition lfp (T : Type) (po : poset T) (f : T -> T) (a : T) := 
    least po (fp_s (po_set po) f) a.
    
(* a is the greatest fixpoint of f smaller than x *)
Definition gfp_x (T : Type) (po : poset T) (f : T -> T) (x a : T) := 
    largest po ({ y : y ∈ fp_s (po_set po) f /\ po_rel po y x }) a.

(* a is the greatest fixpoint of f *)
Definition gfp (T : Type) (po : poset T) (f : T -> T) (a : T) := 
    largest po (fp_s (po_set po) f) a.

(* monotonic *)
Definition monotonic (T T' : Type)
        (po : poset T) (po' : poset T') (f : T -> T') :=
    let X := po_set po in
    let X' := po_set po' in
    (f ~ X |-> X') /\ forall' x ∈ X, forall' y ∈ X, 
        (po_rel po x y -> po_rel po' (f x) (f y)).

(* dual_monotonic : monotonic po po' f -> monotonic (dual_poset po) (dual_poset po') f *)
Lemma dual_monotonic (T T' : Type) (po : poset T) (po' : poset T') (f : T -> T') :
    monotonic po po' f -> monotonic (dual_poset po) (dual_poset po') f.
Proof.
    unfold monotonic. intros Hmono. split.
    by apply Hmono. intros x HxinX y HyinX. by apply Hmono.
Qed.

(* continuous *)
Definition continuous (T T' : Type) 
    (cpo : CPO T) (cpo' : CPO T') (f : T -> T') :=
    let X := po_set (CPO_po cpo) in
    let X' := po_set (CPO_po cpo') in
    (f ~ X |-> X') /\ forall C : set T, 
        chain (CPO_po cpo) C -> chain (CPO_po cpo') (f @ C) /\ 
        f (CPO_join cpo C) = CPO_join cpo' (f @ C).

(* join morphism *)
Definition join_morphism (T T' : Type)
    (L : latt T) (L' : latt T') (f : T -> T') :=
    let X := po_set (latt_po L) in
    let X' := po_set (latt_po L') in
    (f ~ X |-> X') /\ forall' x ∈ X, forall' y ∈ X, 
        f (join_op L x y) = join_op L' (f x) (f y).

(* complete join morphism *)
Definition cjoin_morphism (T T' : Type)
    (cL : comp_latt T) (cL' : comp_latt T') (f : T -> T') :=
    let X := po_set (clatt_po cL) in
    let X' := po_set (clatt_po cL') in
    (f ~ X |-> X') /\ forall' A ⊆ X,
        f (cjoin_op cL A) = cjoin_op cL' (f @ A).

(* extensive *)
Definition extensive (T : Type) (po : poset T) (f : T -> T) := 
    let X := po_set po in
    (f ~ X |-> X) /\ forall' x ∈ X, po_rel po x (f x).

(* reductive *)
Definition reductive (T : Type) (po : poset T) (f : T -> T) := 
    let X := po_set po in
    (f ~ X |-> X) /\ forall' x ∈ X, po_rel po (f x) x.

End PosetFunction.

Add Parametric Morphism {T T': Type} : (@monotonic T T')
    with signature (@poseteq T) ==> (@poseteq T') ==> eq ==> iff as monotonic_mor_eq.
Proof.
    intros P Q HPeqQ M N HMeqN f. unfold monotonic. split.
    { split. rewrite <- HPeqQ. rewrite <-HMeqN. by apply H.
        intros x Hxin y Hyin Hxley. apply HMeqN. apply H. 
        by rewrite HPeqQ. apply H. by rewrite HPeqQ. apply H. by apply HPeqQ.
        by rewrite HPeqQ. apply HPeqQ. by rewrite HPeqQ.
        by rewrite HPeqQ. by[]. }
    { split. rewrite HPeqQ. rewrite HMeqN. by apply H.
        intros x Hxin y Hyin Hxley. apply HMeqN. rewrite HMeqN. apply H.
        by apply HPeqQ. rewrite HMeqN. apply H. by apply HPeqQ. 
        apply H; by apply HPeqQ. }
Qed.         

Section PosetFixpoint.

(* con_is_mono : continuity implies monotonicity *)
Lemma con_is_mono (T T': Type)
        (cpo : CPO T) (cpo' : CPO T')
    : 
    let po := CPO_po cpo in
    let po' := CPO_po cpo' in
    forall f, continuous cpo cpo' f -> monotonic po po' f.
Proof.
    set X := po_set (CPO_po cpo).
    set X' := po_set (CPO_po cpo').
    intros po po' f Hcon. unfold continuous in Hcon. unfold monotonic.
    split. apply Hcon.
    intros x HxinX y HyinX Hxley.
    assert (HxyinX : {{x, y}} ⊆ X).
    { apply bi_ele_in. apply HxinX. apply HyinX. } 
    assert (Hchain : chain po ({{ x , y }})).
    { unfold chain. split. 
        { unfold subset. simpl. intros. destruct H. 
        rewrite H. apply HxinX. destruct H. rewrite H. apply HyinX. destruct H. }
        { apply bi_ele_compare. apply HxinX. apply HyinX. apply Hxley. }
    }
    destruct Hcon.
    destruct (H0 _ Hchain) as [Hchain' Heq]. 
    assert (Hjoinxy_y : CPO_join cpo ({{x, y}}) = y).
    { destruct cpo. simpl. 
        assert (largest po ({{x, y}}) y). 
        { unfold largest. simpl. split. apply HxyinX. split. right. left. auto.
        intros. destruct H1. rewrite H1. apply Hxley. destruct H1. rewrite H1.
        apply (rel_Rrefl po). apply HyinX. destruct H1.
        }
        apply (@sup_unique _ po ({{x, y}})). apply CPO_prop0. apply Hchain.
        apply lar_is_sup. apply H1.
    }
    rewrite Hjoinxy_y in Heq. rewrite Heq.
    destruct cpo'. simpl. apply CPO_prop0. apply Hchain'.
    simpl. exists x. auto.
Qed.

Definition Tarski_lfp (T : Type) (cL : comp_latt T)
    (f : T -> T) (Hfmono : monotonic (clatt_po cL) (clatt_po cL) f) : T 
        := (cmeet_op cL) (post_fp_s (clatt_po cL) f).

(* reference : https://zhuanlan.zhihu.com/p/25674637 *)
(* Tarski_lfp : monotonic f /\ complete lattice X -> lfp f exists in X *)
Theorem Tarski_lfp_prop (T : Type) (cL : comp_latt T)
    (f : T -> T) (Hfmono : monotonic (clatt_po cL) (clatt_po cL) f) : 
    lfp (clatt_po cL) f (Tarski_lfp cL Hfmono).
Proof.
    set po := clatt_po cL.
    set X := po_set (clatt_po cL).
    set u := (cmeet_op cL) (post_fp_s (clatt_po cL) f).
    destruct cL. simpl in *.
    assert (HuinX : u ∈ X). { apply cmeet_prop0. apply post_fp_s_in_X. }
    assert (Hfuup : lower_bound po (post_fp_s po f) (f u)).
    { split. apply post_fp_s_in_X. split. apply Hfmono. apply HuinX.
        intros a Hain. 
        assert (HainX : a ∈ X). { apply (post_fp_s_in_X Hain). } 
        assert (Halefa : po_rel po (f a) a). { apply Hain. }
        refine (rel_Rtrans po (f u) _ (f a) _ a _ _ _).
        by apply Hfmono. by apply Hfmono. by [].
        apply Hfmono. by []. by []. apply cmeet_prop0. apply post_fp_s_in_X. 
        by apply Hain. by apply Halefa.
    }
    assert (Hfuleu : po_rel po (f u) u).
    { apply cmeet_prop0. apply post_fp_s_in_X. apply Hfuup. }
    assert (Huin : u ∈ post_fp_s po f).
    { simpl. unfold post_fp. split. by [].
        split. by apply Hfmono. by apply Hfuleu. }
    assert (Hfuin : f u ∈ post_fp_s po f).
    { simpl. unfold post_fp. split. by apply Hfmono. split. apply Hfmono. by apply Hfmono.
      apply Hfmono. by apply Hfmono. by []. by []. }
    assert (Hulefu : po_rel po u (f u)).
    { apply cmeet_prop0. apply post_fp_s_in_X. apply Hfuin. }
    
    unfold lfp. unfold fp_s. unfold least.
    split. by apply fp_s_in_X. split. simpl. unfold fp. split. by []. apply (rel_Rasymm po).
    by apply Hfmono. by []. by[]. by[].

    intros a Hain. apply cmeet_prop0. apply post_fp_s_in_X.
    apply fp_in_post_fp. apply Hain.
Qed. 

Definition Tarski_gfp (T : Type) (cL : comp_latt T)
    (f : T -> T) (Hfmono : monotonic (clatt_po cL) (clatt_po cL) f) : T 
        := (cjoin_op cL) (pre_fp_s (clatt_po cL) f).

Theorem Tarski_gfp_prop (T : Type) (cL : comp_latt T)
    (f : T -> T) (Hfmono : monotonic (clatt_po cL) (clatt_po cL) f) : 
    gfp (clatt_po cL) f (Tarski_gfp cL Hfmono).
Proof.
    assert (Hfmono' := dual_monotonic Hfmono).
    assert (Hdual := Tarski_lfp_prop (dual_clatt cL) Hfmono').
    intros. apply Hdual.
Qed.

Lemma clat_f_range (T : Type) (cL : comp_latt T) (f : T -> T)
    (Hmono : monotonic (clatt_po cL) (clatt_po cL) f) 
    (S : set T) (HS_in_fps : S ⊆ fp_s (po_set (clatt_po cL)) f) 
    (Hain : (cjoin_op cL) S ∈ (po_set (clatt_po cL)))
    (Hbin : clatt_top cL ∈ (po_set (clatt_po cL)))
    (Haleb : (po_rel (clatt_po cL)) ((cjoin_op cL) S) (clatt_top cL)): 
    let W := ub (clatt_po cL) S in
    let subpo := sub_poset (clatt_po cL) (@ub_in_X _ _ S) in
    monotonic subpo subpo f.
Proof.
    intros.
    destruct cL. simpl in *.
    unfold monotonic. split. 
    
    assert (HSinX : S ⊆ po_set clatt_po0).
    { rewrite HS_in_fps. apply fp_s_in_X. }

    unfold is_set_f. intros. simpl. simpl in H. destruct H as [_ [Hxin Hxub]].
    split. by[]. split. by apply Hmono. intros c Hcin.
    apply (rel_Rtrans clatt_po0) with (y := f c). by apply HSinX. apply Hmono.
    by apply HSinX. by apply Hmono. apply HS_in_fps in Hcin. destruct Hcin. rewrite H0.
    by apply rel_Rrefl. apply Hmono. by apply HSinX. by[]. by apply Hxub.

    intros x Hxin y Hyin Hxley. apply Hmono. apply Hxin. apply Hyin. apply Hxley.
Qed.

End PosetFixpoint.

(*
(* TODO #4 *)
Theorem Tarski_fp_clat (T : Type) (cL : comp_latt T) (f : T -> T) 
    (Hmono : monotonic (clatt_po cL) (clatt_po cL) f) :
    exists cL' : comp_latt T, po_set (clatt_po cL') {=} fp_s (po_set (clatt_po cL)) f 
                    /\ po_rel (clatt_po cL') =r po_rel (clatt_po cL).
Proof.
    
    set clatt_po0 := clatt_po cL.
    set cmeet_op0 := cmeet_op cL.
    set cmeet_prop0 := cmeet_prop cL.
    set cjoin_op0 := cjoin_op cL.
    set cjoin_prop0 := cjoin_prop cL.
    set clatt_bot0 := clatt_bot cL.
    set clatt_bot_prop0 := clatt_bot_prop cL.
    set clatt_top0 := clatt_top cL.
    set clatt_top_prop0 := clatt_top_prop cL.

    set X := po_set clatt_po0.
    set po := clatt_po0.
    set X' := fp_s X f.
    assert (HX'in : X' ⊆ X). { apply fp_s_in_X. }
    set po' := sub_poset po HX'in.

    set _lfp := Tarski_lfp cL Hmono.

    set cjoin_op' := fun A => 

        let 
        Tarski_lfp Wclat HWmono 
        cjoin_op0 ({{ cjoin_op0 A, _lfp }}).

    assert (Hjoin : clatt_join (sub_poset po HX'in) cjoin_op').
    {   intros S HSin.
        set W := up_s po ({{cjoin_op0 S}}).
        assert (HSinX : S ⊆ X). 
        { transitivity X'. by []. apply fp_s_in_X. }
        assert (HWinX : W ⊆ X). { apply up_s_in_X. }
        assert (HWequbS : W {=} ub po S). 
        { apply up_s_sup_is_ub. apply cjoin_prop0. transitivity (po_set po').
            apply HSin. apply HX'in. }
        assert (HSlea : least po W (cjoin_op0 S)).
        { apply lea_point_up_s. by apply cjoin_prop0. }
        assert (HSinf : infimum po W (cjoin_op0 S)). { by apply lea_is_inf. }
        assert (HinfW_eq_supS : cmeet_op0 W = cjoin_op0 S).
        { apply (@inf_unique _ po W). apply cmeet_prop0. apply up_s_in_X. apply HSinf. }

        assert (HinfW_in : cmeet_op0 W ∈ W).
        { rewrite HinfW_eq_supS. simpl. split. apply cjoin_prop0. by [].
            exists (cjoin_op0 S). split. left. auto. apply (rel_Rrefl po). by apply cjoin_prop0. }
        
        About itv_set.

        assert (HainX : cjoin_op0 S ∈ po_set po). { apply cjoin_prop0. apply HSinX. }
        assert (HbinX : clatt_top0 ∈ po_set po). { apply clatt_top_prop0. }
        assert (Haleb : (po_rel po) (cjoin_op0 S) clatt_top0). { apply clatt_top_prop0. 
            apply cjoin_prop0. apply HSinX. }
        assert (HWisitv : W {=} itv_set po HainX HbinX Haleb).
        { unfold W. apply subset_eq. split.
            { unfold subset. intros x Hxin. simpl. split. apply Hxin. split.
            simpl in Hxin. destruct Hxin as [Hxin [a Ha]]. destruct Ha.
            destruct H. by rewrite H in H0. by destruct H.
            apply clatt_top_prop0. apply Hxin. }
            { unfold subset. intros x Hxin. simpl. split. apply Hxin.
                exists (cjoin_op0 S). split. auto. apply Hxin. } 
        }

        assert (HsupW_larX : largest po X (cjoin_op0 W)).
        {   
            assert (HjoinW : cjoin_op0 W = clatt_top0).
            { apply sup_unique with (po:=po)(A:=W). apply cjoin_prop0.
                apply up_s_in_X. rewrite HWisitv. apply itv_sup. }
            rewrite HjoinW. apply clatt_top_prop0.
        }
        
        assert (HsupW_in : cjoin_op0 W ∈ W).
        { simpl. split. apply cjoin_prop0. apply up_s_in_X. exists (cjoin_op0 S).
            split. auto. apply HsupW_larX. by apply cjoin_prop0. }
        
        assert (Hsubposub : sub_poset po HWinX ⊆po clatt_po cL).
        { apply sub_poset_sub. }
        assert (Wclat : exists cL' : comp_latt T, clatt_po cL' =po sub_poset po HWinX).
        {  
            assert (Hsubpoeq : po_set (sub_poset po HWinX) {=} itv_set po HainX HbinX Haleb).
            { by simpl. }
            exists (clatt_interval cL Hsubposub Hsubpoeq).
            split. unfold subclatt. unfold clatt_interval. simpl. reflexivity.
            unfold clatt_interval. by simpl.
        }
        assert (HfonW : f ~ W |-> W).
        { 
            unfold is_set_f. intros. rewrite HWequbS. simpl.

            (* prove by x ∈ ub po S*)
            rewrite HWequbS in H. destruct H as [_ [Hxin Hxub]].
            split. apply HSinX. split. apply Hmono. apply Hxin. intros c Hcin.
            apply (rel_Rtrans po) with (y := f c).
            by apply HSinX. apply Hmono. by apply HSinX. apply Hmono. apply Hxin.
            apply HSin in Hcin. simpl in Hcin. unfold fp in Hcin. 
            destruct Hcin as [? Hcfp]. rewrite Hcfp. apply rel_Rrefl. apply H.
            apply Hmono. by apply HSinX. by apply Hxin. by apply Hxub. 
        }

        destruct Wclat as [Wclat HWclat].

        assert (Hmono' : monotonic (clatt_po Wclat) (clatt_po Wclat) f).
        { rewrite HWclat. split. apply HfonW. intros x Hxin y Hyin Hxley. apply Hmono.
            apply HWinX. by apply Hxin. apply HWinX. by apply Hyin. apply Hxley.  }

        set Wlfp := Tarski_lfp Wclat Hmono'.

        assert (Heq : cjoin_op' S = Wlfp).
        { unfold cjoin_op', Wlfp.  }
        
        
        
        
        

    }



*)


(* ################################################################# *)
(** ** Examples *)

(** Here we consider two examples, using the module we have built. *)

Section PosetExamples.

(** Generally we avoid the used of [LEM] (Law of Excluded Middle), which will 
    damage the calculable property. However, in some situations the problem 
    itself is undecidable. In these cases will may have to use LEM in our proof. *)

Hypothesis H_LEM : LEM.

(** *** Finite Lattice *)

Section FiniteLattice.

(** The first example is a finite lattice with four points. *)

(*    Its Hasse graph looks like this.
 
        D
       / \
      /   \
     B     C
      \   /
       \ /
        A
*)


(** In the following we define the points the partial order. *)

Inductive Point := A | B | C | D .

Definition PointRel : relation Point :=
    fun (p q : Point) =>
    match p, q with
    | A, A => True
    | B, B => True
    | C, C => True
    | D, D => True
    | A, B => True
    | A, C => True
    | B, D => True
    | C, D => True
    | A, D => True
    | _, _ => False
    end.

Definition PointPo : poset Point.
Proof.
    refine (@mk_poset Point 𝕌 PointRel _ _ _).
    { unfold Rrefl, PointRel. intros. by destruct t. }
    { unfold Rtrans, PointRel. intros x _ y _ z _. destruct x,y,z; auto. }
    { unfold Rasymm, PointRel. intros x _ y _. 
        destruct x, y; auto; intros; contradiction. }
Defined.

(** This is a monotonic function on [Point]. *)

Definition f : Point -> Point :=
    fun (x : Point) =>
    match x with
    | A => B
    | B => B
    | C => D
    | D => D
    end.

(** And here is the proof for the monotonicity of [f]. *)
Lemma f_mono : monotonic PointPo PointPo f.
Proof.
    unfold monotonic. split.
    { unfold is_set_f. unfold PointPo; simpl. auto. }
    { intros x Hxin y Hyin Hxley. unfold PointPo; simpl. unfold f. 
        by destruct x, y. }
Qed.

(** There's no doubt that the partial order [Point] is a *complete lattice* 
    since it is finite. How do we prove this fact here in Coq? An apparent
    approach is to directly construct the *meet* and *join* operator, and
    prove the corresponding properties. But unfortunately, we here we cannot
    nominate the operator. Because we have chosen [Prop] to model the set,
    it is not always calculable. *)

Definition PointMeet : set Point -> Point.

Abort.


(** In fact, we can construct such an example:

    [S := { x : x = A /\ (some predicate formula) }],

    and in general it's impossible to determine whether S is an empty set,
    because arbitrary predicate formula can appear in the description of the
    set.

    Therefore, to obtain the high expressive model as desired in maths, we 
    have totally given up the ability of automation.

    But it is not necessary to mention the operators in order to prove a
    complete lattice. The condition of being a complete lattice is "every
    subset has the supremum (resp. infimum)", and it is slightly different
    (at least in Coq) from "there is an operator matching every subset to its
    supremum (resp. infimum)". In other words,

    [exists f : set T -> T, forall' X ⊆ po, supremum po X (f X)]

    [forall' X ⊆ po, exists x : T, supremum po X x]

    are different. The former one requires the calculability of supremum and 
    infimum.
*)

(** Here we prove [Point] is join-complete, without the construction of join
    operator. Note that *LEM* is applied here. *)


Lemma test : forall' Y ⊆ PointPo, exists x, supremum PointPo Y x.
Proof.
    intros Y HYin. 
    destruct (H_LEM (D ∈ Y)) as [HDin | HnDin].

    (** if D ∈ Y  *)
    exists D. unfold supremum. unfold least. split. apply ub_in_X.
    split. simpl. split. by[]. split. by apply HYin. 
    intros a _. by destruct a. intros a Hain. by apply Hain.

    (** if ¬ D ∈ Y *) 
    destruct (H_LEM (B ∈ Y /\ C ∈ Y)) as [[HBin HCin] | HnBCin].

    (**      if B ∈ Y /\ C ∈ Y *)
    exists D. unfold supremum. unfold least. split. apply ub_in_X.
    split. simpl. split. by[]. split. by unfold PointPo; simpl.
    intros a _. by destruct a. intros a Hain. simpl in Hain. 
    destruct Hain as [_ [_ Hle_a]]. 
    { destruct a. by destruct (Hle_a B). by destruct (Hle_a C).
        by destruct (Hle_a B). reflexivity. }

    (**      if ¬ (B ∈ Y /\ C ∈ Y) *)
    destruct (H_LEM (B ∈ Y)) as [HBin | HnBin].

    (**          if B ∈ Y , then ¬ C ∈ Y *)
    exists B. unfold supremum. unfold least. split. apply ub_in_X.
    split. simpl. split. by[]. split. by apply HYin.
    intros a Hain. unfold PointPo; simpl. destruct a. by []. by [].
    destruct (HnBCin (conj HBin Hain)). by destruct HnDin.
    intros a Hain. destruct a. by apply Hain. by []. by apply Hain. by [].

    (**              if ¬ B ∈ Y *)
    destruct (H_LEM (C ∈ Y)) as [HCin | HnCin].

    (**              if C ∈ Y *)
    exists C. unfold supremum. unfold least. split. apply ub_in_X.
    split. simpl. split. by[]. split. by apply HYin.
    intros a Hain. unfold PointPo; simpl. destruct a. by []. by [].
    by []. by destruct HnDin.
    intros a Hain. destruct a. by apply Hain. by apply Hain. by []. by apply Hain.

    (**              if ¬ C ∈ Y *)
    destruct (H_LEM (A ∈ Y)) as [HAin | HnAin].

    (**              if A ∈ Y *)
    exists A. unfold supremum. unfold least. split. apply ub_in_X.
    split. simpl. split. by[]. split. by apply HYin.
    intros a Hain. unfold PointPo; simpl. destruct a. by []. by destruct HnBin.
    by destruct HnCin. by destruct HnDin.
    intros a Hain. by destruct a.

    (** in this case, Y is empty *)
    exists A. unfold supremum. unfold least. split. apply ub_in_X.
    split. simpl. split. by[]. split. by unfold PointPo.
    intros a Hain. by destruct a; contradiction.
    intros a Hain. by destruct a.
Qed.

(** This property can also be proved by arguing that it is a "finite" lattice.
    That is, we can construct a theorem saying that every *finite* lattice is 
    a complete lattice. *)


(** Can we prove this fact without using LEM? I believe the answer is positive. *)

End FiniteLattice.

(** *** Natural Number Lattice *)

(** The next example is [Ncl], the complete lattice of natural number. *)

Section NumberCompleteLattice.

(** It consists of either a natural number or the infinity. *)
Inductive Ncl :=
| Num (n : nat)
| Infty.

(** This relation extends [Nat.le] to include infinity. *)
Definition Ncl_le : relation Ncl := 
    fun (a b : Ncl) => 
    match b with
    | Infty => True
    | Num nb => match a with
                | Infty => False
                | Num na => le na nb
                end
    end.

(** We prove that the [Ncl] set equipped with [Ncl_le] is a poset. (In other
    words, prove the reflexivity, transivity and anti-symmetry properties of
    [Ncl_le]. )*)

Definition Nclpo : poset Ncl.
Proof.
    refine (@mk_poset Ncl 𝕌 Ncl_le _ _ _).
    (** reflexivity *)
    { unfold Rrefl, Ncl_le. intros t _. by destruct t. }
    (** transitivity *)
    { unfold Rtrans, Ncl_le.  
        intros [x|] _ [y|] _ [z|] _; auto. apply transitivity.
        intros; contradiction. }
    (** anti-symmetry *)
    { unfold Rasymm, Ncl_le. intros [x|] _ [y|] _; auto.
        intros. assert (Heq : x = y). { by apply antisymmetry. }
        by rewrite Heq. intros; contradiction. intros; contradiction. }
Defined.

(** The [NclMax] and [NclMin] extend [Nat.max] and [Nat.min]. The are actually
    the *join* and *meet* operators. But again, we cannot nominate the operators
    mapping from sets to their supremum of infimum.*)

Definition NclMax (a b : Ncl) : Ncl :=
    match a, b with
    | Infty, _ => Infty
    | _, Infty => Infty
    | Num na, Num nb => Num (max na nb)
    end.

Definition NclMin (a b : Ncl) : Ncl :=
    match a, b with
    | Infty, b' => b'
    | a', Infty => a'
    | Num na, Num nb => Num (min na nb)
    end.

(** The proof that [Ncl] forms a lattice, with the [NclMin] and [NclMax]
    operators defined. *)

Definition Nclla : latt Ncl.
Proof.
    refine (@mk_latt _ Nclpo NclMin _ NclMax _).
    (** proof of meet property*)
    { unfold latt_meet, NclMin. intros x y. 
        destruct x, y; apply lea_is_inf; apply bi_ele_lea; try by[].

        (** the case of two integers needs special explanation *)
        unfold Nclpo; simpl. apply Nat.le_min_l.
        unfold Nclpo; simpl. apply Nat.le_min_r.
        simpl. assert (Htemp := Nat.min_spec n n0).
        destruct Htemp as [[_ ?] | [_ ?]].
        left. by f_equal. right. left. by f_equal.

        simpl. by left. simpl. by right; left. simpl. by left.
    }

    (** proof of join property *)
    {
        unfold latt_join, NclMin. intros x y. 
        destruct x, y; apply lar_is_sup; apply bi_ele_lar; try by[].
        (** the case of two integers needs special explanation *)
        unfold Nclpo; simpl. apply Nat.le_max_l.
        unfold Nclpo; simpl. apply Nat.le_max_r.
        simpl. assert (Htemp := Nat.max_spec n n0).
        destruct Htemp as [[_ ?] | [_ ?]].
        right; left; by f_equal. left; by f_equal.

        simpl. by right; left. simpl. by left. simpl. by left.
    }
Defined.

(** We can prove that [Nclla] is a complete lattice, by case analysis of 
    whether the set is finite or not.
    - if the set is infinite, then the supremum is [Infty].
    - if the set is finite, then the supremum is the largest element in it
        (in this case the largest element is well-defined). *)

Lemma Nclpo_complete : complete_lattice Nclla.
Proof.
    unfold complete_lattice.
    intros A HAin. split. 

    destruct (H_LEM (set_finite A)) as [HAfin | HAinf]. 

    (* if A is a finite set *)
    assert (Hlist : forall l : list Ncl, exists i, infimum Nclla (list_2_set l) i).
    { induction l.
        - exists Infty. simpl. rewrite inf_em. split. 
            by[]. split. by[]. intros a _. by destruct a.
        - destruct IHl as [i0 Hi0]. exists (NclMax i0 a).
            unfold infimum, largest. simpl. split.
            apply lb_in_X. split. split. unfold union, subset.
            simpl. by intros. split. by unfold NclMax. intros b Hbin.
            simpl in Hbin. unfold Nclpo, NclMax; simpl. destruct Hbin.
            destruct H.
Abort.



End NumberCompleteLattice.

End PosetExamples.


*)

