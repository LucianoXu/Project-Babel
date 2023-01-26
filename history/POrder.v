(** ################################################# **)
(* set related *)

Reserved Notation " A ⊆po B " (at level 60).
Reserved Notation " cL1 '=cL' cL2 " (at level 60).
Reserved Notation " L1 '⊆cL' L2 " (at level 60).

(** subrelation 
    R1 is the sub relation of R2 *)
Module SubRel.
Record type {T : Type} {A B : 𝒫(T)} 
    (R1 : relation A) (R2 : relation B) : Prop := Pack {
    AinB : A ⊆ B;
    subrel : forall x y, R1 x y <-> R2 [x in AinB] [y in AinB];
}.
Module Exports.
Notation subRel := type.
End Exports.

End SubRel.
Export SubRel.Exports.

(** get the subrelation *)
Definition rel_restrict {T : Type} {A B : 𝒫(T)} (R : relation B)
    (HAB : A ⊆ B) : relation A :=
    fun x y => R [x in HAB] [y in HAB].

Lemma rel_restrict_sub {T : Type} {A B : 𝒫(T)} (R : relation B) (HAB : A ⊆ B) :
    subRel (rel_restrict R HAB) R.
Proof. rewrite /rel_restrict. econstructor => x y. reflexivity. Qed.



(** subposet, base on sub relation 
    (This part of theory only works for sets, not for types) *)
Definition subposet {T : Type} {A B : 𝒫(T)} 
    (po1 : poset A) (po2 : poset B) : Prop :=
    subRel (Poset.o_rel po1) (Poset.o_rel po2).
Notation " A ⊆po B " := (subposet A B).


(** If a relation is a [order], then any subrelations of ia must also be 
    [order]s. *)
Lemma sub_order {T : Type} {A B : 𝒫(T)} (R1 : relation A) (R2 : relation B)
    (HsubR : subRel R1 R2) : order _ R2 -> order _ R1.
Proof. move => H. destruct HsubR. constructor.
    rewrite /reflexive => x. rewrite subrel. by apply H.
    rewrite /transitive => x y z. rewrite !subrel. by apply H.
    rewrite /antisymmetric => x y. rewrite !subrel => Hxy Hyx. 
    apply (eq_in_subset AinB). by apply H.
Qed.

(* get a subposet from a existing poset *)
Definition poset_restrict {T : Type} {A B : 𝒫(T)} (po : poset B) (HAB : A ⊆ B) :
    poset A := Poset _ (posetMixin 
        (sub_order (rel_restrict_sub (Poset.o_rel po) HAB) (poset_order po))).

Definition poset_restrict_sub {T : Type} {A B : 𝒫(T)} (po : poset B) 
    (HAB : A ⊆ B) : poset_restrict po HAB ⊆po po.
Proof. rewrite /poset_restrict /subposet //=. by apply rel_restrict_sub. Qed.



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















(*###################################################*)
(** ** about singleton *)

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



(*

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
*)


(*

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
*)















(*


(* dual_rel_inv : x ⊑ y -> x ⊑ y (in the dual relation) *)
Lemma dual_rel_inv {x y : T} {r : relation T} (Hxley : r x y)
        : (r †r) y x.
Proof. apply Hxley. Qed.


Lemma dual_dual_releq (X : set T) (f : relation T) : f †r †r =r(X) f.
Proof. unfold dual_rel, releq. by intros. Qed.


Lemma dual_dual_poseteq (po : poset) : po †po †po =po po.
Proof.
    unfold dual_poset, poseteq. simpl. split. by[]. by apply dual_dual_releq.
Qed.

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


(*
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
*)

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

*)