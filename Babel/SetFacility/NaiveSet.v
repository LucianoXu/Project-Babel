(** * NaiveSet.v : The general naive set theory. *)


From Babel Require Import TerminalDogma.premises 
                          TerminalDogma.Extensionality.


From Coq Require Import Classical Relations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* ################################################################# *)


(** *** Reserved Notations for naive_set *)
Declare Scope NSet_scope.
Open Scope NSet_scope.

Reserved Notation " '𝒫(' T ) " (format "'𝒫(' T )").
Reserved Notation " s '∈' S " (at level 50).
Reserved Notation " s '∉' S " (at level 50).
Reserved Notation " {  expr , x .. y | cond  } " (x binder, at level 0, expr at level 99).
Reserved Notation "∅".
Reserved Notation " '𝒫(' T ')₊' ".
Reserved Notation "'𝕌'".
Reserved Notation " A '⊆' B " (at level 49).
Reserved Notation " A '⊇' B " (at level 49).
Reserved Notation " A '∪' B " (at level 43).
Reserved Notation " A '∩' B " (at level 42).
Reserved Notation " '∁' A" (at level 39). 

Reserved Notation "⋃".
Reserved Notation "⋂".
Reserved Notation " f [<] " (at level 11, right associativity).
Reserved Notation " F [>] " (at level 11, right associativity).
Reserved Notation " F [<<] " (at level 11, right associativity).
Reserved Notation " F [><] " (at level 11, right associativity).

(** TODO #11 *)
Reserved Notation "'forall'' x '∈' A , expr" (at level 80, x at level 20, A at level 80, expr at level 80).
Reserved Notation "'exists'' x '∈' A , expr" (at level 80, x at level 20, A at level 80, expr at level 80).
Reserved Notation "'forall'' A '⊆' B , expr" (at level 80, A at level 20, B at level 80, expr at level 80).
Reserved Notation "'exists'' A '⊆' B , expr" (at level 80, A at level 20, B at level 80, expr at level 80).

Reserved Notation " {{ x , .. , y }} " (at level 20).

(* ################################################################# *)

(** ** Set Definition *)

(** The equivalence between predicates. *)
Lemma predeqP {T : Type} (p q : T -> Prop) : p = q <-> (forall x, p x <-> q x).
Proof. split.
    by move => ->.
    move => H. apply functional_extensionality => x.
    apply propositional_extensionality. by apply H.
Qed.

(** powerset 
    The type [powerset T] is indeed the power powerset of T, because every element of it
    has the [chac] function, which corresponds to a [sig] type. And the [sig]
    type further corresponds to subsets in maths. *)
Record powerset (T : Type) := mk_set { 
    chac : T -> Prop;
}.
(** This notation means 'power set'. *)
Notation " '𝒫(' T ) " := (powerset T) (format "'𝒫(' T )") : NSet_scope.
Notation " s '∈' S " := ((chac S) s) : NSet_scope.
Notation " s '∉' S " := (~ s ∈ S) : NSet_scope.
Notation "{  x : A | P  }" := (mk_set (T:=A) (fun x => P)) : NSet_scope.
Notation "{  x | P  }" := (mk_set (fun x => P)) : NSet_scope.
Notation "{ expr , x .. y | cond }" :=
    { a | (exists x, .. (exists y, cond /\ a = expr ) ..) } : NSet_scope.

Notation "'forall'' x '∈' A , expr" := (forall x , x ∈ A -> expr) : NSet_scope.
Notation "'exists'' x '∈' A , expr" := (exists x , x ∈ A /\ expr) : NSet_scope.
        
        
(** TODO We should add a lemma to move the binder right and left in the set description 
    { f a b , a b | a ∈ A /\ b ∈ B } = { f a [<] B , a | a ∈ A }
*)

(** The equivalence between sets. *)
Lemma seteq_predP {T : Type} (A B : 𝒫(T)) : A = B <-> chac A = chac B.
Proof. split. by move => ->. destruct A, B => /= -> //. Qed.

(** The equivalence between sets (2). *)
Lemma seteqP {T : Type} (A B : 𝒫(T)) : 
    A = B <-> (forall x, x ∈ A <-> x ∈ B).
Proof. 
    split. by move => ->. 
    move => H. by apply /seteq_predP /predeqP.
Qed.

(** This one needs classical logic. *)
Lemma setneqP {T : Type} (A B : 𝒫(T)) : 
    A <> B <-> ((exists x, x ∈ A /\ x ∉ B) \/ (exists x, x ∈ B /\ x ∉ A)).
Proof. split.
    move => HAneqB. apply NNPP => H. apply HAneqB.
    apply not_or_and in H. destruct H as [H1 H2].
Admitted.


(** The set we defined can be converted into a sigma type, which corresponds to
    the subset in type system. *)
Coercion set2sigma (T : Type) (A : 𝒫(T)) : Type := sig (chac A).


Lemma belongs_to [T : Type] : forall (A : 𝒫(T)) (a : A), proj1_sig a ∈ A.
Proof. move => A a. by apply (proj2_sig a). Qed.


(** The empty set. *)
Definition set_em (T : Type) : 𝒫(T) := { x | False }.
Notation "∅" := (set_em _).


(** The universal set (of type T). *)
Definition set_uni (T : Type) : 𝒫(T) := { x | True }.
Notation "'𝕌'" := (set_uni _).

Lemma in_set_em_F [T : Type] : 
    forall (A : 𝒫(T)) (x : T), x ∈ A -> A = ∅ -> False.
Proof. move => A x Hx HA. rewrite HA in Hx. by destruct Hx. Qed.


(** The set is nonempty *)
Lemma nonemptyP {T : Type} (A : 𝒫(T)) :  A <> ∅ <-> exists x, x ∈ A.
Proof. split; last first.

    move => [x Hx] H. move: Hx H. by apply in_set_em_F.

    move => HA. apply NNPP => /(not_ex_all_not _ _) H.
    apply HA. apply /seteqP => x. split.
    by move => Hx; apply (H x).
    by move => [].

Qed.

(*##########################################################*)
(** type of nonempty set *)
Module NemSet.
Section ClassDef.

Definition mixin_of (T : Type) (A : 𝒫(T)) := A <> ∅.
Definition class_of := mixin_of.


Structure type (T : Type) := Pack {
    set : 𝒫(T);
    _ : class_of set;
}.

Variable (T : Type) (cT : type T).

Definition class := let: Pack _ c := cT return class_of (set cT) in c.

Definition pack := Pack.

End ClassDef.

Module Exports.
#[reversible] Coercion set : type >-> powerset.
Arguments class [T] cT.

Notation nemset := type.
Notation " '𝒫(' T ')₊' " := (type T) (format "'𝒫(' T )₊") : NSet_scope.

Notation NemSet T m := (@pack _ T m).
Notation "[ 'nemset' 'of' T ]" := (T : type _)
  (at level 0, format "[ 'nemset'  'of'  T ]") : NSet_scope.

(** This item returns [ ∃ x : _, x ∈ T ] directly. *)
Notation "[ 'nemset_witness' 'of' T ]" := 
    (iffLR (@nonemptyP _ _ ) (class T))
    (at level 0, format "[ 'nemset_witness'  'of'  T ]") : NSet_scope.

End Exports.

End NemSet.
Export NemSet.Exports.



(** subset relation *)
Definition subset {T : Type} (A B : 𝒫(T)) : Prop :=
    forall x, x ∈ A -> x ∈ B.
Notation " A '⊆' B " := (subset A B) : NSet_scope.

(** supset relation, which is dual to subset *)
Definition supset {T : Type} (A B : 𝒫(T)) : Prop := B ⊆ A.
Notation " A '⊇' B " := (supset A B) : NSet_scope.

Notation "'forall'' A '⊆' B , expr" := (forall A , A ⊆ B -> expr) : NSet_scope.
Notation "'exists'' A '⊆' B , expr" := (exists A , A ⊆ B /\ expr) : NSet_scope.
    
Lemma subsupP {T : Type} (A B : 𝒫(T)) : A ⊆ B <-> B ⊇ A.
Proof. split; auto. Qed.

Lemma set_belong_cut {T : Type} (A B : 𝒫(T)) (x : T):
    x ∈ B -> B ⊆ A -> x ∈ A.
Proof. move => Hxin HBinA. apply HBinA. by apply Hxin. Qed.
Arguments set_belong_cut {_} [_] _.

(* 
Lemma set_trichotomy {T : Type} (A B : 𝒫(T)) :
    A = B \/ A ⊆ B \/ A ⊇ B.
Proof.
*)

(** subset relation *)

(** subset_refl : A ⊆ A *)
Lemma subset_refl {T : Type}: reflexive _ (@subset T).
Proof. unfold reflexive, subset. auto. Qed.

(** subset_trans : A ⊆ B -> B ⊆ C -> A ⊆ C *)
Lemma subset_trans {T : Type}: transitive _ (@subset T).
Proof.
    unfold transitive, subset. 
    intros A B C HAinB HBinC. intros x HxinA.
    apply HBinC. apply HAinB. apply HxinA.
Qed.

(** subset_asymm : A ⊆ B -> B ⊆ A -> A = B *)
Lemma subset_asymm {T : Type}: antisymmetric _ (@subset T).
Proof.
    rewrite /antisymmetric => A B HAinB HBinA.
    apply /seteqP => x. split.
    by apply HAinB. by apply HBinA.
Qed.

Add Parametric Relation {T : Type} : _ (@subset T)
    reflexivity proved by (@subset_refl T)
    transitivity proved by (@subset_trans T)
    as subset_rel.

(** supset relation *)

Lemma supset_refl {T : Type}: reflexive _ (@supset T).
Proof. unfold reflexive, supset, subset. auto. Qed.


Lemma supset_trans {T : Type}: transitive _ (@supset T).
Proof.
    unfold transitive, supset, subset. 
    intros A B C HBinA HCinB. intros x HxinC.
    apply HBinA. apply HCinB. apply HxinC.
Qed.

Lemma supset_asymm {T : Type}: antisymmetric _ (@supset T).
Proof.
    rewrite /antisymmetric => A B HAinB HBinA.
    apply /seteqP => x. split.
    by apply HBinA. by apply HAinB.
Qed.
    
Add Parametric Relation {T : Type} : _ (@supset T)
    reflexivity proved by (@supset_refl T)
    transitivity proved by (@supset_trans T)
    as supset_rel.


(** tranform an element into the super set *)
Definition into_supset {T : Type} {A B : 𝒫(T)} (a : A) (HAB : A ⊆ B) : B.
Proof. 
    destruct a.
    rewrite /set2sigma. refine (exist _ x _). by apply HAB.
Defined.

Notation "[ a 'in' HAB ]" := (into_supset a HAB) : NSet_scope.

Lemma eq_in_subset {T : Type} {A B : 𝒫(T)}  
    (x y : A) (HAB : A ⊆ B) : [x in HAB] = [y in HAB] -> x = y.
Proof.
    rewrite /into_supset => H.
    destruct x as [x0 Hx0in], y as [y0 Hy0in].
    inversion H. move : Hx0in Hy0in H. rewrite H1.
    move => Hx0in Hy0in _. replace Hx0in with Hy0in => //.
    by apply proof_irrelevance.
Qed.
Arguments eq_in_subset {T A B} [x y] (HAB).


(** subset_em : ∅ ⊆ A *)
Lemma em_subset {T : Type}: forall (A : 𝒫(T)), ∅ ⊆ A.
Proof. by move => ?. Qed.

Lemma subset_emP {T : Type}: forall (A : 𝒫(T)), A ⊆ ∅ <-> A = ∅.
Proof.
    move => A. split.
    move => HAin. apply /seteqP => x. split.
    by apply HAin. by move => [].
    by move => ->.
Qed.

Lemma subset_uni {T : Type}: forall (A : 𝒫(T)), A ⊆ 𝕌.
Proof. by move => ?. Qed.

Lemma uni_subsetP {T : Type}: forall (A : 𝒫(T)), 𝕌 ⊆ A <-> A = 𝕌.
Proof.
    move => A. split.
    move => HAin. apply seteqP => x. split.
    by []. by apply HAin. by move => ->.
Qed.


(* some calculations between sets *)
Definition union {T : Type} (A B : 𝒫(T)) : 𝒫(T) := { x | x ∈ A \/ x ∈ B }.
Notation " A '∪' B " := (union A B) : NSet_scope.

Definition itsct {T : Type} (A B : 𝒫(T)) : 𝒫(T) := { x | x ∈ A /\ x ∈ B }.
Notation " A '∩' B " := (itsct A B) : NSet_scope.

Definition complement {T : Type} (A : 𝒫(T)) : 𝒫(T) := { x | x ∉ A }.
Notation " '∁' A" := (complement A) : NSet_scope. 

Definition diff {T : Type} (A B: 𝒫(T)) : 𝒫(T) := { x | x ∈ A /\ x ∉ B }.
Notation " A / B " := (diff A B) : NSet_scope.



Add Parametric Morphism {T : Type} : (@union T)
    with signature (@subset T)==> (@subset T) ==> (@subset T) as union_mor_sub.
Proof.
    intros X Y HXinY A B HAinB.
    unfold union. simpl. unfold subset.
    intros x H.
    destruct H. left. by apply HXinY. right. by apply HAinB.
Qed.

Add Parametric Morphism {T : Type} : (@itsct T)
    with signature (@subset T) ==> (@subset T) ==> (@subset T) as itsct_mor_sub.
Proof.
    intros X Y HXinY A B HAinB.
    unfold union. simpl. unfold subset.
    intros x H.
    destruct H as [HxinX HxinA]. split.
    by apply HXinY. by apply HAinB. 
Qed.

Add Parametric Morphism {T : Type} : (@complement T)
    with signature (@subset T) ==> (@supset T) as complement_mor_subsup.
Proof.
    rewrite /complement /supset /subset => A B HAB x //= HxninB HxinA.
    by apply /HxninB /HAB.
Qed.

Add Parametric Morphism {T : Type} : (@diff T)
    with signature (@subset T) ==> (@supset T) ==> (@subset T) as diff_mor_sub.
Proof.
    intros X Y HXinY A B HBinA.
    unfold subset, diff, not; simpl. intros x Hx.
    split. apply HXinY. by apply Hx. intros HxinB. apply HBinA in HxinB.
    by apply Hx.
Qed.



(* set by enumerating *)

Definition singleton {T : Type} (x : T) := { a | a = x }.


Notation "{{ x , .. , y }} " := 
    (singleton x ∪ .. (singleton y ∪ ∅) .. ) : NSet_scope.
    




(** This part, especially [mapL] [mapR] needs the notion of function, base on set. *)

Definition big_union {T : Type} (A : 𝒫(𝒫(T))) : 𝒫(T) :=
    { x | exists X, X ∈ A /\ x ∈ X }.
Notation "⋃" := big_union : NSet_scope.

Add Parametric Morphism {X : Type} : (@big_union X)
    with signature (@subset (𝒫(X))) ==> (@subset X) as bigU_mor_sub.
Proof.
    intros M N HMinN. unfold big_union, subset. simpl.
    intros x [S HS]. exists S. split. apply HMinN. apply HS. apply HS.
Qed.



Definition big_itsct {T : Type} (A : 𝒫(𝒫(T))) : 𝒫(T) :=
    { x | forall X, X ∈ A -> x ∈ X }.
Notation "⋂" := big_itsct : NSet_scope.


(** As is also confirmned in mathematica, this operation can be considered as a
    map. This [mapR] can be considered as the operator to lift a function.
*)
Definition mapR {X Y: Type} (f : X -> Y) : 𝒫(X) -> 𝒫(Y) :=
    fun A => { f x , x | x ∈ A }.
Notation " f [<] " := (@mapR _ _ f) : NSet_scope.

Lemma mapR_fold (X Y: Type) (f : X -> Y) A : 
    { f a , a | a ∈ A } = f [<] A.
Proof. by []. Qed.

Add Parametric Morphism {X Y : Type} : (@mapR X Y)
    with signature eq ==> (@subset X) ==> (@subset Y) as mapR_mor_sub.
Proof.
    intros f M N HMinN. unfold mapR, subset. simpl.
    intros y [x Hxin]. exists x. split. apply HMinN. 
    by apply Hxin. by apply Hxin.
Qed.


Definition mapL {X Y: Type} (F : 𝒫(X -> Y)) : X -> 𝒫(Y) :=
    fun x => { f x , f | f ∈ F }.

Notation " F [>] " := (@mapL _ _ F) : NSet_scope.

Add Parametric Morphism {X Y : Type} : (@mapL X Y)
    with signature (@subset (X -> Y)) ==> eq ==> (@subset Y) as mapL_mor_sub.
Proof.
    rewrite /mapL /subset => F G HFinG x //=.
    move => y [f [Hfin Hyeq]]. exists f. split => //. by apply HFinG.
Qed.
    


(** Note that this operator automatically contains a big union. *)
Definition UmapR {X Y: Type} (F : X -> 𝒫(Y)) : 𝒫(X) -> 𝒫(Y)
    := fun x => ⋃ (F [<] x).

Notation " F [<<] " := (@UmapR _ _ F) : NSet_scope.

Lemma UmapR_fold {X Y: Type} (F : X -> 𝒫(Y)) (A :  𝒫(X)) :

    ⋃ (F [<] A) = F [<<] A.

Proof. by rewrite /UmapR. Qed.

(** Note that this operator automatically contains a big union. *)
Definition UmapLR {X Y: Type} (F : 𝒫(X -> Y)) : 𝒫(X) -> 𝒫(Y)
    := fun x => ⋃ (F [>][<] x).

Notation " F [><] " := (@UmapLR _ _ F) : NSet_scope.

Lemma UmapLR_fold {X Y: Type} (F : 𝒫(X -> Y)) (A :  𝒫(X)) :

    ⋃ (F [>][<] A) = F [><] A.

Proof. by rewrite /UmapLR. Qed.

(*
(*  Example: Function Lifting 
    言の葉ではなく…秘められし真意を伝えん!
*)
Axiom (A B C D: Type) (f : A -> B -> C -> D).
Check (fun x => f [<] x).
Check (fun x => f [<] x [>]).
Check (fun x => f [<] x [>][<<]).
Check (fun x y => ((f [<] x) [>])[<] y).
Check (fun x y z => f [<] x [>][<<] y [>][<<] z).
*)


(** lift operator of a function with two parameters *)
Definition funlift2 {X Y Z: Type} (f : X -> Y -> Z) : 𝒫(X) -> 𝒫(Y) -> 𝒫(Z) :=
    fun A B => f[<]A[>][<<]B.

(*



(* bi_ele_eq : { x , y } {=} { y , x } *)
Lemma bi_ele_eq : forall x y : T, {{ x , y }} {=} {{ y , x }}.
Proof
    intros. split; simpl.
    - intros. destruct H. right. left. apply H.
        destruct H. left. apply H. destruct H.
    - intros. destruct H. right. left. apply H.
        destruct H. left. apply H. destruct H.
Qed.

(* bi_ele_in : x ∈ X -> y ∈ X -> { x , y } ⊆ X *)
Lemma bi_ele_in (X : set T): forall' x ∈ X, forall' y ∈ X, {{x, y}} ⊆ X.
Proof. unfold subset. simpl. intros x HxinX y HyinX z H. 
    destruct H. rewrite H. apply HxinX.
    destruct H. rewrite H. apply HyinX.
    destruct H.
Qed.

*)


(*#######################################################################*)
(** I am not sure whether this axiom is consistent. 
    TODO #10 *)
Module TypeSetEquivalence.

Axiom type_eq_set : forall (T: Type), T = (set_uni T : Type).

(** shoule we add a axiom saying that the sigma type of a sigma type can be 
    simplified? *)

End TypeSetEquivalence.