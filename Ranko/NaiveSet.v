(** * NaiveSet.v : The general naive set theory. *)


From Ranko Require Import TerminalDogma.premises 
                          TerminalDogma.Extensionality.


From Coq Require Import Classical.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* ################################################################# *)


(** *** Reserved Notations for naive_set *)
Declare Scope NSet_scope.
Open Scope NSet_scope.

Reserved Notation " {  expr , x | cond  } " (at level 0, expr at level 99).
Reserved Notation " s '∈' S " (at level 50).
Reserved Notation " s '∉' S " (at level 50).
Reserved Notation "∅".
Reserved Notation "'{U}'".
Reserved Notation " A '⊆' B " (at level 49).
Reserved Notation " A '⊇' B " (at level 49).
Reserved Notation " A '∪' B " (at level 43).
Reserved Notation " A '∩' B " (at level 42).
Reserved Notation " '∁' A" (at level 39). 

Reserved Notation "'⋃' A" (at level 45).
Reserved Notation "'⋂' A" (at level 44).
Reserved Notation " f @ A " (at level 30).
Reserved Notation " A @ f @ B " (at level 30, f at next level).

Reserved Notation "'forall'' x '∈' A , expr" (at level 80, x at level 20, A at level 80, expr at level 80).
Reserved Notation "'exists'' x '∈' A , expr" (at level 80, x at level 20, A at level 80, expr at level 80).
Reserved Notation "'forall'' A '⊆' B , expr" (at level 80, A at level 20, B at level 80, expr at level 80).
Reserved Notation "'exists'' A '⊆' B , expr" (at level 80, A at level 20, B at level 80, expr at level 80).

Reserved Notation " {{ x , .. , y }} " (at level 20).

(* ################################################################# *)

(** ** Set Definition *)

(** The equivalence between predicates. *)
Lemma predeqP (T : Type) (p q : T -> Prop) : p = q <-> (forall x, p x <-> q x).
Proof. split.
    by move => ->.
    move => H. apply functional_extensionality => x.
    apply propositional_extensionality. by apply H.
Qed.

(** set *)
Record set T := mk_set { 
    chac : T -> Prop;
}.
(** This notation means 'power set'. *)
Notation " '𝒫(' T ) " := (set T) (format "'𝒫(' T )") : NSet_scope.
Notation " s '∈' S " := ((chac S) s) : NSet_scope.
Notation " s '∉' S " := (~ s ∈ S) : NSet_scope.
Notation "{  x | P  }" := (mk_set (fun x => P)) : NSet_scope.
Notation "{  x : A | P  }" := (mk_set (T:=A) (fun x => P)) : NSet_scope.
Notation " {  expr , x | cond  } " := { y | exists x, cond /\ expr = y }.


(** The equivalence between sets. *)
Lemma seteqP (T : Type) (A B : 𝒫(T)) : A = B <-> chac A = chac B.
Proof. split. by move => ->. destruct A, B => /= -> //. Qed.

(** The set we defined can be converted into a sigma type, which corresponds to
    the subset in type system. *)

Coercion set2sigma (T : Type) (A : 𝒫(T)) : Type := sig (chac A).


Lemma belongs_to (T : Type) : forall (A : 𝒫(T)) (a : A), proj1_sig a ∈ A.
Proof. move => A a. by apply (proj2_sig a). Qed.


(** The empty set. *)
Definition set_em (T : Type) : 𝒫(T) := { x | False }.
Notation "∅" := (set_em _).

Lemma in_set_em_F (T : Type) : 
    forall (A : 𝒫(T)) (x : T), x ∈ A -> A = ∅ -> False.
Proof. move => A x Hx HA. rewrite HA in Hx. by destruct Hx. Qed.

(** The universal set (of type T). *)
Definition set_uni (T : Type) : 𝒫(T) := { x | True }.
Notation "'{U}'" := (set_uni _).

(** The set is nonempty *)
Lemma nonemptyP (T : Type) (A : 𝒫(T)) :  A <> ∅ <-> exists x, x ∈ A.
Proof. split; last first.

    move => [x Hx] H. move: Hx H. by apply in_set_em_F.

    move => HA. apply NNPP => /(not_ex_all_not _ _) H.
    apply HA. apply /seteqP /predeqP => x. split.
    by move => Hx; apply (H x).
    by move => [].

Qed.


(** subset relation *)
Definition subset (T : Type) (A B : 𝒫(T)) : Prop :=
    forall x, x ∈ A -> x ∈ B.
Notation " A '⊆' B " := (subset A B) : NSet_scope.

(** supset relation, which is dual to subset *)
Definition supset (T : Type) (A B : 𝒫(T)) : Prop := B ⊆ A.
Notation " A '⊇' B " := (supset A B) : NSet_scope.

Lemma subsupP (T : Type) (A B : 𝒫(T)) : A ⊆ B <-> B ⊇ A.
Proof. split; auto. Qed.

(** subset relation *)

(** subset_refl : A ⊆ A *)
Lemma subset_refl (T : Type): Relation_Definitions.reflexive _ (@subset T).
Proof. unfold Relation_Definitions.reflexive, subset. auto. Qed.

(** subset_trans : A ⊆ B -> B ⊆ C -> A ⊆ C *)
Lemma subset_trans (T : Type): Relation_Definitions.transitive _ (@subset T).
Proof.
    unfold Relation_Definitions.transitive, subset. 
    intros A B C HAinB HBinC. intros x HxinA.
    apply HBinC. apply HAinB. apply HxinA.
Qed.

(** subset_asymm : A ⊆ B -> B ⊆ A -> A = B *)
Lemma subset_asymm (T : Type): Relation_Definitions.antisymmetric _ (@subset T).
Proof.
    rewrite /Relation_Definitions.antisymmetric => A B HAinB HBinA.
    apply /seteqP /predeqP => x. split.
    by apply HAinB. by apply HBinA.
Qed.

Add Parametric Relation {T : Type} : _ (@subset T)
    reflexivity proved by (@subset_refl T)
    transitivity proved by (@subset_trans T)
    as subset_rel.

(** supset relation *)

Lemma supset_refl (T : Type): Relation_Definitions.reflexive _ (@supset T).
Proof. unfold Relation_Definitions.reflexive, supset, subset. auto. Qed.


Lemma supset_trans (T : Type): Relation_Definitions.transitive _ (@supset T).
Proof.
    unfold Relation_Definitions.transitive, supset, subset. 
    intros A B C HBinA HCinB. intros x HxinC.
    apply HBinA. apply HCinB. apply HxinC.
Qed.

Lemma supset_asymm (T : Type): Relation_Definitions.antisymmetric _ (@subset T).
Proof.
    rewrite /Relation_Definitions.antisymmetric => A B HAinB HBinA.
    apply /seteqP /predeqP => x. split.
    by apply HAinB. by apply HBinA.
Qed.
    
Add Parametric Relation {T : Type} : _ (@supset T)
    reflexivity proved by (@supset_refl T)
    transitivity proved by (@supset_trans T)
    as supset_rel.

        
(** subset_em : ∅ ⊆ A *)
Lemma em_subset (T : Type): forall (A : 𝒫(T)), ∅ ⊆ A.
Proof. unfold subset. unfold set_em. simpl. intros. destruct H. Qed.

Lemma subset_em (T : Type): forall (A : 𝒫(T)), A ⊆ ∅ -> A = ∅.
Proof.
    move => A HAin.
    apply /seteqP /predeqP => x. split.
    by apply HAin. by move => Hxin; destruct Hxin.
Qed.


(* some calculations between sets *)
Definition union (T : Type) (A B : 𝒫(T)) : 𝒫(T) := { x | x ∈ A \/ x ∈ B }.
Notation " A '∪' B " := (union A B) : NSet_scope.

Definition itsct (T : Type) (A B : 𝒫(T)) : 𝒫(T) := { x | x ∈ A /\ x ∈ B }.
Notation " A '∩' B " := (itsct A B) : NSet_scope.

Definition complement (T : Type) (A : 𝒫(T)) : 𝒫(T) := { x | x ∉ A }.
Notation " '∁' A" := (complement A) : NSet_scope. 

Definition diff (T : Type) (A B: 𝒫(T)) : 𝒫(T) := { x | x ∈ A /\ x ∉ B }.
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


Definition big_union (T : Type) (A : 𝒫(𝒫(T))) : 𝒫(T) :=
    { x | exists X, X ∈ A /\ x ∈ X }.
Notation "'⋃' A" := (big_union A) : NSet_scope.


Definition big_itsct (T : Type) (A : 𝒫(𝒫(T))) : 𝒫(T) :=
    { x | forall X, X ∈ A -> x ∈ X }.
Notation "'⋂' A" := (big_itsct A) : NSet_scope.


Definition f_ele (X Y: Type) (A : 𝒫(X)) (f : X -> Y) : 𝒫(Y) :=
    { f x , x | x ∈ A }.
Notation " f @ A " := (@f_ele _ _ A f) : NSet_scope.

Definition f_outer (X Y Z : Type)(A : 𝒫(X))(B : 𝒫(Y))(f : X -> Y -> Z): 𝒫(Z) :=
    ⋃ ((fun a => { f a b, b | b ∈ B } ) @ A).
Notation " A @ f @ B " := (@f_outer _ _ _ A B f) : NSet_scope.


Notation "'forall'' x '∈' A , expr" := (forall x , x ∈ A -> expr) : NSet_scope.
Notation "'exists'' x '∈' A , expr" := (exists x , x ∈ A /\ expr) : NSet_scope.
Notation "'forall'' A '⊆' B , expr" := (forall A , A ⊆ B -> expr) : NSet_scope.
Notation "'exists'' A '⊆' B , expr" := (exists A , A ⊆ B /\ expr) : NSet_scope.

(* set by enumerating *)
Notation "{{ x , .. , y }} " := 
    ({ a | (a = x \/ .. (a = y \/ False) .. )}) : NSet_scope.

Add Parametric Morphism {X : Type} : (@big_union X)
    with signature (@subset (set X)) ==> (@subset X) as big_union_mor_sub.
Proof.
    intros M N HMinN. unfold big_union, subset. simpl.
    intros x [S HS]. exists S. split. apply HMinN. apply HS. apply HS.
Qed.

Add Parametric Morphism {X Y : Type} : (@f_ele X Y)
    with signature (@subset X) ==> eq ==> (@subset Y) as f_ele_mor_sub.
Proof.
    intros M N HMinN f. unfold f_ele, subset. simpl.
    intros y [x Hxin]. exists x. split. apply HMinN. by apply Hxin. by apply Hxin.
Qed.




Section SetTheory.

Variable (T : Type).

Lemma union_same (A : 𝒫(T)) : A ∪ A = A.
Proof. 
    rewrite /union seteqP predeqP => x //=. split.
    by move => []. by move => ?; left.
Qed.

Lemma union_sub_l (A B : 𝒫(T)) : A ⊆ A ∪ B.
Proof. unfold union, subset; simpl. intros. by left. Qed.

Lemma union_sub_r (A B : 𝒫(T)) : B ⊆ A ∪ B.
Proof. unfold union, subset; simpl. intros. by right. Qed.

Lemma union_comm (A B : 𝒫(T)) : A ∪ B = B ∪ A.
Proof. rewrite /union seteqP predeqP // => x. by apply or_comm. Qed.

Lemma union_assoc (A B C: 𝒫(T)) : (A ∪ B) ∪ C = A ∪ (B ∪ C).
Proof. rewrite /union seteqP predeqP // => x. by apply or_assoc. Qed.

Lemma itsct_same (A : 𝒫(T)) : A ∩ A = A.
Proof.
    rewrite /itsct seteqP predeqP => x //=. split.
    by move => []. by move => ?; split.
Qed.

Lemma itsct_sub_l (A B: 𝒫(T)) : A ∩ B ⊆ A.
Proof. unfold itsct, subset; simpl. intros. apply H. Qed.

Lemma itsct_sub_r (A B: 𝒫(T)) : A ∩ B ⊆ B.
Proof. unfold itsct, subset; simpl. intros. apply H. Qed.

Lemma itsct_comm (A B : 𝒫(T)) : A ∩ B = B ∩ A.
Proof. rewrite /union seteqP predeqP // => x. by apply and_comm. Qed.

Lemma itsct_assoc (A B C: 𝒫(T)) : (A ∩ B) ∩ C = A ∩ (B ∩ C).
Proof. rewrite /union seteqP predeqP // => x. by apply and_assoc. Qed.
    
(*

(* bi_ele_eq : { x , y } {=} { y , x } *)
Lemma bi_ele_eq : forall x y : T, {{ x , y }} {=} {{ y , x }}.
Proof.
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

Lemma diff_subset (X Y: 𝒫(T)) : X / Y ⊆ X.
Proof. unfold diff, subset; simpl. intros x Hx. by apply Hx. Qed.

Lemma union_diff_subset (X Y: 𝒫(T)) : (X ∪ Y) / Y ⊆ X.
Proof.
    unfold union, diff, subset; simpl. intros x [Hx1 Hx2].
    by destruct Hx1.
Qed.


Lemma union_diff_subset_diff_union (X Y: 𝒫(T)) : (X ∪ Y) / Y ⊆ (X / Y) ∪ Y.
Proof. unfold union, diff, subset; simpl. intros x [Hxin1 Hxin2].
    destruct Hxin1. by left. by right.
Qed. 

End SetTheory.