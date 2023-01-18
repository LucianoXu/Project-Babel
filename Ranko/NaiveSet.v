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

Reserved Notation "'⋃'".
Reserved Notation " f [<] " (at level 1, left associativity).
Reserved Notation " f [<] ( A )" (at level 1, left associativity).
Reserved Notation " F [>] " (at level 30, right associativity).
Reserved Notation " F [>] x" (at level 30, right associativity, only printing).
Reserved Notation " F [@] " (at level 30, right associativity).
Reserved Notation " F [@] A" (at level 30, right associativity, only printing).

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

(** set *)
Record set (T : Type) := mk_set { 
    chac : T -> Prop;
}.
(** This notation means 'power set'. *)
Notation " '𝒫(' T ) " := (set T) (format "'𝒫(' T )") : NSet_scope.
Notation " s '∈' S " := ((chac S) s) : NSet_scope.
Notation " s '∉' S " := (~ s ∈ S) : NSet_scope.
Notation "{  x : A | P  }" := (mk_set (T:=A) (fun x => P)) : NSet_scope.
Notation "{  x | P  }" := (mk_set (fun x => P)) : NSet_scope.
Notation "{ expr , x .. y | cond }" :=
    { a | (exists x, .. (exists y, cond /\ expr = a ) ..) } : NSet_scope.

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

(** The set we defined can be converted into a sigma type, which corresponds to
    the subset in type system. *)

Coercion set2sigma (T : Type) (A : 𝒫(T)) : Type := sig (chac A).


Lemma belongs_to [T : Type] : forall (A : 𝒫(T)) (a : A), proj1_sig a ∈ A.
Proof. move => A a. by apply (proj2_sig a). Qed.


(** The empty set. *)
Definition set_em (T : Type) : 𝒫(T) := { x | False }.
Notation "∅" := (set_em _).

Lemma in_set_em_F [T : Type] : 
    forall (A : 𝒫(T)) (x : T), x ∈ A -> A = ∅ -> False.
Proof. move => A x Hx HA. rewrite HA in Hx. by destruct Hx. Qed.


(** TODO add the special structure *)
Record nem_set (T : Type) := mk_nem_set {
    nem_set_obj :> 𝒫(T);
    nem_set_class : nem_set_obj <> ∅;
}.

Notation " '𝒫(' T ')₊' " := (nem_set T) (format "'𝒫(' T )₊") : NSet_scope.


(** The universal set (of type T). *)
Definition set_uni (T : Type) : 𝒫(T) := { x | True }.
Notation "'𝕌'" := (set_uni _).

(** The set is nonempty *)
Lemma nonemptyP {T : Type} (A : 𝒫(T)) :  A <> ∅ <-> exists x, x ∈ A.
Proof. split; last first.

    move => [x Hx] H. move: Hx H. by apply in_set_em_F.

    move => HA. apply NNPP => /(not_ex_all_not _ _) H.
    apply HA. apply /seteqP => x. split.
    by move => Hx; apply (H x).
    by move => [].

Qed.


(* This one uses classical logic. *)
Lemma em_classic {T : Type} (A : 𝒫(T)) : A = ∅ \/ A <> ∅.
Proof. apply classic. Qed.


(** subset relation *)
Definition subset {T : Type} (A B : 𝒫(T)) : Prop :=
    forall x, x ∈ A -> x ∈ B.
Notation " A '⊆' B " := (subset A B) : NSet_scope.

(** supset relation, which is dual to subset *)
Definition supset {T : Type} (A B : 𝒫(T)) : Prop := B ⊆ A.
Notation " A '⊇' B " := (supset A B) : NSet_scope.

Lemma subsupP {T : Type} (A B : 𝒫(T)) : A ⊆ B <-> B ⊇ A.
Proof. split; auto. Qed.

(* 
Lemma set_trichotomy {T : Type} (A B : 𝒫(T)) :
    A = B \/ A ⊆ B \/ A ⊇ B.
Proof.
*)

(** subset relation *)

(** subset_refl : A ⊆ A *)
Lemma subset_refl {T : Type}: Relation_Definitions.reflexive _ (@subset T).
Proof. unfold Relation_Definitions.reflexive, subset. auto. Qed.

(** subset_trans : A ⊆ B -> B ⊆ C -> A ⊆ C *)
Lemma subset_trans {T : Type}: Relation_Definitions.transitive _ (@subset T).
Proof.
    unfold Relation_Definitions.transitive, subset. 
    intros A B C HAinB HBinC. intros x HxinA.
    apply HBinC. apply HAinB. apply HxinA.
Qed.

(** subset_asymm : A ⊆ B -> B ⊆ A -> A = B *)
Lemma subset_asymm {T : Type}: Relation_Definitions.antisymmetric _ (@subset T).
Proof.
    rewrite /Relation_Definitions.antisymmetric => A B HAinB HBinA.
    apply /seteqP => x. split.
    by apply HAinB. by apply HBinA.
Qed.

Add Parametric Relation {T : Type} : _ (@subset T)
    reflexivity proved by (@subset_refl T)
    transitivity proved by (@subset_trans T)
    as subset_rel.

(** supset relation *)

Lemma supset_refl {T : Type}: Relation_Definitions.reflexive _ (@supset T).
Proof. unfold Relation_Definitions.reflexive, supset, subset. auto. Qed.


Lemma supset_trans {T : Type}: Relation_Definitions.transitive _ (@supset T).
Proof.
    unfold Relation_Definitions.transitive, supset, subset. 
    intros A B C HBinA HCinB. intros x HxinC.
    apply HBinA. apply HCinB. apply HxinC.
Qed.

Lemma supset_asymm {T : Type}: Relation_Definitions.antisymmetric _ (@subset T).
Proof.
    rewrite /Relation_Definitions.antisymmetric => A B HAinB HBinA.
    apply /seteqP => x. split.
    by apply HAinB. by apply HBinA.
Qed.
    
Add Parametric Relation {T : Type} : _ (@supset T)
    reflexivity proved by (@supset_refl T)
    transitivity proved by (@supset_trans T)
    as supset_rel.


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







(** This part, especially [mapL] [mapR] needs the notion of function, base on set. *)

Definition big_union {T : Type} (A : 𝒫(𝒫(T))) : 𝒫(T) :=
    { x | exists X, X ∈ A /\ x ∈ X }.
Notation "⋃" := big_union : NSet_scope.

Add Parametric Morphism {X : Type} : (@big_union X)
    with signature (@subset (set X)) ==> (@subset X) as big_union_mor_sub.
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
Notation " f [<] ( A ) " := (@mapR _ _ f A) : NSet_scope.

Lemma mapR_fold (X Y: Type) (f : X -> Y) A : 
    { f a , a | a ∈ A } = f [<] A.
Proof. by []. Qed.

Add Parametric Morphism {X Y : Type} : (@mapR X Y)
    with signature eq ==> (@subset X) ==> (@subset Y) as mapR_mor_sub.
Proof.
    intros f M N HMinN. unfold mapR, subset. simpl.
    intros y [x Hxin]. exists x. split. apply HMinN. by apply Hxin. by apply Hxin.
Qed.


Definition mapL {X Y: Type} (F : 𝒫(X -> Y)) : X -> 𝒫(Y) :=
    fun x => { f x , f | f ∈ F }.

Notation " F [>] " := (@mapL _ _ F) : NSet_scope.
(* Notation " F [>] x" := (@mapL _ _ F x) : NSet_scope. *)



Definition mapLR {X Y: Type} (F : 𝒫(X -> Y)) : 𝒫(X) -> 𝒫(Y) :=
    fun A => ⋃ (F [>][<] A).

Notation " F [@] " := (@mapLR _ _ F) : NSet_scope.
(* Notation " F [@] A" := (@mapLR _ _ F A) : NSet_scope. *)

Notation "'forall'' x '∈' A , expr" := (forall x , x ∈ A -> expr) : NSet_scope.
Notation "'exists'' x '∈' A , expr" := (exists x , x ∈ A /\ expr) : NSet_scope.
Notation "'forall'' A '⊆' B , expr" := (forall A , A ⊆ B -> expr) : NSet_scope.
Notation "'exists'' A '⊆' B , expr" := (exists A , A ⊆ B /\ expr) : NSet_scope.

(* set by enumerating *)
Notation "{{ x , .. , y }} " := 
    ({ a | (a = x \/ .. (a = y \/ False) .. )}) : NSet_scope.





Section SetTheory.

Variable (T: Type).

Lemma singletonP (a x : T): x ∈ {{ a }} <-> x = a.
Proof. split.
    by move => [].
    move => H. by left.
Qed.

Lemma union_same (A : 𝒫(T)) : A ∪ A = A.
Proof. 
    rewrite /union seteqP => x //=. split.
    by move => []. by move => ?; left.
Qed.

Lemma union_sub_l (A B : 𝒫(T)) : A ⊆ A ∪ B.
Proof. unfold union, subset; simpl. intros. by left. Qed.

Lemma union_sub_r (A B : 𝒫(T)) : B ⊆ A ∪ B.
Proof. unfold union, subset; simpl. intros. by right. Qed.

Lemma in_union_l (A B : 𝒫(T)) (x : T) : x ∈ A -> x ∈ A ∪ B.
Proof. rewrite /union => Hxin. simpl. by left. Qed.

Lemma in_union_r (A B : 𝒫(T)) (x : T) : x ∈ B -> x ∈ A ∪ B.
Proof. rewrite /union => Hxin. simpl. by right. Qed.

Lemma union_comm (A B : 𝒫(T)) : A ∪ B = B ∪ A.
Proof. rewrite /union seteqP // => x. by apply or_comm. Qed.

Lemma union_assoc (A B C: 𝒫(T)) : (A ∪ B) ∪ C = A ∪ (B ∪ C).
Proof. rewrite /union seteqP // => x. by apply or_assoc. Qed.

Lemma itsct_same (A : 𝒫(T)) : A ∩ A = A.
Proof.
    rewrite /itsct seteqP => x //=. split.
    by move => []. by move => ?; split.
Qed.

Lemma itsct_sub_l (A B: 𝒫(T)) : A ∩ B ⊆ A.
Proof. unfold itsct, subset; simpl. intros. apply H. Qed.

Lemma itsct_sub_r (A B: 𝒫(T)) : A ∩ B ⊆ B.
Proof. unfold itsct, subset; simpl. intros. apply H. Qed.

Lemma itsct_comm (A B : 𝒫(T)) : A ∩ B = B ∩ A.
Proof. rewrite /union seteqP // => x. by apply and_comm. Qed.

Lemma itsct_assoc (A B C: 𝒫(T)) : (A ∩ B) ∩ C = A ∩ (B ∩ C).
Proof. rewrite /union seteqP // => x. by apply and_assoc. Qed.

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




(** Theories about big operators and mappings. *)
Section AdvancedTheory.

Lemma big_union_em {T : Type} :

        ⋃ ∅ = set_em T.

Proof.
    rewrite /big_union. apply seteqP => x. split.
    move => [?] [H]. by destruct H.
    by move => [].
Qed.


(** subset morphism of ⋃ ◦ (f [<]) set *)
(** Here a more precise description of the relation between f and g is 
    something like 'subfunction' *)
Lemma bigU_mapR_mor_sub {X Y: Type} (f g: X -> 𝒫(Y)) (A B: 𝒫(X)):
    A ⊆ B -> (forall t, f t ⊆ g t) ->

        ⋃ (f [<] A) ⊆ ⋃ (g [<] B).

Proof. rewrite /subset => HAinB Hfleg v [Sv] [[t] [Htin HSveq] Hvin].
    have H := Hfleg t v. rewrite HSveq in H. have H' := H Hvin.
    exists (g t). split => //. exists t. split => //. by apply HAinB.
Qed.

        
(** About big opertor and mappings *)

(** This method requires that the type of [y] is not dependent on [A]. *)
Lemma mapR_rei {X Y : Type} (A : 𝒫(X)) (y : Y) :

    A <> ∅ -> { y , a | a ∈ A } = {{ y }} .

Proof. move => /nonemptyP [a Hain]. apply seteqP => x. split.
    move => [x0] [Hx0in] Heq. rewrite Heq. by apply singletonP.
    move => [Heq|].
    exists a. by split.
    by move => [].
Qed.

Lemma mapR_em {X Y: Type} (f : X -> Y) :

        f [<] ∅ = ∅.

Proof. rewrite /mapR. apply seteqP => x. split.
    by move => [?] [[]].
    by move => [].
Qed.


Lemma bigU_fun_rei {X Y: Type} (A : 𝒫(X)) (f : X -> Y):

        ⋃ { {{ f a }}, a | a ∈ A } = f [<] A.
    
Proof. rewrite /mapR /big_union. apply seteqP => x. split.
    move => [Sy] [[x0 [Hx0in HSyeq]]]. rewrite -{}HSyeq.
    rewrite singletonP => ->. exists x0. by split.
    move => [x0 [Hx0in Hxeq]].
    eexists. split. eexists. split. apply Hx0in. rewrite Hxeq.
    by []. by apply singletonP.
Qed.
    

Lemma bigU_rei {X : Type} (A : 𝒫(X)) :

        ⋃ { {{ a }}, a | a ∈ A } = A.

Proof. rewrite /big_union. apply seteqP => x. split.
    move => [Sx] [[x0 [Hx0in HSxeq]]]. rewrite -{}HSxeq. 
    by rewrite singletonP => ->.
    move => Hx.
    exists ({{x}}). split. exists x. by split. by apply singletonP.
Qed.


Lemma bigU_sgl_nem {X Y: Type} (A : 𝒫(X)) (a : 𝒫(Y)) : 

        A <> ∅ -> ⋃ { a, x | x ∈ A } = a.

Proof.
    rewrite /big_union => /nonemptyP HAnem. apply seteqP => x. split.

    move => [Sx] [[x0] [Hx0in HSxeq]] Hxin.
    by rewrite HSxeq.

    (** nonempty A is need in this direction*)
    destruct HAnem as [x0 Hx0].
    move => Hx. exists a. split => //. eexists x0. split => //=.
Qed.

Lemma bigU_sgl_em {X Y: Type} (A : 𝒫(X)) (a : 𝒫(Y)) : 

        A = ∅ -> ⋃ { a, x | x ∈ A } = ∅.

Proof.
    rewrite /big_union => ->. apply seteqP => x. split.
    move => [Sy] [[y0] [Hy0in HSyeq]]. destruct Hy0in.
    move => Hx. destruct Hx.
Qed.

Lemma bigU_union_dist {X : Type} (A B: 𝒫(𝒫(X))) :
    
        ⋃ (A ∪ B) = (⋃ A) ∪ (⋃ B).

Proof.
    rewrite /union /big_union. apply seteqP => x. split.
    by move => [SX] [[HSXin|HSXin]] Hxin ; [left|right]; exists SX; split.
    by move => [[SX [HSXin Hxin]]|[SX [HSXin Hxin]]]; exists SX; split => //;
    [left|right] => //.
Qed.


(** Note: The following one is also a unique lemma. *)
Lemma union_bigU_mapR_dist {X Y : Type} (A : 𝒫(X)) (f g : X -> 𝒫(Y)) :

        (⋃ (f [<] A) ) ∪ (⋃ (g [<] A)) = ⋃ { f x ∪ g x, x | x ∈ A }.

Proof.
    rewrite /union /big_union. apply seteqP => x. split.
    move => [].
    
    { move => [y] [[x0 [Hx0in Hyeq]]] Hxin.
    exists ((f x0)∪(g x0)). split =>//. exists x0. split => //. rewrite Hyeq.
    by apply in_union_l. }
    
    { move => [y] [[x0 [Hx0in Hyeq]]] Hxin.
    exists ((f x0)∪(g x0)). split =>//. exists x0. split => //. rewrite Hyeq.
    by apply in_union_r. }

    move => [y] [[x0] [Hx0in Hyeq]] Hxin. rewrite -{}Hyeq in Hxin.
    destruct Hxin.

    { left. exists (f x0). split => //. exists x0. by split. }
    { right. exists (g x0). split => //. exists x0. by split. }
Qed.


Lemma mapR_in {X Y : Type} (A : 𝒫(X)) (f : X -> Y) :
    forall x : X, 

        x ∈ A -> f x ∈ f [<] A.

Proof. rewrite /mapR => x ? //=. by exists x. Qed.



(*************************)
(** ESPECIALLY IMPORTANT *)
(*************************)

Lemma mapR_bigU_swap {X Y : Type} (f : X -> Y) (A : 𝒫(𝒫(X))):
    
        { f x, x | x ∈ (⋃ A) } = ⋃ { f [<] a , a | a ∈ A }.

Proof.
    rewrite /big_union /mapR. apply /seteqP => x //=. split.

    move => [x0] [[a [Hain Hx0in]]] Hfeq.
    eexists. split. exists a. split => //.
    exists x0. by split.

    move => [y] [[a [Ha Hyeq]]] Heq.
    rewrite -Hyeq in Heq. destruct Heq as [x0 [Hx01 Hx02]].
    exists x0. split => //. exists a. by split.
Qed.


Lemma mapR_bigU_swap_fun {X Y : Type} (f : X -> Y) :

        (f [<]) ◦ ⋃ = ⋃ ◦ ((f [<])[<]).

Proof.
    apply functional_extensionality => A.
    by apply mapR_bigU_swap.
Qed.


(*************************)
(** ESPECIALLY IMPORTANT *)
(*************************)


Lemma double_mapR {X Y Z : Type} (g : X -> Y) (f : Y -> Z) (A : 𝒫(X)) :

        { f b , b | b ∈ g [<] A } = { f (g a), a | a ∈ A }.

Proof.
    rewrite /mapR. apply /seteqP => x //=. split.
    move => [v] [[a [Hain Hveq]] Hxeq]. exists a. rewrite Hveq. by split.
    move => [a] [Hain Hxeq]. exists (g a). split => //=. by exists a.
Qed.

Lemma double_mapR_fun {X Y Z : Type} (g : X -> Y) (f : Y -> Z) :
    
        f[<] ◦ g[<] = (f ◦ g)[<].

Proof.
    apply functional_extensionality => x.
    move : (double_mapR g f x).
    rewrite !mapR_fold. rewrite fun_compP.
    by [].
Qed.
    

(*************************)
(** ESPECIALLY IMPORTANT *)
(*************************)

Lemma bigU_swap {X : Type} (A : 𝒫(𝒫(𝒫(X)))) :

        ⋃ { ⋃ a , a | a ∈ A } = ⋃ (⋃ A).

Proof.
    rewrite /big_union. apply /seteqP => x. split.

    move => [Sx] [[SSx] [HSSxin HSxeq]] Hxin.
    rewrite -HSxeq in Hxin. destruct Hxin as [Sx0 [HSx0in Hxin]].
    exists Sx0. split => //. exists SSx. by split.

    move => [Sx] [[SSx] [HSSxin HSxin]] Hxin.
    eexists. split. eexists. split; last first. eexists. 2: eexists.
    apply HSSxin. split. apply HSxin. by apply Hxin.
Qed.

Lemma bigU_swap_fun {X : Type}  :

        (@big_union X) ◦ (⋃[<]) = ⋃ ◦ ⋃.

Proof.
    apply functional_extensionality => x.
    by apply bigU_swap.
Qed.


Lemma bigU_fun_dist {X Y: Type} (f : X -> 𝒫(𝒫(Y))) (A : 𝒫(X)):

        ⋃ { ⋃ (f a) , a | a ∈ A } = ⋃ (⋃ (f [<] A)).

Proof.
    
    (** transform into the function equality *)
    rewrite mapR_fold. 
    equal_f_comp A.

    rewrite -[RHS]fun_comp_assoc.
    rewrite -bigU_swap_fun.
    rewrite fun_comp_assoc.
    by rewrite -double_mapR_fun.
Qed.

Lemma bigU_fun_dist_fun {X Y: Type} (f : X -> 𝒫(𝒫(Y))):

        ⋃ ◦ (⋃ ◦ f)[<] = ⋃ ◦ ⋃ ◦ f[<].

Proof.
    apply functional_extensionality => x.
    by apply bigU_fun_dist.
Qed.


End AdvancedTheory.

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

