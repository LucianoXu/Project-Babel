(** * NemSet.v : 
    This module gathers all advanced conclusions about the empty set.
    Including special structures about nonempty sets. *)


From Babel Require Import TerminalDogma 
                          ExtraDogma.Extensionality.

From Babel Require Export NaiveSet SetBasic SetAdvanced SetCharacter.

From Coq Require Import Relations Classical.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Reserved Notation " A '⊆₊' B " (at level 49).
Reserved Notation " A '⊇₊' B " (at level 49).


(*##########################################################*)
(** Lemmas *)

(** In a inhabited type, 𝕌 ≠ ∅. *)
Lemma uni_neq_em (T : iType) : set_uni T <> set_em T.
Proof. apply nonemptyP. by exists [witness of T]. Qed.

(* This one uses classical logic. *)
Lemma em_classic {T : Type} (A : 𝒫(T)) : A = ∅ \/ A <> ∅.
Proof. apply classic. Qed.



Lemma sgt_nem {T : Type} (x : T) : singleton x <> ∅.
Proof. apply nonemptyP. by exists x. Qed.

Lemma uni_nem (T : iType) : set_uni T <> ∅.
Proof. by apply uni_neq_em. Qed.
    
Lemma union_nem_L {T : Type} (A : 𝒫(T)) (B : 𝒫(T)) :
    
        A <> ∅ -> (A ∪ B) <> ∅.

Proof. rewrite !nonemptyP => [[x Hx]]. exists x => //=. by left. Qed.
    

Lemma cond_False_em (T T': Type) (t : T):

    { t , _ : T' | False } = ∅.

Proof. rewrite seteqP => //= => x. split => //.
    by move => [] _ [] [].
Qed.


Lemma big_union_em {T : Type} :

        ⋃ ∅ = set_em T.

Proof.
    set_level.
    (*
    rewrite /big_union. apply seteqP => x. split.
    move => [?] [H]. by destruct H.
    by move => [].
    *)
Qed.

Lemma big_itsct_em {T : Type} :

        ⋂ ∅ = set_uni T.

Proof. set_level.
    (* rewrite /big_itsct. by apply seteqP => /=. *)
Qed.


(** This method requires that the type of [y] is not dependent on [A]. *)
Lemma mapR_rei {X Y : Type} (A : 𝒫(X)) (y : Y) :

    A <> ∅ -> { y , a | a ∈ A } = {{ y }} .

Proof. 
    move => /nonemptyP [a Hain]. apply seteqP => x. split.
    move => [x0] [Hx0in] Heq. rewrite Heq. by apply singletonP.
    move => [Heq|].
    exists a. by split.
    by move => [].
Qed.


Lemma mapR_eq_emP {X Y: Type} (f : X -> Y) (A : 𝒫(X)):

    f [<] A = ∅ <-> A = ∅.

Proof. 
    rewrite /mapR. split; last first.
    move ->. apply seteqP => x. split.
    by move => [?] [[]].
    by move => [].

    move => /seteqP /= H. apply seteqP => x. split => //=.
    move => Hxin.
    apply (H (f x)). by exists x.
Qed.

Lemma mapR_em {X Y: Type} (f : X -> Y) :
    
    f [<] ∅ = ∅.

Proof. by apply mapR_eq_emP. Qed.

Lemma mapR_nem {X Y: Type} (f : X -> Y) (A : 𝒫(X)) :

    A <> ∅ -> f [<] A <> ∅.

Proof. by rewrite mapR_eq_emP. Qed.


Lemma UmapLR_nem {X Y: Type} (F : 𝒫(X -> Y)) (A : 𝒫(X)) :

    F <> ∅ -> A <> ∅ -> F [><] A <> ∅.

Proof.
    rewrite !nonemptyP. move => [f Hfin] [x Hxin].
    exists (f x), (F [>] x). split. 
    by apply mapR_in. by apply mapL_in.
Qed.


Lemma bigU_nemP {X : Type} (A : 𝒫(𝒫(X))) :

        (exists' X ∈ A, X <> ∅) <-> ⋃ A <> ∅.

Proof. split.
    move => [A0 [HA0in /nonemptyP [x Hxin]]].
    apply nonemptyP. exists x => //=. by exists A0. 
    
    move => /nonemptyP [x [A0 [HA0in HA0nem]]].
    exists A0. split => //=. apply /nonemptyP. by exists x.
Qed.

(** How to combine the following two lemmas? *)
Lemma bigU_sgt_nem {X Y: Type} (A : 𝒫(X)) (a : 𝒫(Y)) : 

        A <> ∅ -> ⋃ { a, x | x ∈ A } = a.

Proof.
    rewrite /big_union => /nonemptyP HAnem. apply seteqP => x. split.

    move => [Sx] [[x0] [Hx0in HSxeq]] Hxin.
    by rewrite -HSxeq.

    (** nonempty A is need in this direction*)
    destruct HAnem as [x0 Hx0].
    move => Hx. exists a. split => //. eexists x0. split => //=.
Qed.

Lemma bigU_sgt_em {X Y: Type} (A : 𝒫(X)) (a : 𝒫(Y)) : 

        A = ∅ -> ⋃ { a, x | x ∈ A } = ∅.

Proof.
    rewrite /big_union => ->. apply seteqP => x. split.
    move => [Sy] [[y0] [Hy0in HSyeq]]. destruct Hy0in.
    move => Hx. destruct Hx.
Qed.        

(** About multiple elements *)
Lemma bigU_ele1 {X : Type} (A : 𝒫(X)) :

        ⋃ ({{ A }}) = A.

Proof. 
    rewrite bigU_union_dist.
    rewrite big_union_em bigU_sgt.
    by apply union_em.
Qed.

Lemma bigU_ele2 {X : Type} (A B : 𝒫(X)) :

        ⋃ ({{A, B}}) = A ∪ B.

Proof.
    rewrite bigU_union_dist.
    by rewrite bigU_ele1 bigU_sgt.
Qed.

Lemma bigI_ele1 {X : Type} (A : 𝒫(X)) :

    ⋂ ({{ A }}) = A.

Proof. 
    rewrite bigI_itsct_sgt_dist.
    rewrite big_itsct_em.
    by apply itsct_uni.
Qed.

Lemma bigI_ele2 {X : Type} (A B : 𝒫(X)) :

    ⋂ ({{A, B}}) = A ∩ B.

Proof.
    rewrite bigI_itsct_sgt_dist.
    by rewrite bigI_ele1.
Qed.


Lemma nemset_eqP {T : Type} (A B : 𝒫(T)₊) : A = B <-> (A : 𝒫(T)) = (B : 𝒫(T)).
Proof.
    split. by move ->.
    destruct A as [A mA], B as [B mB] => //= Heq.
    move : mA mB. rewrite Heq => mA mB. replace mA with mB => //.
    by apply proof_irrelevance.
Qed.

(** get nemset type directly from [x ∈ A]. *)
Lemma belonging_nemMixin {T : Type} (A : 𝒫(T)) (x : T) (Hin : x ∈ A) :
    NemSet.mixin_of A.
Proof. apply nonemptyP. by exists x. Qed.

Coercion belonging_nemType {T : Type} (A : 𝒫(T)) (x : T) (Hin : x ∈ A) :=
    NemSet _ (belonging_nemMixin Hin).


(*##################################################################*)
(** singleton is nonempty *)

Lemma sgt_nemMixin {T : Type} (x : T) : NemSet.mixin_of (singleton x).
Proof. by apply sgt_nem. Qed.

Canonical sgt_nemType {T : Type} (x : T) := NemSet _ (@sgt_nemMixin _ x).

(*##################################################################*)
(** universal set nonempty *)

Lemma uni_nemMixin (T : iType) : NemSet.mixin_of (set_uni T).
Proof. by apply uni_nem. Qed.

Canonical uni_nemType (T : iType) := NemSet _ (@uni_nemMixin T).

(*##################################################################*)
(** union to nonempty
    Note : the canonical structure if on the left of [A ∪ B]. That is, [A]
    should be nonempty to get the nonempty set of [A ∪ B]. *)
    
Lemma union_nemMixin_L {T : Type} (A : 𝒫(T)₊) (B : 𝒫(T)) :
    NemSet.mixin_of (A ∪ B).
Proof. apply union_nem_L. by apply NemSet.class. Qed.

Canonical union_nemType_L {T : Type} (A : 𝒫(T)₊) (B : 𝒫(T)) :=
    NemSet _ (@union_nemMixin_L _ A B).
(*
(** typical usage: *)
Axiom (a b c : nat) (A : 𝒫(nat)₊) (B : 𝒫(nat)).
Check ([nemset of (A ∪ B)]).
Check ([nemset of {{a}}]).
Check ([nemset of {{a, b}}]).
*)



(*##################################################################*)
(** mapR nonempty *)

Lemma mapR_nemMixin (X Y: Type) (f : X -> Y) (A : 𝒫(X)₊): 
    NemSet.mixin_of (f [<] A).
Proof. 
    rewrite /NemSet.mixin_of. rewrite mapR_eq_emP. 
    by apply NemSet.class. 
Qed.

Canonical mapR_nemType (X Y: Type) (f : X -> Y) (A : 𝒫(X)₊) :=
    NemSet _ (@mapR_nemMixin _ _ f A).


(*##################################################################*)
(** supset relation *)

Definition nem_subset {T : Type} (A B : 𝒫(T)₊) : Prop := A ⊆ B.
Notation " A '⊆₊' B " := (nem_subset A B) : NSet_scope.

Definition nem_supset {T : Type} (A B : 𝒫(T)₊) : Prop := A ⊇ B.
Notation " A '⊇₊' B " := (nem_supset A B) : NSet_scope.

Lemma nem_supset_refl {T : Type}: reflexive _ (@nem_supset T).
Proof. rewrite /reflexive => x. by apply supset_rel. Qed.

Lemma nem_supset_trans {T : Type}: transitive _ (@nem_supset T).
Proof. rewrite /transitive => x y z. by apply supset_rel. Qed.

Lemma nem_supset_asymm {T : Type}: antisymmetric _ (@nem_supset T).
Proof.
    rewrite /antisymmetric => A B HAB HBA. apply nemset_eqP.
    by apply supset_asymm.
Qed.
    
Add Parametric Relation {T : Type} : _ (@nem_supset T)
    reflexivity proved by (@nem_supset_refl T)
    transitivity proved by (@nem_supset_trans T)
    as nem_supset_rel.


    
(*##################################################################*)
(** special operators for nemsets *)

(** Transform the inner nemset type into normal set type. *)
Definition nemset2set {T : Type} : 𝒫(𝒫(T)₊) -> 𝒫(𝒫(T)) :=
    (@NemSet.set T) [<].
Notation "[ T 'as' 'set' ]" := (nemset2set T)
    (at level 0, format "[ T  'as'  'set' ]") : NSet_scope.

(** A special operator is need. We need to turn ∅ into 𝕌. *)
Definition nem_big_itsct {T : Type} (A : 𝒫(𝒫(T)₊)) : 𝒫(T) :=
    (⋂ [ A as set ]).
Notation "⋂₊" := nem_big_itsct : NSet_scope.

Definition nem_big_union {T : Type} (A : 𝒫(𝒫(T)₊)) : 𝒫(T) :=
    (⋃ [ A as set ]).
Notation "⋃₊" := nem_big_union : NSet_scope.

Lemma nem_big_union_nem {T : Type} (A : 𝒫(𝒫(T)₊)) :

    A <> ∅ -> ⋃₊ A <> ∅.

Proof.
    rewrite !nonemptyP => [[X HX]].
    case [nemset_witness of X] => x Hx.
    exists x, X. split => //=. by exists X.
Qed. 


Lemma nem_big_union_nemMixin {T : Type} (A : 𝒫(𝒫(T)₊)₊) :
    NemSet.class_of (⋃₊ A).
Proof. apply nem_big_union_nem. by apply NemSet.class. Qed.

Canonical nem_big_union_nemType {T : Type} (A : 𝒫(𝒫(T)₊)₊) :=
    NemSet _ (@nem_big_union_nemMixin _ A).

(*#######################################################################*)
(** Proof facilities about sets *)

Lemma forall_to_exists_nonempty {T : Type} (A : 𝒫(T)) (P : T -> Prop) :
    A <> ∅ -> (forall' x ∈ A, P x) -> (exists' x ∈ A, P x).
Proof.
    move => /nonemptyP [x Hx] H.
    exists x. split => //. by apply H.
Qed.

Lemma forall_to_exists_nemset {T : Type} (A : 𝒫(T)₊) (P : T -> Prop) :
    (forall' x ∈ A, P x) -> (exists' x ∈ A, P x).
Proof. apply forall_to_exists_nonempty. by apply NemSet.class. Qed.

    