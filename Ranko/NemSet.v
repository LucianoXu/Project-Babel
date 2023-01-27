(** * NemSet.v : special structure about nonempty sets. *)


From Ranko Require Import TerminalDogma.premises 
                          TerminalDogma.Extensionality.

From Ranko Require Export NaiveSet.

From Coq Require Import Relations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Reserved Notation " A '⊆₊' B " (at level 49).
Reserved Notation " A '⊇₊' B " (at level 49).

(*##########################################################*)
(** type of nonempty set *)
Module NemSet.

Definition mixin_of (T : Type) (A : 𝒫(T)) := A <> ∅.
Notation class_of := mixin_of (only parsing).

Section ClassDef.

Structure type (T : Type) := Pack {
    obj : 𝒫(T);
    _ : class_of obj;
}.

Definition class T (cT : type T) := 
    let: Pack _ c := cT return class_of (obj cT) in c.

End ClassDef.

Module Exports.
Coercion obj : type >-> powerset.
Arguments class [T] cT.

Notation nemset := type.
Notation " '𝒫(' T ')₊' " := (type T) (format "'𝒫(' T )₊") : NSet_scope.

Notation NemSet T m := (@Pack _ T m).
Notation "[ 'nemset' 'of' T ]" := ([get s | obj s ~ T : 𝒫(_)])
  (at level 0, format "[ 'nemset'  'of'  T ]") : NSet_scope.
Notation "[ 'nemsetMixin' 'of' T ]" := (class [nemset of T])
  (at level 0, format "[ 'nemsetMixin'  'of'  T ]") : NSet_scope.

(** This item returns [ ∃ x : _, x ∈ T ] directly. *)
Notation "[ 'nemset_witness' 'of' T ]" := 
    (iffLR (@nonemptyP _ _ ) [nemsetMixin of T])
    (at level 0, format "[ 'nemset_witness'  'of'  T ]") : NSet_scope.

End Exports.

End NemSet.
Export NemSet.Exports.

Lemma nemset_eqP {T : Type} (A B : 𝒫(T)₊) : A = B <-> (A : 𝒫(T)) = (B : 𝒫(T)).
Proof.
    split. by move ->.
    destruct A as [A mA], B as [B mB] => //= Heq.
    move : mA mB. rewrite Heq => mA mB. replace mA with mB => //.
    by apply proof_irrelevance.
Qed.

(** get nemset type directly from [x ∈ A]. *)
Lemma belonging_nemMixin {T : Type} (A : 𝒫(T)) (x : T) (Hin : x ∈ A) :
    NemSet.class_of A.
Proof. apply nonemptyP. by exists x. Qed.

Coercion belonging_nemType {T : Type} (A : 𝒫(T)) (x : T) (Hin : x ∈ A) :=
    NemSet _ (belonging_nemMixin Hin).


(*##################################################################*)
(** singleton is nonempty *)
Lemma sgt_nemMixin {T : Type} (x : T): NemSet.class_of (singleton x).
Proof. 
    rewrite /NemSet.mixin_of. apply nonemptyP. 
    exists x => //=.
Qed.

Canonical sgt_nemType {T : Type} (x : T) := NemSet _ (@sgt_nemMixin _ x).


(*##################################################################*)
(** union to nonempty
    Note : the canonical structure if on the left of [A ∪ B]. That is, [A]
    should be nonempty to get the nonempty set of [A ∪ B]. *)
Lemma union_nemMixin_L {T : Type} (A : 𝒫(T)) (B : 𝒫(T)) 
    (mA : NemSet.class_of A):
    NemSet.class_of (A ∪ B).
Proof.
    rewrite /NemSet.mixin_of. apply nonemptyP.
    set nemA := NemSet _ mA.
    case [nemset_witness of nemA]. move => x Hx.
    exists x. by apply in_union_l.
Qed.

Canonical union_nemType_L {T : Type} (A : 𝒫(T)₊) (B : 𝒫(T)) :=
    NemSet _ (@union_nemMixin_L _ A B (NemSet.class A)).
(*
(** typical usage: *)
Axiom (a b c : nat) (A : 𝒫(nat)₊) (B : 𝒫(nat)).
Check ([nemset of (A ∪ B)]).
Check ([nemset of {{a}}]).
Check ([nemset of {{a, b}}]).
*)


(*##################################################################*)
(** universal set nonempty *)
Lemma uni_nemMixin (T : iType) : NemSet.class_of (set_uni T).
Proof. rewrite /NemSet.mixin_of. apply uni_neq_em. Qed.

Canonical uni_nemType (T : iType) := NemSet _ (@uni_nemMixin T).


(*##################################################################*)
(** mapR nonempty *)
Lemma mapR_nemMixin (X Y: Type) (f : X -> Y) (A : 𝒫(X)₊): 
    NemSet.class_of (f [<] A).
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
    (@NemSet.obj T) [<].
Notation "[ T 'as' 'set' ]" := (nemset2set T)
    (at level 0, format "[ T  'as'  'set' ]") : NSet_scope.

(** A special operator is need. We need to turn ∅ into 𝕌. *)
Definition nem_big_itsct {T : Type} (A : 𝒫(𝒫(T)₊)) : 𝒫(T) :=
    (⋂ [ A as set ]).
Notation "⋂₊" := nem_big_itsct : NSet_scope.

Definition nem_big_union {T : Type} (A : 𝒫(𝒫(T)₊)) : 𝒫(T) :=
    (⋃ [ A as set ]).
Notation "⋃₊" := nem_big_union : NSet_scope.


Lemma nem_big_union_nemMixin {T : Type} (A : 𝒫(𝒫(T)₊)₊) :
    NemSet.class_of (⋃₊ A).
Proof.
    rewrite /NemSet.mixin_of. apply /nonemptyP.
    case [nemset_witness of A] => X HX.
    case [nemset_witness of X] => x Hx.
    exists x. exists X => //=. split => //=. by exists X.
Qed.

Canonical nem_big_union_nemType {T : Type} (A : 𝒫(𝒫(T)₊)₊) :=
    NemSet _ (@nem_big_union_nemMixin _ A).

(*#######################################################################*)
(** Proof facilities about sets *)

Lemma forall_to_exists_nemset {T : Type} (A : 𝒫(T)₊) (P : T -> Prop) :
    (forall' x ∈ A, P x) -> (exists' x ∈ A, P x).
Proof.
    move => H. case [nemset_witness of A]. move => x Hx.
    exists x. split => //. by apply H.
Qed.