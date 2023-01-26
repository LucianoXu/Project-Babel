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

Notation Nemset T m := (@Pack _ T m).
Notation "[ 'nemset' 'of' T ]" := ([get s | obj s ~ T : 𝒫(_)])
  (at level 0, format "[ 'nemset'  'of'  T ]") : NSet_scope.
Notation "[ 'nemsetMixin' 'of' T ]" := (class [nemset of T])
  (at level 0, format "[ 'nemsetMixin'  'of'  T ]") : NSet_scope.
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

Definition nem_subset {T : Type} (A B : 𝒫(T)₊) : Prop := A ⊆ B.
Notation " A '⊆₊' B " := (nem_subset A B) : NSet_scope.


Definition nem_supset {T : Type} (A B : 𝒫(T)₊) : Prop := A ⊇ B.
Notation " A '⊇₊' B " := (nem_supset A B) : NSet_scope.

(** supset relation *)

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


Definition nemset2set {T : Type} (A : 𝒫(𝒫(T)₊)) : 𝒫(𝒫(T)) :=
    { (x : 𝒫(T)), x | x ∈ A }.

(** A special operator is need. We need to turn ∅ into 𝕌. *)
Definition nem_big_itsct {T : Type} (A : 𝒫(𝒫(T)₊)) : 𝒫(T) :=
    (⋂ (nemset2set A)) ∪ { _ | A = ∅ }.
Notation "⋂₊" := nem_big_itsct : NSet_scope.


