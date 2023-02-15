(** SetBasic.v : basic theorems about set *)

From Babel Require Import TerminalDogma 
ExtraDogma.Extensionality.

From Babel Require Export NaiveSet SetCharacter.

From Coq Require Import Classical.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


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

Lemma union_uni (A : 𝒫(T)) : A ∪ 𝕌 = 𝕌.
Proof. rewrite /union seteqP //= => x. split => //=.
    by move => _; right.
Qed.

Lemma union_em (A : 𝒫(T)) : A ∪ ∅ = A.
Proof. rewrite /union seteqP //= => x. split.
    by case. by move => H; left.
Qed.

Lemma itsct_uni (A : 𝒫(T)) : A ∩ 𝕌 = A.
Proof. rewrite /itsct seteqP //= => x. split.
    by move => [] ? _. by move => ?; split.
Qed.

Lemma itsct_em (A : 𝒫(T)) : A ∩ ∅ = ∅.
Proof. rewrite /itsct seteqP //= => x. split => //=.
    by move => [].
Qed.


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
