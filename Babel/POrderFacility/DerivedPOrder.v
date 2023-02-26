(** * DerivedPOrder.v : some derived partial orders *)

From Babel Require Import TerminalDogma 
                          ExtraDogma.Extensionality.

From Babel Require Export POrder.

From Babel Require Import Ranko.POrderCharacter.

From Coq Require Import Relations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*##############################################################*)
Module FunPointwiseOrder.
Section OrderDef.

(*###############################################################################*)
(** point-wise order of normal functions *)

Definition fun_ord (X : Type) (Y : poset) : relation (X -> Y) :=
    fun f g => forall x, f x ⊑ g x.
Hint Unfold fun_ord : magic_book.

Lemma fun_ord_refl (X : Type) (Y : poset) : reflexive _ (@fun_ord X Y).
Proof. rewrite /reflexive. porder_level. Qed.
    
Lemma fun_ord_trans (X : Type) (Y : poset) : transitive _ (@fun_ord X Y).
Proof. rewrite /transitive. porder_level.
    by transitivity (y x0).
Qed.

Lemma fun_ord_antisym (X : Type) (Y : poset) : antisymmetric _ (@fun_ord X Y).
Proof. rewrite /antisymmetric. porder_level.
    apply functional_extensionality. porder_level.
Qed.

Definition fun_poset_mixin (X : Type) (Y : poset) : Poset.mixin_of (X -> Y):=
    Poset.Mixin {|
        ord_refl := fun_ord_refl (Y:=Y);
        ord_trans := fun_ord_trans (Y:=Y);
        ord_antisym := fun_ord_antisym (Y:=Y)
    |}.


Canonical fun_poset_type (X : Type) (Y : poset) := 
    Poset (X -> Y) (fun_poset_mixin X Y).


(*###########################################################################*)
(** point-wise order of monotonic functions*)

Definition monofun_ord (X Y : poset) : relation ([X ↦ᵐ Y]) :=
    fun f g => (f : X -> Y) ⊑ g.
Hint Unfold monofun_ord : magic_book.

Lemma monofun_ord_refl (X Y : poset) : reflexive _ (@monofun_ord X Y).
Proof. rewrite /reflexive. porder_level. Qed.
    
Lemma monofun_ord_trans (X Y : poset) : transitive _ (@monofun_ord X Y).
Proof. rewrite /transitive. porder_level.
    by transitivity (y x0).
Qed.

Lemma monofun_ord_antisym (X Y : poset) : antisymmetric _ (@monofun_ord X Y).
Proof. rewrite /antisymmetric. porder_level. Qed.
        
Definition monofun_poset_mixin (X Y : poset) : Poset.mixin_of ([X ↦ᵐ Y]):=
    Poset.Mixin {|
        ord_refl := monofun_ord_refl (Y:=Y);
        ord_trans := monofun_ord_trans (Y:=Y);
        ord_antisym := monofun_ord_antisym (Y:=Y)
    |}.

Canonical monofun_poset_type (X Y : poset) := 
    Poset ([X ↦ᵐ Y]) (monofun_poset_mixin X Y).

End OrderDef.


Module CanonicalStruct.

Canonical fun_poset_type.
Canonical monofun_poset_type.
#[global] Hint Unfold fun_ord : magic_book.
#[global] Hint Unfold monofun_ord : magic_book.

End CanonicalStruct.

End FunPointwiseOrder.



(** If 'isomorphism extensionality' is introduced, then the two type are equal. 
    This module says that even we don't have isomorphism extensionality, we can
    still build the new order structure using an isomorphism. *)

From Babel Require Import TerminalDogma 
                        Isomorphism.
From Coq Require Import Relations.

Module IsomorphismOrder.

Definition isomor_porderMixin (A : Type) (B : poset) 
    (Hiso : A ≅ (Poset.sort B)) : Poset.mixin_of A.
Proof.
    set op := fun a1 a2 => Hiso a1 ⊑ Hiso a2.
    econstructor. instantiate (1 := op).
    constructor.
    - rewrite /reflexive /op => ?; reflexivity.
    - rewrite /transitive /op => x y z; apply poset_trans.
    - rewrite /antisymmetric /op => x y Hxy Hyx. cut (Hiso x = Hiso y). 
        + by apply Injection.class.
        * by apply poset_antisym.
Defined.

Definition isomor_porder (A : Type) (B : poset) (Hiso : A ≅ (Poset.sort B)) :=
    Poset A (isomor_porderMixin Hiso).

Definition isomor_clattice_joinEssence 
    (A : Type) (B : clattice) (Hiso : A ≅ (Poset.sort B)) : 
        CLattice.join_essence_of (isomor_porder Hiso).
Proof.
    repeat econstructor. 
    instantiate (1:= (fun sa => inv_bij Hiso (⊔ᶜˡ (Hiso [<] sa)))).
    - porder_level. 
        have t:= (inv_bij_inv Hiso).
        destruct t. unfold left_inverse in H0. rewrite H0.
        porder_level.

    - porder_level.
        have t:= (inv_bij_inv Hiso).
            destruct t. unfold left_inverse in H0. rewrite H0.
        porder_level.
Defined.

Definition isomor_clatticeMixin 
    (A : Type) (B : clattice) (Hiso : A ≅ (Poset.sort B)) :=
    CLattice.join_essence_to_mixin (isomor_clattice_joinEssence Hiso).

Definition isomor_clattice 
    (A : Type) (B : clattice) (Hiso : A ≅ (Poset.sort B)) :=
        CLattice A (isomor_clatticeMixin Hiso).

End IsomorphismOrder.
            


