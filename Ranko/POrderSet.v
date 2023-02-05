(** * POrderSet.v : Library for partial orders with sets. *)


From Ranko Require Import TerminalDogma.premises 
                          TerminalDogma.Extensionality.


From Coq Require Import Relations Classical.

From Ranko Require Export POrder SetFacility.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.




(*#########################################################*)
(** ** power set as poset, with subset order*)

Module SubsetOrder.
Section OrderDef.

(** inclusion order (subset) *)
Definition poset_mixin (T : Type): Poset.mixin_of 𝒫(T) :=
    Poset.Mixin {|
      ord_refl := subset_refl;
      ord_trans := subset_trans;
      ord_antisym := subset_asymm;
    |}.

Canonical poset_type (T : Type) := Poset 𝒫(T) (poset_mixin T).

(** Directly construction of complete lattice. *)
Definition clattice_essence (T : Type) : CLattice.essence_of 𝒫(T).
Proof.
    refine (@CLattice.Essence _ big_union _ big_itsct _) => A.
    apply lubP; split. by apply bigU_ub. by apply bigU_lub.
    apply glbP; split. by apply bigI_lb. by apply bigI_glb.
Defined.

Canonical clattice_type (T : Type) := CLattice 𝒫(T) 
            (CLattice.essence_to_mixin (clattice_essence T)).

(** The structure for direct coercions of [cpo] and [lattice]. *)
Local Coercion lattice_type (T : Type) : lattice := clattice_type T.
Local Coercion cpo_type (T : Type) : cpo := clattice_type T.

(*########################################################################*)
(** prove that certaion operators are continuous *)

(** monotonicity of mapR *)
Definition mapR_monotonicMixin {X Y: Type} (f : X -> Y) : 
    MonotonicFun.mixin_of (f [<]).
Proof.
    rewrite /MonotonicFun.mixin_of => //= A B HAinB. by apply mapR_mor_sub.
Defined.

Canonical mapR_monotonicType {X Y: Type} (f : X -> Y) :=
    MonotonicFun _ (@mapR_monotonicMixin _ _ f).

(** continuity of mapR *)
Definition mapR_continuousMixin {X Y: Type} (f : X -> Y) :
    @ContinuousFun.mixin_of X Y _ (MonotonicFun.class (f [<])).
Proof.
    rewrite /ContinuousFun.mixin_of /CPO.join_op => //= c.
    equal_f_comp c. rewrite -[LHS]fun_assoc -[RHS]fun_assoc. 
    by rewrite mapR_bigU_swapF.
Defined.

Canonical mapR_continuousType {X Y: Type} (f : X -> Y) :=
    ContinuousFun _ (@mapR_continuousMixin _ _ f).

(** monotonicity of bigU *)

Definition bigU_monotonicMixin {X : Type} :
    MonotonicFun.mixin_of (@big_union X).
Proof.
    rewrite /MonotonicFun.mixin_of => //= A B. by apply bigU_mor_sub.
Defined.

Canonical bigU_monotonicType (X : Type) :=
    MonotonicFun _ (@bigU_monotonicMixin X).


(** continuity of bigU *)

Definition bigU_continuousMixin {X : Type} :
    @ContinuousFun.mixin_of 𝒫(X) X _ (MonotonicFun.class ((@big_union X) : monotonicfun _ _)).
Proof.
    (** Coq自动帮我算出来了我要证明什么。这是辅助证明的一大好处。*)
    rewrite /ContinuousFun.mixin_of /CPO.join_op //= => c.
    (** 来一点神奇的咒语…… *)
    equal_f_comp c. rewrite -[LHS]fun_assoc -[RHS]fun_assoc. 
    by rewrite bigU_swapF.
Defined.

Definition bigU_continuousType {X : Type} :=
    ContinuousFun _ (@bigU_continuousMixin X).

End OrderDef.

(** Import this module to use the subset poset canonical structures. *)
Module CanonicalStruct.

Canonical clattice_type.
Canonical poset_type.
Coercion lattice_type : Sortclass >-> lattice.
Coercion cpo_type : Sortclass >-> cpo.
Canonical mapR_monotonicType.
Canonical mapR_continuousType.
Canonical bigU_monotonicType.
Canonical bigU_continuousType.

End CanonicalStruct.

End SubsetOrder.



(*#########################################################*)
(** ** power set as poset, with supset order*)
Module SupsetOrder.
Section OrderDef.
(** inverse inclusion order (supset), definition through dual poset *)

(* 
Definition poset_mixin (T : Type): Poset.class_of 𝒫(T) :=
    Poset.class ((SubsetOrder.poset_type T) †po ).
Canonical poset_type (T : Type) := Poset 𝒫(T) (poset_mixin T).
*)

Canonical clattice_type (T : Type) := 
    CLattice _ (CLattice.class ((SubsetOrder.clattice_type T) †cL)).
Local Coercion poset_type (T : Type) : poset := clattice_type T.
Local Coercion lattice_type (T : Type) : lattice := clattice_type T.
Local Coercion cpo_type (T : Type) : cpo := clattice_type T.


(*########################################################################*)
(** prove that certaion operators are continuous *)

(** monotonicity of mapR *)
Definition mapR_monotonicMixin {X Y: Type} (f : X -> Y) : 
    @MonotonicFun.mixin_of X Y (f [<]).
Proof.
    rewrite /MonotonicFun.mixin_of => //= A B HAinB. by apply mapR_mor_sub.
Defined.

Canonical mapR_monotonicType {X Y: Type} (f : X -> Y) :=
    MonotonicFun _ (@mapR_monotonicMixin _ _ f).

(** NOTE : continuity of mapR does not hold *)


(** monotonicity of bigU *)

Definition bigU_monotonicMixin {X : Type} :
    @MonotonicFun.mixin_of 𝒫(X) X (@big_union X).
Proof.
    rewrite /MonotonicFun.mixin_of => //= A B. by apply bigU_mor_sub.
Defined.

Canonical bigU_monotonicType (X : Type) :=
    MonotonicFun _ (@bigU_monotonicMixin X).


(** NOTE : continuity of bigU does not hold *)

End OrderDef.

(** Import this module to use the supset poset canonical structures. *)
Module CanonicalStruct.

(** This seems not working very well. 
    The coercion of [poset] does not work. *)

Canonical clattice_type.
Coercion poset_type : Sortclass >-> poset.
Coercion lattice_type : Sortclass >-> lattice.
Coercion cpo_type : Sortclass >-> cpo.
Canonical mapR_monotonicType.
Canonical bigU_monotonicType.

End CanonicalStruct.

End SupsetOrder.




(*#########################################################*)
(** ** nonempty set type as poset, with supset order*)
Module NemSetOrder.

(** inclusion order (supset) *)
Definition poset_mixin (T : iType): Poset.class_of 𝒫(T)₊ :=
    Poset.Mixin {|
        ord_refl := nem_supset_refl;
        ord_trans := nem_supset_trans;
        ord_antisym := nem_supset_asymm;
    |}.

Canonical poset_type (T : iType) := Poset 𝒫(T)₊ (poset_mixin T).


(** Import this module to use the nonempty poset canonical structures. *)
Module CanonicalStruct.

Canonical poset_type.

End CanonicalStruct.

End NemSetOrder.