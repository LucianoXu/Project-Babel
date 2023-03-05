


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