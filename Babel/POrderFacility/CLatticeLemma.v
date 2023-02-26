(** * CLatticeLemma.v : some lemmas about complete lattice. *)

From Babel Require Import TerminalDogma 
                          ExtraDogma.Extensionality.

From Babel Require Export POrder DerivedPOrder.

From Babel Require Import Ranko.POrderCharacter.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(*###############################################################*)
(** complete lattice of monotonic functions *)

Module MonoFunCLattice.

Import FunPointwiseOrder.CanonicalStruct.

Definition join_op (C : poset) (D : clattice) (F : 𝒫([C ↦ᵐ D])) : [C ↦ᵐ D].
Proof.
    set f := fun c => ⊔ᶜˡ { f c, f | f ∈ F }.
    refine (MonotonicFun f _).

    porder_level. 
    rewrite /f //=. porder_level.
    apply (CLattice.join_prop (CLattice.class D)) => //=. porder_level.
    
    (* Set Printing All. *)
    apply (@poset_trans _ _ (x0 y) _).
    by apply MonotonicFun.class.
    
    porder_level.
Defined.

Definition clattice_join_essence (C : poset) (D : clattice): 
    CLattice.join_essence_of [C ↦ᵐ D].
Proof.
    refine (@CLattice.JoinEssence _ (@join_op C D) _) => //=.
    porder_level.
Defined.

Definition AUX_clattice_type (C : poset) (D : clattice) :=
    CLattice [C ↦ᵐ D] (CLattice.join_essence_to_mixin 
                            (clattice_join_essence C D)).

Definition lattice_mixin (C : poset) (D : clattice) : 
    Lattice.mixin_of (Poset.class [C ↦ᵐ D]) :=
    Lattice.class [lattice of AUX_clattice_type C D].

Canonical lattice_type (C : poset) (D : clattice) :=
    Lattice [C ↦ᵐ D] (lattice_mixin C D).

Definition clattice_mixin (C : poset) (D : clattice) : 
    CLattice.mixin_of (Lattice.class [C ↦ᵐ D]) :=
    CLattice.class [clattice of AUX_clattice_type C D].

Canonical clattice_type (C : poset) (D : clattice) :=
    CLattice [C ↦ᵐ D] (clattice_mixin C D).

Canonical cpo_type (C : poset) (D : clattice) : cpo :=
    CPO [C ↦ᵐ D] (CPO.class [cpo of [clattice of [C ↦ᵐ D]]]).

Module Exports.

Canonical lattice_type.
Canonical clattice_type.
Canonical cpo_type.

End Exports.

End MonoFunCLattice.

Export MonoFunCLattice.Exports.
    

