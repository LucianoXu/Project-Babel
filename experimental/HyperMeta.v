(** HyperMeta : build meta theory with structurally. *)

Notation "⌈ P ⇒ Q ⌉" := (forall s, P s ⊑ Q s) : MetaLan_Scope.

(****************************************)
(*                                      *)
(*       LanSyntax                      *)
(*       (Language Syntax)              *)
(*                                      *)
(****************************************)

(****************************************)
(*                                      *)
(*       FwdSemMod                      *)
(*       (Forward Semantics)            *)
(*                                      *)
(****************************************)

Module FwdSemMod.

Module MetaType.

    Record mixin_of (Stt : Type) := {}.

    Notation class_of := mixin_of (only parsing).

End MetaType.

Record metaType := Pack {
    Stt : Type;
    _ : MetaType.class_of Stt;
}.

    Module Exports.

    Notation metaType := type.
    Notation Stt := Stt.

    End Exports.

End MetaType.
Export MetaType.

Section ClassDef.

Record mixin_of (mT : metaType) (syntax : Type) := {
    deSem : syntax -> Stt mT -> Stt mT;
}.

Notation class_of := mixin_of (only parsing).

Record type mT := Pack {
    syntax : Type;
    _ : class_of mT syntax;
}.

Local Coercion syntax : type >-> Sortclass.

Definition class mT (cT : type mT) := let: Pack _ c := cT return class_of mT cT in c.


End ClassDef.

Module Exports.

#[reversible] Coercion syntax : type >-> Sortclass.

Notation fwdSemMod := type.

Notation "FwdSemMod.metaType" := metaType.
Notation "FwdSemMod.Stt" := Stt.

End Exports.

End FwdSemMod.
Export FwdSemMod.Exports.


(****************************************)
(*                                      *)
(*       BwdSemMod                      *)
(*       (Backward Semantics)           *)
(*                                      *)
(****************************************)

Module BwdSemMod.

Module MetaType.

    Record mixin_of (Stt : Type) := {
        Asn : clattice;
        (** The type of satisfaction value (complete lattice required). *)
        SVal : clattice;
        (** The function to evaluate the satisfaction value. *)
        sat_eval : Asn -> Stt -> SVal;
        (** The consistency between [Asn] order and [SVal] order *)
        sat_eval_consistent : 
            forall (P Q : Asn), P ⊑ Q <-> ⌈ sat_eval P ⇒ sat_eval Q ⌉;
    }.

    Notation class_of := mixin_of (only parsing).

    Record type := Pack {
        Stt : Type;
        _ : class_of Stt;
    }.

    Local Coercion Stt : type >-> Sortclass.

    Definition class (cT : type) := let: Pack _ c := cT return class_of cT in c.

    Module Exports.

    Coercion class : type >-> class_of.

    Notation metaType := type.

    Notation Stt := Stt.
    Notation Asn := Asn.
    Notation SVal := SVal.

    Notation MetaType T m := (@Pack T m).

    End Exports.

End MetaType.
Export MetaType.Exports.

Section ClassDef.

Record mixin_of (mT : metaType) (syntax : Type) := {

    (* the denotational semantics of the program *)
    wp : syntax -> Asn mT -> Asn mT;

    wp_monotonic : forall p: syntax, MonotonicFun.mixin_of (wp p);
}.

Notation class_of := mixin_of (only parsing).

Record type mT := Pack {
    syntax : Type;
    _ : class_of mT syntax;
}.

Local Coercion syntax : type >-> Sortclass.

Definition class mT (cT : type mT) := let: Pack _ c := cT return class_of mT cT in c.

End ClassDef.

Module Exports.

#[reversible] Coercion syntax : type >-> Sortclass.

Notation bwdSemMod := type.

Notation "BwdSemMod.metaType" := metaType.
Notation "BwdSemMod.MetaType T m" := (MetaType T m).
Notation "BwdSemMod.Stt" := Stt.
Notation "BwdSemMod.Asn" := Asn.
Notation "BwdSemMod.SVal" := SVal.

End Exports.

End BwdSemMod.
Export BwdSemMod.Exports.


(****************************************)
(*                                      *)
(*       DeSemMod                       *)
(*       (Denotational Semantics)       *)
(*                                      *)
(****************************************)

Module DeSemMod.

Module MetaType.

    Section ClassDef.

    Record mixin_of (Stt : Type)
                    (b_f : FwdSemMod.MetaType.class_of Stt) 
                    (b_b : BwdSemMod.MetaType.class_of Stt) := Mixin {
    }.

    Record class_of (Stt : Type) := Class {
        base_fwd : FwdSemMod.MetaType.class_of Stt;
        base_bwd : BwdSemMod.MetaType.class_of Stt;
        mixin : mixin_of base_fwd base_bwd;
    }.

    Record type := Pack {
        Stt : Type;
        _ : class_of Stt;
    }.

    Local Coercion Stt : type >-> Sortclass.
    Local Coercion base_fwd : class_of >-> FwdSemMod.MetaType.class_of.
    Local Coercion base_bwd : class_of >-> BwdSemMod.MetaType.class_of.

    Variables (cT : type).

    Definition class := let: Pack _ c := cT return class_of cT in c.

    Definition Asn := BwdSemMod.Asn class.

    Definition SVal := BwdSemMod.SVal class.

    Definition BwdSemMod_metaType := BwdSemMod.metaType

    End ClassDef.

    Module Exports.

    Coercion class : type >-> class_of.
    Coercion base_fwd : class_of >-> FwdSemMod.MetaType.class_of.
    Coercion base_bwd : class_of >-> BwdSemMod.MetaType.class_of.
        
    Notation metaType := type.

    Notation Stt := Stt.
    Notation Asn := Asn.
    Notation SVal := SVal.


    End Exports.

End MetaType.
Export MetaType.Exports.

Section ClassDef.

Record mixin_of (mT : metaType) (syntax : Type) 
                (base_bwd : BwdSemMod.mixin_of syntax):= {

    (* the denotational semantics of the program *)
    wp : syntax -> Asn mT -> Asn mT;

    wp_monotonic : forall p: syntax, MonotonicFun.mixin_of (wp p);
}.

Notation class_of := mixin_of (only parsing).

Record type mT := Pack {
    syntax : Type;
    _ : class_of mT syntax;
}.

Local Coercion syntax : type >-> Sortclass.

Definition class mT (cT : type mT) := let: Pack _ c := cT return class_of mT cT in c.

End ClassDef.

Module Exports.

#[reversible] Coercion syntax : type >-> Sortclass.

Notation bwdSemMod := type.

Notation "BwdSemMod.metaType" := metaType.
Notation "BwdSemMod.Stt" := Stt.
Notation "BwdSemMod.Asn" := Asn.
Notation "BwdSemMod.SVal" := SVal.

End Exports.

End BwdSemMod.
Export BwdSemMod.Exports.





