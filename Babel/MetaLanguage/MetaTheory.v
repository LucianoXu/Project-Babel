(** MetaRefinement.v *)
From Babel Require Import TerminalDogma 
                          ExtraDogma.Extensionality
                          POrderFacility.

From Babel Require Import Ranko
                            ExtensionalityCharacter
                            AllDecidableCharacter
                            ClassicalCharacter.

From Coq Require Import Relations Classical.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Declare Scope MetaLan_scope.
Open Scope MetaLan_scope.


Notation "⌈ P ⇒ Q ⌉" := (forall s, P s ⊑ Q s) : MetaLan_scope.

Module BackwardSemModel.


Lemma fun_impl_trans (X : Type) (Y : poset) (P Q R : X -> Y) : 

    ⌈ P ⇒ Q ⌉ -> ⌈ Q ⇒ R ⌉ -> ⌈ P ⇒ R ⌉.

Proof. ranko. transitivity (Q s); ranko. Qed.

(** Meta-language type 
    Specifies the language specifications for a backward semantics language 
    model. *)
Record metaType : Type := {
    (** The type of data structure. *)
    Stt : Type;
    (** The type of assertions (complete lattice required). *)
    Asn : clattice;
    (** The type of satisfaction value (complete lattice required). *)
    SVal : clattice;
    (** The function to evaluate the satisfaction value. *)
    sat_eval : Asn -> Stt -> SVal;
    (** The consistency between [Asn] order and [SVal] order *)
    sat_eval_consistent : 
        forall (P Q : Asn), P ⊑ Q <-> ⌈ sat_eval P ⇒ sat_eval Q ⌉;
}.

(** program language model (with meta type) *)
Record language (mT : metaType) : Type := {

    (* the program syntax type *)
    syntax : Type;

    (* the denotational semantics of the program *)
    wp : syntax -> Asn mT -> Asn mT;

    wp_monotonic : forall p: syntax, MonotonicFun.mixin_of (wp p);
}.

End BackwardSemModel.








Module DeSemModel.

Notation "⌈ P ⇒ Q ⌉" := (forall s, P s ⊑ Q s) : MetaLan_scope.


Lemma fun_impl_trans (X : Type) (Y : poset) (P Q R : X -> Y) : 

    ⌈ P ⇒ Q ⌉ -> ⌈ Q ⇒ R ⌉ -> ⌈ P ⇒ R ⌉.

Proof. ranko. transitivity (Q s); ranko. Qed.

(** Meta-language type 
    Specifies the language specifications for a backward semantics language 
    model. *)
Record metaType : Type := {
    (** The type of data structure. *)
    Stt : Type;
    (** The type of assertions (complete lattice required). *)
    Asn : clattice;
    (** The type of satisfaction value (complete lattice required). *)
    SVal : clattice;
    (** The function to evaluate the satisfaction value. *)
    sat_eval : Asn -> Stt -> SVal;
    (** The consistency between [Asn] order and [SVal] order *)
    sat_eval_consistent : 
        forall (P Q : Asn), P ⊑ Q <-> ⌈ sat_eval P ⇒ sat_eval Q ⌉;
}.

(** program language model (with meta type) *)
Record language (mT : metaType) : Type := {

    (* the program syntax type *)
    syntax : Type;

    deSem : syntax -> Stt mT -> Stt mT;

    (* the denotational semantics of the program *)
    wp : syntax -> Asn mT -> Asn mT;

    wp_monotonic : forall p: syntax, MonotonicFun.mixin_of (wp p);

    (* consistency between forward and backward transformers *)
    desem_consistent :
        forall (S0 : syntax) (P Q : Asn mT) (s : Stt mT), 
            sat_eval P s ⊑ sat_eval Q (deSem S0 s)
            <-> P ⊑ wp S0 Q;
}.

End DeSemModel.



(******* VERIFICATION MODULE ************)

Module VeriMod.


(** Meta-language type 
    Specifies the language specifications for a backward semantics language 
    model. *)
Record metaType : Type := {
    (** The type of data structure. *)
    Stt : Type;
    (** The type of assertions (complete lattice required). *)
    Asn : clattice;
    (** The type of satisfaction value (complete lattice required). *)
    SVal : clattice;
    (** The function to evaluate the satisfaction value. *)
    sat_eval : Asn -> Stt -> SVal;
    (** The consistency between [Asn] order and [SVal] order *)
    sat_eval_consistent : 
        forall (P Q : Asn), P ⊑ Q <-> ⌈ sat_eval P ⇒ sat_eval Q ⌉;
}.

(** program language model (with meta type) *)
Record language (mT : metaType) : Type := {

    (* the program syntax type *)
    syntax : Type;

    (* the denotational semantics of the program *)
    wp : syntax -> Asn mT -> Asn mT;

    wp_monotonic : forall p: syntax, MonotonicFun.mixin_of (wp p);

    (* the axiomatic system for reasoning *)
    ax_sys : Asn mT -> syntax -> Asn mT -> Prop;

    ax_sys_sound : forall (p : syntax) (P Q : Asn mT),
        ax_sys P p Q -> P ⊑ wp p Q;

    ax_sys_complete : forall (p : syntax) (P Q : Asn mT),
        P ⊑ wp p Q -> ax_sys P p Q;
}.

End VeriMod.
