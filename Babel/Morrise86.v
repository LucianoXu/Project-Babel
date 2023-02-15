Require Import POrder POrderSet TerminalDogma
                                ExtraDogma.Extensionality
                                ExtraDogma.IotaDescription.

Require Import Classical.

Require Import SetFacility 
                POrderFacility 
                POrderBool.

From Babel Require Import Maps.

Require Import Ranko.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.




(** The type of state:
    partial maps from identifiers to [nat]. *)
Definition variable := string.
Definition Stt := partial_map nat.

(** Expressions *)
Definition expression := Stt -> nat.


(** >>> *)
Import LeibnizEqOrder.CanonicalStruct.

Definition Sta := [poset of Stt].



(** >>> *)
Import FunPointwiseOrder.CanonicalStruct.
Import BoolOrder.CanonicalStruct.

Definition Asn := [clattice of [Sta ↦ᵐ bool]].


(** The substitution of assertions. *)
Axiom asn_substitute : forall (P : Asn) (b : variable) (e : expression), Asn.
Notation " P '[' b ':' e ']' " := (asn_substitute P b e) (at level 0, b at next level).

(** The assumption of substitution. *)
Axiom asn_sub_eq : forall (P : Asn) (s : Stt) (b : variable) (e : expression),
    P s = (P [b : e]) (b ?-> e s; s).




(** some wrapping definitions *)
Definition asn_impl_comp (P Q : Asn) : Sta -> bool := fun s => (P s ==> Q s).
Notation "P ⇒ Q" := (asn_impl_comp P Q) (at level 40).
#[local] Hint Unfold asn_impl_comp : magic_book.

Definition asn_or (P Q : Asn) : Sta -> bool := fun s => (P s || Q s).
Notation "P 'or' Q" := (asn_or P Q) (at level 40).
#[local] Hint Unfold asn_or : magic_book.

Definition asn_and (P Q : Asn) : Sta -> bool := fun s => (P s && Q s).
Notation "P 'and' Q" := (asn_or P Q) (at level 40).
#[local] Hint Unfold asn_and : magic_book.

Definition uni_quantification (P : Asn) : Prop := forall s, P s.
Notation "⌈ P ⌉" := (uni_quantification P).
#[local] Hint Unfold uni_quantification : magic_book.



Lemma Lemma_3_1 (P Q : Asn) :
    P ⊑ Q <-> ⌈ P ⇒ Q ⌉.
Proof.
    ranko.

    apply /implyP. by apply (H s).

    by move : (implyP (H x) H0).
Qed.


(** big exists and big forall *)
Definition EQtf (B : 𝒫(Asn)) (f : Sta -> bool) : Prop :=
    forall x, f x = true <-> exists' P ∈ B, P x.
#[local] Hint Unfold EQtf : magic_book.

Lemma EQtf_iota_mixin (B : 𝒫(Asn)): Iota.mixin_of (EQtf B).
Proof.
Admitted.

Canonical EQtf_iota (B : 𝒫(Asn)) := Iota (EQtf B) (EQtf_iota_mixin B).


Lemma Lemma_3_2 (B : 𝒫(Asn)) :
    ⊔ᶜˡ B = ι(EQtf B).
Proof.
    apply monotonicfun_eqP.
    apply functional_extensionality.
    move : (iota_spec (EQtf B)) => //=.
    ranko.
    apply iota_eqP.
    rewrite /BoolOrder.pred_join //=. split. intros. apply iota_spec. move: H. ranko.
    move => HEQtf. apply iota_spec in HEQtf. move: HEQtf. ranko.
Qed.


Notation guard := (Stt -> bool).

(** program 

    We can consider this idea:
        Here's a difference from [Morrise86] : we use general action with
        known wp function in substitution of assignment. 
        
        This adopts a little taste of modularized language building. *)

Inductive prog : Type :=
| skip_
| abort_ 
| assign_ (b : variable) (e : expression)
| if_ (g1 g2 : guard) (s1 s2 : prog)
| seq_ (s1 s2 : prog)
| block_ (s : prog).

Notation " 'Skip' " := skip_.
Notation " 'Abort' " := abort_.
Notation " b <- e " := (assign_ b e) (at level 10).
Notation " 'If' g1 ↦ s1 □ g2 ↦ s2 'Fi'" := (if_ g1 g2 s1 s2).
Notation " s1 ; s2 " := (seq_ s1 s2) (at level 95, right associativity).
Notation " [ 'Block' ; p ] " := (block_ p) (at level 0, p at next level).


Reserved Notation " p '{[' R ']}' " (at level 5).


Fixpoint wp (p : prog) (R : Asn) := 
    match p with
    | Abort => (fun s => false) : Stt -> bool
    | Skip => R
    | b <- e => R [ b : e ]
    | p; q => p {[ q {[ R ]} ]}
    | If g1 ↦ s1 □ g2 ↦ s2 Fi => 
        (g1 or g2) and (g1 ⇒ s1{[R]}) and (g2 ⇒ s2{[R]})
    (** semantics of recursion is omitted here*)
    | [ Block ; s ] => s {[ R ]}
    end
    where " p {[ R ]} " := (wp p R).