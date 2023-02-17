Require Import POrder POrderSet TerminalDogma
                                ExtraDogma.Extensionality
                                ExtraDogma.IotaDescription
                                ExtraDogma.AllDecidable.


Require Import SetFacility 
                POrderFacility 
                POrderBool.

From Babel Require Import Maps.

Require Import Classical Relations.

Require Import Ranko
                ExtensionalityCharacter
                IotaDescriptionCharacter.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** Assume universal decidability *)
Coercion decide_oracle : Sortclass >-> bool.



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

Definition asn_true : Asn := (fun _ => true) : Stt -> bool.
#[local] Hint Unfold asn_true : magic_book.

Definition asn_false : Asn := (fun _ => false) : Stt -> bool.
#[local] Hint Unfold asn_false : magic_book.

(** The substitution of assertions. *)
Axiom asn_substitute : forall (P : Asn) (b : variable) (e : expression), Asn.
Notation " P '[' b ':' e ']' " := (asn_substitute P b e) (at level 0, b at next level).

(** The assumption of substitution. *)
Axiom asn_sub_eq : forall (P : Asn) (s : Stt) (b : variable) (e : expression),
    (P [b : e]) s = P (b ?-> e s; s).


(** some wrapping definitions *)
Definition asn_impl_comp (P Q : Asn) : Sta -> bool := fun s => (P s ==> Q s).
Notation "P ⇒ Q" := (asn_impl_comp P Q) (at level 40).
#[local] Hint Unfold asn_impl_comp : magic_book.

Definition asn_or (P Q : Asn) : Sta -> bool := fun s => (P s || Q s).
Notation "P 'or' Q" := (asn_or P Q) (at level 40).
#[local] Hint Unfold asn_or : magic_book.

Definition asn_and (P Q : Asn) : Sta -> bool := fun s => (P s && Q s).
Notation "P 'and' Q" := (asn_and P Q) (at level 40).
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
    move : (iota_spec (EQtf B)) => //=.
    ranko 0 10 10.
    ranko.
    rewrite iota_spec in H.
    move : H. ranko.
Qed.


Notation guard := (Stt -> bool).

(** program 

    We can consider this idea:
        Here's a difference from [Morrise86] : we use general action with
        known wp function in substitution of assignment. 
        
        This adopts a little taste of modularized language building. *)

Inductive specif : Type :=
| skip_
| abort_ 
| assign_ (b : variable) (e : expression)
| if_ (g1 g2 : guard) (s1 s2 : specif)
| seq_ (s1 s2 : specif)
| block_ (s : specif)

| prescription_ (P Q : Asn).

Notation " 'Skip' " := skip_.
Notation " 'Abort' " := abort_.
Notation " b <- e " := (assign_ b e) (at level 10).
Notation " 'If' g1 ↦ s1 □ g2 ↦ s2 'Fi'" := (if_ g1 g2 s1 s2).
Notation " s1 ; s2 " := (seq_ s1 s2) (at level 95, right associativity).
Notation " [ 'Block' ; p ] " := (block_ p) (at level 0, p at next level).
Notation " P ‖ Q " := (prescription_ P Q) (at level 50).

Reserved Notation " p '{[' R ']}' " (at level 5).


Fixpoint is_program (p : specif) : bool :=
    match p with
    | p; q => is_program p && is_program q
    | If g1 ↦ s1 □ g2 ↦ s2 Fi => is_program s1 && is_program s2
    | [ Block ; s ] => is_program s
    | P ‖ Q => false
    | _ => true
    end.

Fixpoint wp (p : specif) (R : Asn) := 
    match p with
    | Abort => asn_false
    | Skip => R
    | b <- e => R [ b : e ]
    | p; q => p {[ q {[ R ]} ]}
    | If g1 ↦ s1 □ g2 ↦ s2 Fi => 
        (g1 or g2) and (g1 ⇒ s1{[R]}) and (g2 ⇒ s2{[R]})
    (** semantics of recursion is omitted here*)
    | [ Block ; s ] => s {[ R ]}
    | P ‖ Q => P and ((fun x => ⌈ Q ⇒ R ⌉) : Stt -> bool)
    end
    where " p {[ R ]} " := (wp p R).



(** Theorem 3.3 *)

Lemma wp_monotonicMixin (p : specif) : MonotonicFun.mixin_of (wp p).
Proof.
    rewrite /MonotonicFun.mixin_of. induction p.

    ranko.
    ranko.
    ranko. rewrite asn_sub_eq. apply H. by rewrite -asn_sub_eq.


    move => P Q HPQ. 
    move : (IHp1 _ _ HPQ) (IHp2 _ _ HPQ).
    ranko 0 0 0. 
    
    move: H (IHp0 x) (IHp3 x). rewrite -!Bool.implb_true_iff.
    case: (p1 {[P]} x); case: (p1 {[Q]} x); 
    case: (p2 {[P]} x); case: (p2 {[Q]} x); 
    case: (g2 x); case (g1 x) => //=.

    
    move => P Q HPQ.
    move: (IHp2 _ _ HPQ). move: (IHp1 p2 {[P]} p2 {[Q]}).
    clear IHp1 IHp2.
    ranko.
    
    ranko.

    (** prescription *)
    ranko.

    rewrite Bool.andb_true_iff in H0.
    destruct H0. apply /andP. split. by [].

    apply /decide_oracleP => s. apply /implyP => HQs. apply H.

    rewrite decide_oracle_true in H1.

    move : HQs. by apply /implyP.
Qed.

Canonical wp_monotonicfun (p : specif) := 
    MonotonicFun (wp p) (@wp_monotonicMixin p).


Axiom wp_extensionality : forall (p q : specif), wp p = wp q -> p = q.

(** embed specifications in the complete lattice *)
(** 
Check wp _ : [clattice of [Asn  ↦ᵐ  Asn]].
*)
Lemma specif_porderMixin : Poset.mixin_of specif.
Proof.
    refine (@Poset.Mixin specif (fun s1 s2 => wp s1 ⊑ wp s2) _).
    constructor.
    ranko.
    rewrite /transitive. ranko.
    rewrite /antisymmetric. ranko.
        apply wp_extensionality. 
        apply poset_antisym. ranko. ranko.
Defined.

Canonical specif_porder := Poset specif specif_porderMixin.

Definition Spec := [poset of specif].



(** Theorem 3.4 *)
Theorem Theorem_3_4a (P Q : Asn) (s : specif) :

        P ‖ Q ⊑ s <-> P ⊑ s{[Q]}.

Proof.
    split.
    ranko. 
    apply H. apply /andP. ranko.
    apply /decide_oracleP => s0. by apply /implyP.

    ranko.
    rewrite  Bool.andb_true_iff in H0. destruct H0.
    apply H in H0. move: x0 H0. 
    apply (MonotonicFun.class (wp s)).
    rewrite decide_oracle_true in H1.
    ranko. move : H0. by apply /implyP.
Qed.

Theorem Theorem_3_4b (P Q : Asn) (s : specif) :

        P ⊑ s{[Q]} <-> ⌈ P ⇒ s{[Q]} ⌉.

Proof. by apply Lemma_3_1. Qed.



(** ** Properties of specifications *)

Definition specif_chance := asn_true ‖ asn_true.
Definition specif_miracle := asn_true ‖ asn_false.
Definition specif_abort1 := asn_false ‖ asn_true.
Definition specif_abort2 := asn_false ‖ asn_false.


Lemma specif_abort1_prop (R : Asn): 

        specif_abort1 {[ R ]} = asn_false.

Proof. ranko. Qed.

Lemma specif_abort2_prop (R : Asn): 

        specif_abort2 {[ R ]} = asn_false.

Proof. ranko. Qed.

Lemma specif_miracle_prop (R : Asn):

        specif_miracle {[ R ]} = asn_true.

Proof. ranko. apply /decide_oracleP. by move => _.
Qed.


Lemma specif_chance_prop (R : Asn):

        specif_chance {[ R ]} = [monotonicfun of (fun _ => ⌈ R ⌉) : Sta -> bool].

Proof. ranko. Qed.


Lemma prog_property_1 (p : specif) (prog_p : is_program p) :

        p {[ asn_false ]} = asn_false.

Proof.
    elim: p prog_p.
    ranko.
    ranko.
    ranko.

    ranko. by apply asn_sub_eq.

    ranko. rewrite /is_true Bool.andb_true_iff in prog_p. destruct prog_p.
    rewrite (H H1). rewrite (H0 H2).
    by case: (g1 x); case: (g2 x) => //=.

    ranko. rewrite /is_true Bool.andb_true_iff in prog_p. destruct prog_p.
    have t : s2 {[LeibnizEqOrder.fun_monotonicType xpred0]} = asn_false.
        ranko.
    rewrite t. ranko.

    ranko.

    ranko.
Qed.

Lemma prog_property_2 (s : specif) (P Q : Asn):

    s {[ P and Q ]} = s {[ P ]} and s {[ Q ]}.

Proof.
    elim: s P Q.
    - ranko.
    - ranko.
    - ranko.
        rewrite !asn_sub_eq. ranko.

    - move => g1 g2 s1 Hs1 s2 Hs2 P Q.
    move : (Hs1 P Q) (Hs2 P Q). clear Hs1 Hs2.
    ranko.
    by case: (g1 x); case: (g2 x); 
    case: (s1 {[P]} x); case: (s2 {[P]} x);
    case: (s1 {[Q]} x); case: (s2 {[Q]} x) => //=.

    (** Oh my god. Ranko did this! *)
    - ranko.

    - ranko.

    - ranko.

    have t : ((∀ s : Stt, Q s ==> P0 s && Q0 s) : bool) =
    (∀ s : Stt, Q s ==> P0 s) && (∀ s : Stt, Q s ==> Q0 s).
    case E: (decide_oracle (∀ s : Stt, Q s ==> P0 s && Q0 s)).

    * rewrite decide_oracle_true in E.
    symmetry. apply Bool.andb_true_iff. split; rewrite decide_oracle_true => s;
    have t := (E s).
    rewrite Bool.implb_andb_distrib_r in t.
    rewrite /is_true Bool.andb_true_iff in t. apply t.
    rewrite Bool.implb_andb_distrib_r in t.
    rewrite /is_true Bool.andb_true_iff in t. apply t.

    * rewrite decide_oracle_false in E. apply not_all_ex_not in E.
        destruct E. rewrite /is_true Bool.implb_true_iff in H.
        apply imply_to_and in H. destruct H. apply Bool.not_true_is_false in H0.
        apply Bool.andb_false_iff in H0.
        symmetry. apply Bool.andb_false_iff. rewrite !decide_oracle_false.
        destruct H0.
        -- left. apply ex_not_not_all. exists x0. by rewrite H H0.
        -- right. apply ex_not_not_all. exists x0. by rewrite H H0.
    
    - case: (P x); case: (Q x); case: (P0 x); case: (Q0 x) => //=.

Qed.


Lemma prog_property_3 (p : specif) (prog_p : is_program p) (asnC : chain Asn) :

    p {[ ι(EQtf asnC) ]} = ι(EQtf (wp p [<] asnC)).

Proof.
    elim: p prog_p.

    ranko.

Abort.




