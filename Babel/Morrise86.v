Require Import POrder POrderSet TerminalDogma
                                ExtraDogma.Extensionality
                                ExtraDogma.IotaDescription
                                ExtraDogma.AllDecidable.


Require Import SetFacility 
                POrderFacility 
                POrderBool.

From Babel Require Import Maps.

From Coq Require Import Classical Relations Bool.

Require Import Ranko
                ExtensionalityCharacter
                IotaDescriptionCharacter
                AllDecidableCharacter
                ClassicalCharacter.

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

(** Asn : complete lattice *)
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

Definition asn_not (P : Asn) : Sta -> bool := fun s => ~~ P s.
Notation "'not' P" := (asn_not P) (at level 50).
#[local] Hint Unfold asn_not : magic_book.

Definition uni_quantification (P : Asn) : Prop := forall s, P s.
Notation "⌈ P ⌉" := (uni_quantification P).
#[local] Hint Unfold uni_quantification : magic_book.


Lemma Lemma_3_1 (P Q : Asn) :
    P ⊑ Q <-> ⌈ P ⇒ Q ⌉.
Proof. ranko. Qed.


(** big exists and big forall *)
Definition EQtf (B : 𝒫(Asn)) (f : Sta -> bool) : Prop :=
    forall x, f x = true <-> exists' P ∈ B, P x.
#[local] Hint Unfold EQtf : magic_book.

Lemma EQtf_iota_mixin (B : 𝒫(Asn)): Iota.mixin_of (EQtf B).
Proof. rewrite /Iota.mixin_of /unique.
Admitted.

Canonical EQtf_iota (B : 𝒫(Asn)) := Iota (EQtf B) (EQtf_iota_mixin B).


Lemma Lemma_3_2 (B : 𝒫(Asn)) :
    ⊔ᶜˡ B = ι(EQtf B).
Proof. ranko. Qed.


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
Notation " s1 ⨾ s2 " := (seq_ s1 s2) (at level 15, right associativity).
Notation " [ 'Block' ; p ] " := (block_ p) (at level 0, p at next level).
Notation " P ‖ Q " := (prescription_ P Q) (at level 50).

Reserved Notation " p '{[' R ']}' " (at level 5).


Fixpoint is_program (p : specif) : bool :=
    match p with
    | p⨾ q => is_program p && is_program q
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
    | p⨾ q => p {[ q {[ R ]} ]}
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
    ranko 0 2 0.

    
    move => P Q HPQ.
    move: (IHp2 _ _ HPQ). move: (IHp1 p2 {[P]} p2 {[Q]}).
    clear IHp1 IHp2.
    ranko.
    
    ranko.

    (** prescription *)
    ranko.
    (*
    rewrite Bool.andb_true_iff in H0.
    destruct H0. apply /andP. split. by [].
    ranko. apply /implyP => HQs. apply H.

    move : HQs. by apply /implyP.
    *)
Qed.

(** Every specification s ∈ [Asn ↦ᵐ Asn] *)
Canonical wp_monotonicfun (p : specif) := 
    MonotonicFun (wp p) (@wp_monotonicMixin p).


Axiom wp_extensionality : forall (p q : specif), wp p = wp q -> p = q.

(** embed specifications in the complete lattice *)
(** 
Check wp _ : [clattice of [Asn  ↦ᵐ  Asn]].
Check wp : specif -> [clattice of [Asn  ↦ᵐ  Asn]].
Check wp : [poset of specif] -> [clattice of [Asn  ↦ᵐ  Asn]].
Check (wp   : specif -> [Asn  ↦ᵐ  Asn])
            : [[poset of specif] ↦ᵐ [clattice of [Asn  ↦ᵐ  Asn]]].

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
Theorem Theorem_3_4a (P Q : Asn) (s : Spec) :

        P ‖ Q ⊑ s <-> P ⊑ s{[Q]}.

Proof.
    split.
    ranko. 
    apply H. ranko.

    ranko. apply H in a. move: x0 a.
    apply (MonotonicFun.class (wp s)).
    ranko.
Qed.

Theorem Theorem_3_4b (P Q : Asn) (s : Spec) :

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

Proof. ranko. Qed.


Lemma specif_chance_prop (R : Asn):

        specif_chance {[ R ]} = [monotonicfun of (fun _ => ⌈ R ⌉) : Sta -> bool].

Proof. ranko. Qed.


Lemma prog_property_1 (p : Spec) (prog_p : is_program p) :

        p {[ asn_false ]} = asn_false.

Proof.
    elim: p prog_p.
    ranko.
    ranko.
    ranko.

    ranko. by apply asn_sub_eq.


    ranko 0 1 0. repeat prop_2_bool_ssr_branch.
    rewrite (H a). rewrite (H0 b).
    by case: (g1 x); case: (g2 x) => //=.

    ranko.

    ranko.

    ranko.
Qed.

Lemma prog_property_2 (s : Spec) (P Q : Asn):

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
    - give_up. (* ranko. *)

    - ranko.

    - ranko.

    have t : ((∀ s : Stt, Q s ==> P0 s && Q0 s) : bool) =
    (∀ s : Stt, Q s ==> P0 s) && (∀ s : Stt, Q s ==> Q0 s).
    case E: (decide_oracle (∀ s : Stt, Q s ==> P0 s && Q0 s));
    move: E.

    * ranko.
    (*
    apply Bool.andb_true_iff. split; rewrite decide_oracle_true => s;
    have t := (E s).
    rewrite Bool.implb_andb_distrib_r in t.
    rewrite /is_true Bool.andb_true_iff in t. apply t.
    rewrite Bool.implb_andb_distrib_r in t.
    rewrite /is_true Bool.andb_true_iff in t. apply t.
    *)

    * ranko.
    
    - case: (P x); case: (Q x); case: (P0 x); case: (Q0 x) => //=.

Admitted. (* Qed. *)


Lemma prog_property_3 (p : Spec) (prog_p : is_program p) (asnC : chain Asn) :

    p {[ ι(EQtf asnC) ]} = ι(EQtf (wp p [<] asnC)).

Proof.
    elim: p prog_p.

    - ranko.

    - ranko.


    - ranko. rewrite asn_sub_eq. ranko.
    case E: (ι (EQtf_iota { (x0) [(b) : e], x0 : 
        monotonicfun Sta BoolOrder.clattice_type | x0 ∈ asnC }) x); move: E.
    ranko. by rewrite -asn_sub_eq.
    ranko. apply E. ranko. by rewrite asn_sub_eq.

    - ranko. rewrite (H a) (H0 b). clear H H0. ranko.
    case E: (ι (EQtf_iota { LeibnizEqOrder.fun_monotonicType
         (λ s : Stt, (g1 s || g2 s) && (g1 s ==> s1 {[x0]} s) && (g2 s ==> s2 {[x0]} s)),
       x0 : monotonicfun Sta BoolOrder.clattice_type | x0 ∈ asnC }) x); move: E.
    ranko. ranko.
    prop_2_bool_ssr.
    case: (g1 x); case: (g2 x).
    case E1: (ι
    (EQtf_iota
       { s1 {[x0]}, x0 : monotonicfun Sta BoolOrder.clattice_type | 
       x0 ∈ asnC }) x);
    case E2: (ι
    (EQtf_iota
       { s2 {[x0]}, x0 : monotonicfun Sta BoolOrder.clattice_type | 
       x0 ∈ asnC }) x) => //=; move: E1 E2.

Abort.


(** Theorem 4.1 *)

Theorem Theorem_4_1 (P Q : Asn) :

        P ‖ Q ⊑ Skip <-> ⌈ P ⇒ Q ⌉.

Proof. ranko. apply H. ranko. Qed.



Theorem Theorem_4_2 (P Q : Asn) (b : variable) (e : expression) :

        P ‖ Q ⊑ b <- e <-> ⌈ P ⇒ Q[b : e] ⌉.

Proof. ranko. apply H. ranko.
    move: (H x0); clear H.
    rewrite !asn_sub_eq.
    move: b0. ranko.
    move: (b0 (b ?-> e x0; x0)); clear b0.
    ranko.
Qed.


Theorem Theorem_4_3 (P Q R S : Asn) :

        P ‖ Q ⊑ R ‖ S <-> (⌈ P ⇒ R ⌉ /\ ⌈ S ⇒ Q ⌉) \/ ⌈ not P ⌉.

Proof. 
    rewrite Theorem_3_4a Theorem_3_4b.
    ranko.
    case : (classic (∀ s : Stt, P s = false)). 
    ranko. 
    ranko.
Qed.

Theorem Theorem_4_4 (P Q : Asn) (g1 g2 :guard) (s1 s2 : Spec) :
        
        P ‖ Q ⊑ If g1 ↦ s1 □ g2 ↦ s2 Fi <->
            ⌈ P ⇒ g1 or g2 ⌉ /\ (P and g1 ‖ Q ⊑ s1) /\ (P and g2 ‖ Q ⊑ s2).

Proof.
    rewrite Theorem_3_4a Theorem_3_4b.
    ranko. (* wait a second *)
    - move: (H s).
    by case: (P s); case: (g1 s); case: (g2 s).
    - move: (H x0); clear H. ranko.
        move: (H a); clear a H. ranko.
        move: (b1 b); clear b1 b a b2. move: x0. 
        apply (MonotonicFun.class (wp s1)). ranko.

    - move: (H x0); clear H. ranko.
        move: (H a); clear a H. ranko.
        move: (b2 b); clear b1 b a b2. move: x0. 
        apply (MonotonicFun.class (wp s2)). ranko.
    
    - move: (a s); clear a a0 b. ranko.
        rewrite orb_true_iff. rewrite orb_true_iff in a.
        destruct a. 
        + left. move: H H0. by case: (P s); case: (g1 s).
        + by right.
    
    - move: (a0 Q); clear a0 b. ranko.
        move: (a0 s); clear a0. ranko.
        apply a0. ranko.

    - move: (b Q); clear a0 b. ranko.
        move: (b s); clear b. ranko.
        apply b. ranko.
Qed.

Theorem Theorem_4_5 (P Q R S T U : Asn) :

        ⌈ P ⇒ R ⌉ /\ ⌈ S ⇒ T ⌉ /\ ⌈ U ⇒ Q ⌉ 
        -> P ‖ Q ⊑ (R ‖ S) ⨾ (T ‖ U).

Proof. ranko. Qed.


Theorem Theorem_4_6 (P Q : Asn) (s : Spec) :

        P ‖ Q ⊑ s -> P ‖ Q ⊑ [ Block ; s ].

Proof. ranko. Qed.


Lemma Lemma_4_7a (P Q R S : Asn) (s : Spec):

        P ‖ Q ⊑ s /\ R ‖ S ⊑ s -> (P and R) ‖ (Q and S) ⊑ s.

Proof. ranko 3 0 3.
    have HQ : s {[Q]} x0 = true. apply a. ranko.
    have HS : s {[S]} x0 = true. apply b. ranko.
    clear a b.

    have HQS : s {[ Q and S ]} x0 = true.
    rewrite prog_property_2. ranko. clear HQ HS a0 b0.
    move: x0 HQS. 
    apply (MonotonicFun.class (wp s)). ranko.
Qed.


Lemma Lemma_4_8a (P Q : Asn) (s : Spec):

        P ‖ Q ⊑ ((P ‖ s {[ Q ]}) ⨾ s).

Proof. ranko. move: s0 H.
    apply (MonotonicFun.class (wp s)). ranko.
Qed.

Lemma Lemma_4_8b (P Q : Asn) (s : Spec):

        s {[ P ]} ‖ Q = (s ⨾ (P ‖ Q)).

Proof.
    elim: s.
    - apply wp_extensionality. ranko.
    - apply wp_extensionality. ranko.
    - move => b e. apply wp_extensionality. 
        ranko. rewrite !asn_sub_eq. ranko.
    - ranko.
    - ranko.
    - ranko.
    - move => R S. apply poset_antisym. 
        + ranko. 
        + ranko.
    (** The last case is indeeded unprovable. Consider :
            R ‖ S = true ‖ false = miracle,
            P = Q = true.
    *)
Abort.
         

(** If we limit [s] to programs [p], the above lemma holds. *)
Lemma Lemma_4_8c (P Q : Asn) (p : Spec) (Hprog : is_program p):

        p {[ P ]} ‖ Q = (p ⨾ (P ‖ Q)).

Proof.
    elim: p Hprog.
    - move => Hprog. apply wp_extensionality. ranko.
    - move => Hprog. apply wp_extensionality. ranko.
    - move => Hprog b e. apply wp_extensionality. 
        ranko. rewrite !asn_sub_eq. ranko.
    - ranko.
    - ranko.
    - ranko.
    - ranko.
Qed.
    
        


    