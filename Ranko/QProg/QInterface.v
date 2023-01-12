(** QInterface.v *)

From Ranko Require Import TerminalDogma.premises 
                          TerminalDogma.Extensionality.

From Coq Require Import Classical.
From Coq Require Import Arith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** This file contains the interface of quantum theory need in quantum 
    programs. *)


(** Basic aspects of quantum theory. *)
Module Type QTheoryBasicType.

Declare Scope QTheory_scope.
Open Scope QTheory_scope.

(** Hilbert spaces are the types of quantum variables *)
Parameter HilbertSpace : Type.


(** The scope of quantum variable used in a program. *)
Parameter QvarScope : Type.
Parameter QvScopeType : QvarScope -> HilbertSpace.
Coercion QvScopeType : QvarScope >-> HilbertSpace.

(** Get the type of quantum varibles from the quantum scope.
    Here the quantum variable can refer to 'a bunch of variables' *)
Parameter Qvar : QvarScope -> Type.
Coercion Qvar : QvarScope >-> Sortclass.

(** Empty quantum variable. *)
Parameter em_var : forall qs : QvarScope, qs.

(** The operator to union two quantum varibles *)
Parameter QvarUnion : forall qs : QvarScope, qs -> qs -> qs.
Notation " a [+] b " := (@QvarUnion _ a b ) 
    (at level 10, left associativity) : QTheory_scope.

Parameter QvType : forall qs: QvarScope, qs -> HilbertSpace.
Coercion QvType : Qvar >-> HilbertSpace.

Parameter PDensityOpt : HilbertSpace -> Type.
Notation " '𝒟(' H ')⁻' " := (PDensityOpt H) : QTheory_scope.

Parameter UnitaryOpt : HilbertSpace -> Type.
Parameter MeaOpt : HilbertSpace -> Type.

End QTheoryBasicType.





Module Type QTheorySetType (Export QTB : QTheoryBasicType).

(** Here we need the notion of subset. it can be described base on a
    wrapping of sigma type. 
    TODO #1 *)
Parameter PDensitySet : HilbertSpace -> Type.
Notation " '𝒫(𝒟(' H ')⁻)' " := (PDensitySet H) : QTheory_scope.

(** The universal set of this partial density operator *)
Parameter PDensitySet_uni : forall {H}, 𝒫(𝒟( H )⁻).
Notation " '𝒟(' H ')⁻' " := (@PDensitySet_uni H) 
    (only printing) : QTheory_scope.

(** Here we have the difference : we need to perform 'union' on the program
    state, but we cannot union two density operators. Therefore density 
    operator sets are needed.*)
Parameter union_set : forall {H : HilbertSpace}, 
    𝒫(𝒟( H )⁻) -> 𝒫(𝒟( H )⁻) -> 𝒫(𝒟( H )⁻).
        
Parameter add_set : forall {H : HilbertSpace}, 
    𝒫(𝒟( H )⁻) -> 𝒫(𝒟( H )⁻) -> 𝒫(𝒟( H )⁻).

Notation " A '∪' B " := (@union_set _ A B) (at level 10) : QTheory_scope.
Notation " A + B " := (@add_set _ A B) : QTheory_scope.

Axiom add_set_uni_l : forall {H : HilbertSpace} (s : 𝒫(𝒟( H )⁻)), 
    PDensitySet_uni + s = PDensitySet_uni.

Axiom add_set_uni_r : forall {H : HilbertSpace} (s : 𝒫(𝒟( H )⁻)), 
    s + PDensitySet_uni = PDensitySet_uni.


Parameter InitSttS : forall {qs : QvarScope}
        (qv_init : qs) (rho_s : 𝒫(𝒟( qs )⁻)), 𝒫(𝒟( qs )⁻).
(* Notation "'𝒮ℯ𝓉⁰_'" := InitStt. *)

Parameter UapplyS : forall (qs : QvarScope)
       (qv_U : qs) (U : UnitaryOpt qv_U) 
       (rho_s : 𝒫(𝒟( qs )⁻)), 𝒫(𝒟( qs )⁻).
(* Notation "'𝒰_'" := Uapply. *)

Parameter MapplyS : forall (qs : QvarScope)
       (qv_M : qs) (m : MeaOpt qv_M) 
       (rho_s : 𝒫(𝒟( qs )⁻)) (result : bool), 𝒫(𝒟( qs )⁻).
(* Notation "'𝒫_'" := Mapply. *)

Axiom MapplyS_repeat : forall (qs : QvarScope)
         (qv_M : qs) (m : MeaOpt qv_M) 
         (rho_s : 𝒫(𝒟( qs )⁻)) (result : bool), 
         MapplyS m (MapplyS m rho_s result) result
         = MapplyS m rho_s result.

(** about set order *)

(** Arguments about order *)
Axiom PDenSetOrder : forall {H : HilbertSpace}, 
    𝒫(𝒟( H )⁻) -> 𝒫(𝒟( H )⁻) -> Prop.
Notation " A '⊑♯' B " := (PDenSetOrder A B) (at level 60) : QTheory_scope.


Axiom PDenSetOrder_refl : 
    forall H, Relation_Definitions.reflexive _ (@PDenSetOrder H).
Axiom PDenSetOrder_trans : 
    forall H, Relation_Definitions.transitive _ (@PDenSetOrder H).
Axiom PDenSetOrder_asymm :
    forall H, Relation_Definitions.antisymmetric _ (@PDenSetOrder H).

Add Parametric Relation H : _ (@PDenSetOrder H)
    reflexivity proved by (@PDenSetOrder_refl H)
    transitivity proved by (@PDenSetOrder_trans H) as rel_PDenSetOrder.

Axiom PDenSet_uni_least : 
    forall {H : HilbertSpace} (s : 𝒫(𝒟( H )⁻)), PDensitySet_uni ⊑♯ s.



Add Parametric Morphism {H : HilbertSpace} : (@add_set H)
    with signature (@PDenSetOrder H) ==> (@PDenSetOrder H) 
                    ==> (@PDenSetOrder H) as add_mor_le.
Proof.
Admitted.
Lemma PDenSetOrder_add_split {H : HilbertSpace} :
    forall {rho_s1 rho_s2 rho_s1' rho_s2': 𝒫(𝒟( H )⁻)}, 
        rho_s1 ⊑♯ rho_s1' -> rho_s2 ⊑♯ rho_s2' 
            -> rho_s1 + rho_s2 ⊑♯ rho_s1' + rho_s2'.
Proof. move => a b c d Hac Hbd. rewrite Hac Hbd. by reflexivity. Qed.


Add Parametric Morphism {H : HilbertSpace} : (@union_set H)
    with signature (@PDenSetOrder H) ==> (@PDenSetOrder H) 
                    ==> (@PDenSetOrder H) as union_mor_le.
Proof.
Admitted.
Lemma PDenSetOrder_union_split {H : HilbertSpace} :
    forall {rho_s1 rho_s2 rho_s1' rho_s2': 𝒫(𝒟( H )⁻)}, 
        rho_s1 ⊑♯ rho_s1' -> rho_s2 ⊑♯ rho_s2' 
            -> rho_s1 ∪ rho_s2 ⊑♯ rho_s1' ∪ rho_s2'.
Proof. move => a b c d Hac Hbd. rewrite Hac Hbd. by reflexivity. Qed.



Axiom PDenSetOrder_Init : 
    forall {qs : QvarScope} r1 r2 (qv : qs), 
        r1 ⊑♯ r2 -> InitSttS qv r1 ⊑♯ InitSttS qv r2.
Axiom PDenSetOrder_U : 
    forall {qs : QvarScope} r1 r2 (qv : qs) (U : UnitaryOpt qv),
        r1 ⊑♯ r2 -> UapplyS U r1 ⊑♯ UapplyS U r2.
Axiom PDenSetOrder_M : 
    forall {qs : QvarScope} r1 r2 (qv_m : qs) (m : MeaOpt qv_m) (result : bool),
        r1 ⊑♯ r2 -> MapplyS m r1 result ⊑♯ MapplyS m r2 result.




(* chain and CPO conclusions *)

(** Define the increasing set and least upper bound *)
Record chain (H : HilbertSpace) := mk_chain {
    chain_obj : nat -> 𝒫(𝒟( H )⁻);
    chain_prop : forall n, chain_obj n ⊑♯ chain_obj n.+1;
}.
Notation " ch _[ n ] " := (chain_obj ch n) (at level 40) : QTheory_scope.

(** Convert a singal element into a list *)
Definition singleton_chain_obj {H : HilbertSpace} rho_s : nat -> 𝒫(𝒟( H )⁻) :=
    fun => rho_s.

Lemma singleton_chain_prop {H : HilbertSpace} (rho_s : 𝒫(𝒟( H )⁻)) 
    : forall n, singleton_chain_obj rho_s n ⊑♯ singleton_chain_obj rho_s n.+1.
Proof. rewrite /singleton_chain_obj => n => //=. by reflexivity. Qed.

Definition singleton_chain {H : HilbertSpace} rho_s : chain H :=
    mk_chain (singleton_chain_prop rho_s).

Coercion singleton_chain : PDensitySet >-> chain.

(** Prove the loose criterion of chain equivalence *)
Lemma chain_eqP H : forall (ch1 ch2 : chain H),
        ch1 = ch2 <-> chain_obj ch1 = chain_obj ch2.
Proof. split. by move => -> //.
    move => Heq. destruct ch1 as [obj1 p1], ch2 as [obj2 p2]. simpl in Heq.
    move : p1 p2. rewrite Heq => p1 p2. by rewrite (proof_irrelevance _ p1 p2).
Qed.

Axiom chain_limit : forall H (ch : chain H), 𝒫(𝒟( H )⁻).
Notation " 'lim→∞' ( ch ) " := (@chain_limit _ ch) 
    (at level 200) : QTheory_scope.

Axiom chain_limit_ub : forall H (ch : chain H) n,
    ch _[n] ⊑♯ lim→∞ (ch).

Axiom chain_limit_lub : forall H (ch : chain H) rho_ub,
    (forall n, ch _[n] ⊑♯ rho_ub) -> lim→∞ (ch) ⊑♯ rho_ub.

Lemma singleton_chain_limit (H : HilbertSpace) (rho_s : 𝒫(𝒟( H )⁻)) :
    lim→∞ (rho_s) = rho_s.
Proof.
    apply PDenSetOrder_asymm.
    apply chain_limit_lub. 
    rewrite /singleton_chain /singleton_chain_obj => n => //=. by reflexivity.
    have temp := chain_limit_ub rho_s. by apply (temp 0).
Qed.


(* chain_add *)
Definition chain_add_obj (H : HilbertSpace) (ch_obj1 ch_obj2 : nat -> 𝒫(𝒟( H )⁻)) :=
    fun n => ch_obj1 n + ch_obj2 n.
Lemma chain_add_obj_prop (H : HilbertSpace) (ch1 ch2 : chain H) :
    let ch := chain_add_obj (chain_obj ch1) (chain_obj ch2) in 
        forall n, ch n ⊑♯ ch n.+1.
Proof. move => ch n. rewrite /ch /chain_add_obj. apply PDenSetOrder_add_split.
    by apply ch1. by apply ch2.
Qed.

(** Add chain is needed for proving if statement *)
Definition chain_add H (ch1 ch2 : chain H) : chain H :=
    mk_chain (chain_add_obj_prop ch1 ch2).

(** We still need the assumption that addition is continuous *)
Axiom add_continuous : forall H (ch1 ch2 : chain H),
    (lim→∞(ch1)) + (lim→∞(ch2)) = lim→∞ (chain_add ch1 ch2).


(* chain_union *)
Definition chain_union_obj (H : HilbertSpace) (ch1 ch2 : chain H) :=
    fun n => (ch1 _[n]) ∪ (ch2 _[n]).
Lemma chain_union_prop (H : HilbertSpace) (ch1 ch2 : chain H) :
    forall n, chain_union_obj ch1 ch2 n ⊑♯ chain_union_obj ch1 ch2 n.+1.
Proof. move => n. rewrite /chain_union_obj. apply PDenSetOrder_union_split.
    by apply ch1. by apply ch2.
Qed.

(** union chain is needed for proving parallel statement *)
Definition chain_union H (ch1 ch2 : chain H) : chain H :=
    mk_chain (chain_union_prop ch1 ch2).

(** We still need the assumption that union is continuous *)
Axiom union_continuous : forall H (ch1 ch2 : chain H),
    (lim→∞(ch1)) ∪ (lim→∞(ch2)) = lim→∞ (chain_union ch1 ch2).


(* The chain of InitSttS ch *)
Definition InitStt_chain_obj {qs : QvarScope} (qv : qs) (ch : chain qs) :=
    fun i => InitSttS qv (ch _[i]).
Lemma InitStt_chain_prop {qs : QvarScope} (qv : qs) (ch : chain qs)
    : forall i, InitStt_chain_obj qv ch i ⊑♯ InitStt_chain_obj qv ch i.+1.
Proof.
    rewrite /InitStt_chain_obj => i. apply PDenSetOrder_Init. by apply ch.
Qed.

Definition InitStt_chain {qs : QvarScope} (qv : qs) (ch : chain qs) :=
    mk_chain (InitStt_chain_prop qv ch).

(** We still need the assumption that addition is continuous *)
Axiom init_continuous : forall {qs : QvarScope} (qv : qs) (ch : chain qs),
    InitSttS qv (lim→∞ (ch)) = lim→∞ (InitStt_chain qv ch).

(* The chain of UapplyS U ch *)
Definition Uapply_chain_obj 
    {qs : QvarScope} (qv : qs) (U : UnitaryOpt qv) (ch : chain qs) :=
    fun i => UapplyS U (ch _[i]).
Lemma Uapply_chain_prop 
    {qs : QvarScope} (qv : qs) (U : UnitaryOpt qv) (ch : chain qs)
    : forall i, Uapply_chain_obj U ch i ⊑♯ Uapply_chain_obj U ch i.+1.
Proof.
    rewrite /Uapply_chain_obj => i. apply PDenSetOrder_U. by apply ch.
Qed.

Definition Uapply_chain 
    {qs : QvarScope} (qv : qs) (U : UnitaryOpt qv) (ch : chain qs) :=
    mk_chain (Uapply_chain_prop U ch).

(** We still need the assumption that addition is continuous *)
Axiom unitary_continuous : 
    forall {qs : QvarScope} (qv : qs) (U : UnitaryOpt qv) (ch : chain qs),
    UapplyS U (lim→∞ (ch)) = lim→∞ (Uapply_chain U ch).


(* The chain of MapplyS M ch result *)
Definition Mapply_chain_obj 
    {qs : QvarScope} (qv : qs) (M : MeaOpt qv) (ch : chain qs) (r : bool) :=
    fun i => MapplyS M (ch _[i]) r.
Lemma Mapply_chain_prop 
    {qs : QvarScope} (qv : qs) (M : MeaOpt qv) (ch : chain qs) (r : bool)
    : forall i, Mapply_chain_obj M ch r i ⊑♯ Mapply_chain_obj M ch r i.+1.
Proof.
    rewrite /Mapply_chain_obj => i. apply PDenSetOrder_M. by apply ch.
Qed.

Definition Mapply_chain 
    {qs : QvarScope} (qv : qs) (M : MeaOpt qv) (ch : chain qs) (r : bool) :=
    mk_chain (Mapply_chain_prop M ch r).

(** We still need the assumption that addition is continuous *)
Axiom mea_continuous : forall {qs : QvarScope} 
    (qv : qs) (M : MeaOpt qv) (ch : chain qs) (r : bool),
    MapplyS M (lim→∞ (ch)) r = lim→∞ (Mapply_chain M ch r).

End QTheorySetType.