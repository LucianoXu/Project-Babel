(** QInterface.v *)

From Ranko Require Import TerminalDogma.premises 
                          TerminalDogma.Extensionality
                          NaiveSet.

From Coq Require Import Classical Reals.
From Coq Require Import Arith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** This file contains the interface of quantum theory need in quantum 
    programs. *)


(** Basic aspects of quantum theory. *)
Module Type QTheoryBasicType.

Declare Scope QTheoryBasic_scope.
Open Scope QTheoryBasic_scope.
Delimit Scope QTheoryBasic_scope with QTB.

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
    (at level 10, left associativity) : QTheoryBasic_scope.

Parameter QvType : forall qs: QvarScope, qs -> HilbertSpace.
Coercion QvType : Qvar >-> HilbertSpace.

Parameter PDensityOpt : HilbertSpace -> Type.
Notation " '𝒟(' H ')⁻' " := (PDensityOpt H) 
    (format "'𝒟(' H ')⁻'" ): QTheoryBasic_scope.

Parameter densityOpt0 : forall {H : HilbertSpace}, 𝒟( H )⁻.
Notation " 𝟎 " := (@densityOpt0 _) : QTheoryBasic_scope.

Parameter InitStt : 
    forall (qs : QvarScope), qs -> 𝒟( qs )⁻ -> 𝒟( qs )⁻.

Parameter UnitaryOpt : HilbertSpace -> Type.

Parameter Uapply : 
    forall (qs : QvarScope) (qv : qs), UnitaryOpt qv -> 𝒟( qs )⁻ -> 𝒟( qs )⁻.

(** Here we assume the measurements are dichotomous. *)
Parameter MeaOpt : HilbertSpace -> Type.

Parameter Mapply : forall (qs : QvarScope) (qv : qs),
    MeaOpt qv -> bool -> 𝒟( qs )⁻ -> 𝒟( qs )⁻.

Parameter scalar_PDenOpt : forall (H : HilbertSpace),
    [0, 1]R -> 𝒟( H )⁻ -> 𝒟( H )⁻.
Notation " a * b " := (scalar_PDenOpt a b) : QTheoryBasic_scope.

Parameter scalar_convex_comb : forall (H : HilbertSpace),
    [0, 1]R -> 𝒟( H )⁻ -> 𝒟( H )⁻ -> 𝒟( H )⁻.
Notation " a [ p ⊕ ] b " := (scalar_convex_comb p a b) 
    (at level 10): QTheoryBasic_scope.

Parameter add_PDenOpt : forall (H : HilbertSpace),
    𝒟( H )⁻ -> 𝒟( H )⁻ -> 𝒟( H )⁻.
Notation " a + b " := (add_PDenOpt a b) : QTheoryBasic_scope.

End QTheoryBasicType.





Module Type QTheorySetType (Export QTB : QTheoryBasicType).

Export NaiveSet.

Declare Scope QTheorySet_scope.
Delimit Scope QTheorySet_scope with QTS.
Open Scope QTheorySet_scope.

(** Here we need the notion of subset. it can be described base on a
    wrapping of sigma type. 
    TODO #1 *)
Definition PDensitySet (H: HilbertSpace) : Type := 𝒫(𝒟( H )⁻).
(* Notation " '𝒫(𝒟(' H ')⁻)' " := (PDensitySet H) : QTheorySet_scope. *)

(** The universal set of this partial density operator *)
(* Parameter PDensitySet_uni : forall {H}, 𝒫(𝒟( H )⁻). *)

(* Notation " '𝒟(' H ')⁻' " := (@PDensitySet_uni H) 
    (only printing) : QTheorySet_scope. *)

(** Here we have the difference : we need to perform 'union' on the program
    state, but we cannot union two density operators. Therefore density 
    operator sets are needed.*)
Definition union_set : forall {H : HilbertSpace}, 
    𝒫(𝒟( H )⁻) -> 𝒫(𝒟( H )⁻) -> 𝒫(𝒟( H )⁻) :=
        fun _ a b => a ∪ b.
        
Definition add_set : forall {H : HilbertSpace}, 
    𝒫(𝒟( H )⁻) -> 𝒫(𝒟( H )⁻) -> 𝒫(𝒟( H )⁻) :=
        fun _ a b => ⋃ { add_PDenOpt x [<] b, x | x ∈ a }.

(* Notation " A '∪' B " := (@union_set _ A B) (at level 10) : QTheorySet_scope. *)
Notation " A + B " := (@add_set _ A B) : QTheorySet_scope.

(* TODO #5 *)
Axiom add_set_0_l : forall {H : HilbertSpace} (s : 𝒫(𝒟( H )⁻)), 
    {{ 𝟎 }} + s = s.

Axiom add_set_0_r : forall {H : HilbertSpace} (s : 𝒫(𝒟( H )⁻)), 
    s + {{ 𝟎 }} = s.

(*
Axiom add_set_uni_l : forall {H : HilbertSpace} (s : 𝒫(𝒟( H )⁻)), 
    𝕌 + s = 𝕌.
    
Axiom add_set_uni_r : forall {H : HilbertSpace} (s : 𝒫(𝒟( H )⁻)), 
    s + 𝕌 = 𝕌.
*)

Definition InitSttS {qs : QvarScope} qv rho_s : 𝒫(𝒟( qs )⁻) :=
    (InitStt qv) [<] rho_s.

(* Notation "'𝒮ℯ𝓉⁰_'" := InitStt. *)

Definition UapplyS {qs : QvarScope} (qv_U : qs) (U : UnitaryOpt qv_U) rho_s :
     𝒫(𝒟( qs )⁻) :=
    (Uapply U) [<] rho_s.
(* Notation "'𝒰_'" := Uapply. *)

Definition MapplyS (qs : QvarScope) (qv_M : qs) (m : MeaOpt qv_M) (r : bool)
    rho_s : 𝒫(𝒟( qs )⁻) :=
    (Mapply m r) [<] rho_s.
(* Notation "'𝒫_'" := Mapply. *)

Parameter scalar_convex_combS : forall (H : HilbertSpace), 
    [0, 1]R -> 𝒫(𝒟( H )⁻) -> 𝒫(𝒟( H )⁻) -> 𝒫(𝒟( H )⁻).
Notation " A [ p ⊕ ] B " := (@scalar_convex_combS _ p A B) 
    (format "A  [ p ⊕ ]  B"): QTheorySet_scope.

Axiom MapplyS_repeat : forall (qs : QvarScope)
         (qv_M : qs) (m : MeaOpt qv_M) 
         (rho_s : 𝒫(𝒟( qs )⁻)) (result : bool), 
         MapplyS m result (MapplyS m result rho_s ) 
         = MapplyS m result rho_s .

(** about set order *)

(** Arguments about order *)
(* Axiom PDenSetOrder : forall {H : HilbertSpace}, 
    𝒫(𝒟( H )⁻) -> 𝒫(𝒟( H )⁻) -> Prop. *)
Definition PDenSetOrder {H : HilbertSpace} (A B : 𝒫(𝒟( H )⁻)) :=
    B ⊆ A.
Notation " A '⊑♯' B " := (PDenSetOrder A B) (at level 60) : QTheorySet_scope.


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
    forall {H : HilbertSpace} (s : 𝒫(𝒟( H )⁻)), 𝕌 ⊑♯ s.



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


Add Parametric Morphism {H : HilbertSpace} : (@scalar_convex_combS H)
    with signature eq ==> (@PDenSetOrder H) ==> (@PDenSetOrder H) 
                ==> (@PDenSetOrder H) as convex_comb_mor_le.
Proof.
Admitted.
Lemma PDensetOrder_cv_comb_split {H : HilbertSpace} :
    forall p {rho_s1 rho_s2 rho_s1' rho_s2': 𝒫(𝒟( H )⁻)},
        rho_s1 ⊑♯ rho_s1' -> rho_s2 ⊑♯ rho_s2' 
            -> rho_s1 [ p ⊕ ] rho_s2 ⊑♯ rho_s1' [ p ⊕ ] rho_s2'.
Proof. move => p a b c d Hac Hbd. by apply convex_comb_mor_le. Qed.

Add Parametric Morphism {H : HilbertSpace} : (@union_set H)
    with signature (@PDenSetOrder H) ==> (@PDenSetOrder H) 
                    ==> (@PDenSetOrder H) as union_mor_le.
Proof. rewrite /PDenSetOrder /union_set => a c Hac b d Hbd.
    by rewrite Hac Hbd.
Qed.

Lemma PDenSetOrder_union_split {H : HilbertSpace} :
    forall {rho_s1 rho_s2 rho_s1' rho_s2': 𝒫(𝒟( H )⁻)}, 
        rho_s1 ⊑♯ rho_s1' -> rho_s2 ⊑♯ rho_s2' 
            -> rho_s1 ∪ rho_s2 ⊑♯ rho_s1' ∪ rho_s2'.
Proof. 
    rewrite /PDenSetOrder => a b c d Hac Hbd. 
    rewrite Hac Hbd. by reflexivity. 
Qed.



Axiom PDenSetOrder_Init : 
    forall {qs : QvarScope} r1 r2 (qv : qs), 
        r1 ⊑♯ r2 -> InitSttS qv r1 ⊑♯ InitSttS qv r2.
Axiom PDenSetOrder_U : 
    forall {qs : QvarScope} r1 r2 (qv : qs) (U : UnitaryOpt qv),
        r1 ⊑♯ r2 -> UapplyS U r1 ⊑♯ UapplyS U r2.
Axiom PDenSetOrder_M : 
    forall {qs : QvarScope} r1 r2 (qv_m : qs) (m : MeaOpt qv_m) (result : bool),
        r1 ⊑♯ r2 -> MapplyS m result r1 ⊑♯ MapplyS m result r2.




(* chain and CPO conclusions *)

(** Define the increasing set and least upper bound *)
Record chain (T : Type) := mk_chain {
    chain_obj : nat -> 𝒫(T);
    (** Here for simplicity we take the inverse direction *)
    chain_prop : forall n, chain_obj n ⊇ chain_obj n.+1;
}.
Notation " ch _[ n ] " := (chain_obj ch n) (at level 40) : QTheorySet_scope.

(** Convert a singal element into a list *)
Definition singleton_chain_obj {H : HilbertSpace} rho_s 
    : nat -> PDensitySet H :=
    fun => rho_s.

Lemma singleton_chain_prop {H : HilbertSpace} (rho_s : PDensitySet H) 
    : forall n, singleton_chain_obj rho_s n ⊑♯ singleton_chain_obj rho_s n.+1.
Proof. rewrite /singleton_chain_obj => n => //=. Qed.
Arguments singleton_chain_prop {H} rho_s.

Definition singleton_chain {H : HilbertSpace} rho_s : chain 𝒟( H )⁻ :=
    mk_chain (singleton_chain_prop rho_s).

Coercion singleton_chain : PDensitySet >-> chain.

(** Prove the loose criterion of chain equivalence *)
Lemma chain_eqP H : forall (ch1 ch2 : chain H),
        ch1 = ch2 <-> chain_obj ch1 = chain_obj ch2.
Proof. split. by move => -> //.
    move => Heq. destruct ch1 as [obj1 p1], ch2 as [obj2 p2]. simpl in Heq.
    move : p1 p2. rewrite Heq => p1 p2. by rewrite (proof_irrelevance _ p1 p2).
Qed.

Axiom chain_limit : forall T (ch : chain T), 𝒫(T).
Notation " 'lim→∞' ( ch ) " := (@chain_limit _ ch) 
    (at level 200) : QTheorySet_scope.

Axiom chain_limit_ub : forall T (ch : chain T) n,
    ch _[n] ⊇ lim→∞ (ch).

Axiom chain_limit_lub : forall T (ch : chain T) rho_ub,
    (forall n, ch _[n] ⊇ rho_ub) -> lim→∞ (ch) ⊇ rho_ub.

Lemma singleton_chain_limit (H : HilbertSpace) (rho_s : PDensitySet H) :
    lim→∞ (rho_s) = rho_s.
Proof.
    apply PDenSetOrder_asymm.
    apply chain_limit_lub. 
    rewrite /singleton_chain /singleton_chain_obj => n => //=.
    have temp := @chain_limit_ub _ (singleton_chain rho_s). 
    by apply (temp O).
Qed.

Lemma repeat_chain_limit (T : Type) (ch : chain T) x :
    (forall i, ch _[i] = x) -> lim→∞ (ch) = x.
Proof. move => H.
    apply subset_asymm.
    transitivity (ch _[1]). by apply chain_limit_ub. by rewrite H.
    apply chain_limit_lub. move => i. by rewrite H.
Qed.



(* chain_add *)
Definition chain_add_obj (H : HilbertSpace) 
    (ch_obj1 ch_obj2 : nat -> PDensitySet H) :=
    fun n => ch_obj1 n + ch_obj2 n.
Lemma chain_add_prop (H : HilbertSpace) (ch1 ch2 : chain 𝒟( H )⁻) :
    let ch := chain_add_obj (chain_obj ch1) (chain_obj ch2) in 
        forall n, ch n ⊑♯ ch n.+1.
Proof. move => ch n. rewrite /ch /chain_add_obj. apply PDenSetOrder_add_split.
    by apply ch1. by apply ch2.
Qed.
Arguments chain_add_prop {H} ch1 ch2.

Definition chain_add H (ch1 ch2 : chain 𝒟( H )⁻) : chain 𝒟( H )⁻ :=
    mk_chain (chain_add_prop ch1 ch2).

(** We still need the assumption that addition is continuous *)
Axiom add_continuous : forall H (ch1 ch2 : chain 𝒟( H )⁻),
    (lim→∞(ch1)) + (lim→∞(ch2)) = lim→∞ (chain_add ch1 ch2).


(* chain_cv_comb *)
Definition chain_cvcomb_obj (H : HilbertSpace) p
    (ch_obj1 ch_obj2 : nat -> PDensitySet H) :=
    fun n => (ch_obj1 n) [p⊕] (ch_obj2 n).
Lemma chain_cvcomb_prop (H : HilbertSpace) p (ch1 ch2 : chain 𝒟( H )⁻) :
    let ch := chain_cvcomb_obj p (chain_obj ch1) (chain_obj ch2) in 
        forall n, ch n ⊑♯ ch n.+1.
Proof. move => ch n. rewrite /ch /chain_cvcomb_obj. 
    apply PDensetOrder_cv_comb_split.
    by apply ch1. by apply ch2.
Qed.
Arguments chain_cvcomb_prop {H} p ch1 ch2.

Definition chain_cvcomb H p (ch1 ch2 : chain 𝒟( H )⁻) : chain 𝒟( H )⁻ :=
    mk_chain (chain_cvcomb_prop p ch1 ch2).

(** We still need the assumption that addition is continuous *)
Axiom cvcomb_continuous : forall H p (ch1 ch2 : chain 𝒟( H )⁻),
    (lim→∞(ch1)) [p⊕] (lim→∞(ch2)) = lim→∞ (chain_cvcomb p ch1 ch2).


(* chain_union *)
Definition chain_union_obj (H : HilbertSpace) (ch1 ch2 : chain 𝒟( H )⁻) :=
    fun n => (ch1 _[n]) ∪ (ch2 _[n]).
Lemma chain_union_prop (H : HilbertSpace) (ch1 ch2 : chain 𝒟( H )⁻) :
    forall n, chain_union_obj ch1 ch2 n ⊑♯ chain_union_obj ch1 ch2 n.+1.
Proof. move => n. rewrite /chain_union_obj. apply PDenSetOrder_union_split.
    by apply ch1. by apply ch2.
Qed.
Arguments chain_union_prop {H} ch1 ch2.

(** union chain is needed for proving parallel statement *)
Definition chain_union H (ch1 ch2 : chain 𝒟( H )⁻) : chain 𝒟( H )⁻ :=
    mk_chain (chain_union_prop ch1 ch2).

(** We still need the assumption that union is continuous *)
Axiom union_continuous : forall H (ch1 ch2 : chain 𝒟( H )⁻),
    (lim→∞(ch1)) ∪ (lim→∞(ch2)) = lim→∞ (chain_union ch1 ch2).


(* The chain of InitSttS ch *)
Definition InitStt_chain_obj {qs : QvarScope} (qv : qs) (ch : chain 𝒟(qs)⁻) :=
    fun i => InitSttS qv (ch _[i]).
Lemma InitStt_chain_prop {qs : QvarScope} (qv : qs) (ch : chain 𝒟(qs)⁻)
    : forall i, InitStt_chain_obj qv ch i ⊑♯ InitStt_chain_obj qv ch i.+1.
Proof.
    rewrite /InitStt_chain_obj => i. apply PDenSetOrder_Init. by apply ch.
Qed.
Arguments InitStt_chain_prop {qs} qv ch.

Definition InitStt_chain {qs : QvarScope} (qv : qs) (ch : chain 𝒟(qs)⁻) :=
    mk_chain (InitStt_chain_prop qv ch).

(** We still need the assumption that addition is continuous *)
Axiom init_continuous : forall {qs : QvarScope} (qv : qs) (ch : chain 𝒟(qs)⁻),
    InitSttS qv (lim→∞ (ch)) = lim→∞ (InitStt_chain qv ch).

(* The chain of UapplyS U ch *)
Definition Uapply_chain_obj 
    {qs : QvarScope} (qv : qs) (U : UnitaryOpt qv) (ch : chain 𝒟(qs)⁻) :=
    fun i => UapplyS U (ch _[i]).
Lemma Uapply_chain_prop 
    {qs : QvarScope} (qv : qs) (U : UnitaryOpt qv) (ch : chain 𝒟(qs)⁻)
    : forall i, Uapply_chain_obj U ch i ⊑♯ Uapply_chain_obj U ch i.+1.
Proof.
    rewrite /Uapply_chain_obj => i. apply PDenSetOrder_U. by apply ch.
Qed.
Arguments Uapply_chain_prop {qs} {qv} U ch.

Definition Uapply_chain 
    {qs : QvarScope} (qv : qs) (U : UnitaryOpt qv) (ch : chain 𝒟(qs)⁻) :=
    mk_chain (Uapply_chain_prop U ch).

(** We still need the assumption that addition is continuous *)
Axiom unitary_continuous : 
    forall {qs : QvarScope} (qv : qs) (U : UnitaryOpt qv) (ch : chain 𝒟(qs)⁻),
    UapplyS U (lim→∞ (ch)) = lim→∞ (Uapply_chain U ch).


(* The chain of MapplyS M ch result *)
Definition Mapply_chain_obj 
    {qs : QvarScope} (qv : qs) (M : MeaOpt qv) (r : bool) (ch : chain 𝒟(qs)⁻) :=
    fun i => MapplyS M r (ch _[i]).
Lemma Mapply_chain_prop 
    {qs : QvarScope} (qv : qs) (M : MeaOpt qv) (ch : chain 𝒟(qs)⁻) (r : bool)
    : forall i, Mapply_chain_obj M r ch i ⊑♯ Mapply_chain_obj M r ch i.+1.
Proof.
    rewrite /Mapply_chain_obj => i. apply PDenSetOrder_M. by apply ch.
Qed.
Arguments Mapply_chain_prop {qs} {qv} M ch r.

Definition Mapply_chain 
    {qs : QvarScope} (qv : qs) (M : MeaOpt qv) (r : bool) (ch : chain 𝒟(qs)⁻) :=
    mk_chain (Mapply_chain_prop M ch r).

(** We still need the assumption that addition is continuous *)
Axiom mea_continuous : forall {qs : QvarScope} 
    (qv : qs) (M : MeaOpt qv) (ch : chain 𝒟(qs)⁻) (r : bool),
    MapplyS M r (lim→∞ (ch)) = lim→∞ (Mapply_chain M r ch).




(* The chain of UapplyS U ch *)
Definition bigU_chain_obj (T : Type) (ch : chain 𝒫(T)) :=
    fun i => ⋃ (ch _[i]).
Lemma bigU_chain_prop (T : Type) (ch : chain 𝒫(T))
    : forall i, bigU_chain_obj ch i ⊇ bigU_chain_obj ch i.+1.
Proof.
    rewrite /bigU_chain_obj => i. apply big_union_mor_sub. by apply ch.
Qed.
Arguments bigU_chain_prop {T} ch.

Definition bigU_chain (T : Type) (ch : chain 𝒫(T)) :=
    mk_chain (bigU_chain_prop ch).

(** We still need the assumption that big_union is continuous *)
Axiom bigU_continuous : 
    forall (T : Type) (ch : chain 𝒫(T)),
    ⋃ (lim→∞ (ch)) = lim→∞ (bigU_chain ch).


(* The chain of mapR *)
Definition fmap_chain_obj (T V: Type) (f : T -> V) (ch : chain T):=
    fun i => f [<] (ch _[i]).
Lemma fmap_chain_prop (T V: Type) (f : T -> V) (ch : chain T)
    : forall i, fmap_chain_obj f ch i ⊇ fmap_chain_obj f ch i.+1.
Proof.
    move => i. apply mapR_mor_sub => //. by apply ch.
Qed.
Arguments fmap_chain_prop {T V} f ch.

Definition fmap_chain (T V: Type) (f : T -> V) (ch : chain T) :=
    mk_chain (fmap_chain_prop f ch).

(** We still need the assumption that big_union is continuous *)
Axiom fmap_continuous : 
    forall (T V: Type) (f : T -> V) (ch : chain T),
        f [<] (lim→∞ (ch)) = lim→∞ (fmap_chain f ch).
    

End QTheorySetType.