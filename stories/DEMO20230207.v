Require Import POrder POrderSet TerminalDogma.premises
                                TerminalDogma.Extensionality.
Require Import Relations.
Require Import SetFacility.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** Canonical structure *)

(** Enter the 'context' by introducing the canonical structures. *)
Import SubsetOrder.CanonicalStruct.

(** The single item [𝒫(nat)] has coercions to many notions related. *)
Check 𝒫(nat).
Check 𝒫(nat) : poset.
Check 𝒫(nat) : clattice.
Check 𝒫(nat) : cpo.

Axiom A : chain (𝒫(nat)).
Check (⊔ᶜᵖᵒ A).

(** the type of monotonic functions between [𝒫(nat)] and [𝒫(nat)] *)
Check [ 𝒫(nat) ↦ᵐ 𝒫(nat) ].


(** The system 'knows' that if we apply monotonic functions to a chain, we get
    a chain. *)
Axiom (f : 𝒫(nat) -> 𝒫(nat)) (monof : [ 𝒫(nat) ↦ᵐ 𝒫(nat) ]).

Check f [<] A : 𝒫( _ ).
Fail Check f [<] A : chain _. 

Check monof [<] A : 𝒫( _ ).
Check monof [<] A : chain _.


(** nonempty set *)
Check 𝒫(nat)₊.
Check union : 𝒫(nat) ->  𝒫(nat)-> 𝒫(nat).
(** Because of canonical structure, [union] 'remembers' its property about 
    nonempty sets. *)
Check union : 𝒫(nat)₊ -> 𝒫(nat) -> 𝒫(nat)₊.



(** Function lifting *)
Section FunctionLifting.

Variable (T V W: Type) (f : T -> V) (g : T -> V -> W).

(** function lifting of single-variable functions *)
Check f : T -> V.
Check f[<] : 𝒫(T) -> 𝒫(V).

(** function lifting of multi-variable functions *)
Check g                             : T -> V -> W.
Check g[<]                          : 𝒫(T) -> 𝒫(V -> W).
Check (fun a => g[<]a[>])           : 𝒫(T) -> V -> 𝒫(W).
Check (fun a => g[<]a[>][<])        : 𝒫(T) -> 𝒫(V) -> 𝒫(𝒫(W)).
Check (fun a b => ⋃(g[<]a[>][<]b))  : 𝒫(T) -> 𝒫(V) -> 𝒫(W).

Definition g_lifted := (fun a b => ⋃(g[<]a[>][<]b)).



Lemma continuity_f_lifted A : f[<](⋃ A) = ⋃ (f[<][<]A).
Proof. 
    equal_f_comp A.
    rewrite mapR_bigU_swapF. by [].

    Restart.
    seteq_killer. 
Qed.

Lemma continuity_g_lifted A B : g_lifted (⋃ A) (⋃ B) = ⋃ (g_lifted [<] A [><] B).
Proof. 
    rewrite /g_lifted.

    Restart.
    seteq_killer. 
Qed.

End FunctionLifting.


(** seteq_killer demo *)

Lemma Example1 {X Y: Type} (f : X -> 𝒫(𝒫(Y))):

    ⋃ ◦ (⋃ ◦ f)[<] = ⋃ ◦ ⋃ ◦ f[<].

Proof.
    apply functional_extensionality => A.
    seteq_killer.

    Undo.
    apply seteqP => x; split.
    set_simpl.
    set_move_up.
    set_move_down.
    set_simpl.
    set_move_up.
    set_move_down.
Qed.

Lemma Example2 {X : Type} (A B: 𝒫(𝒫(X))) :
    
        ⋃ (A ∪ B) = (⋃ A) ∪ (⋃ B).

Proof. 
    seteq_killer.
Qed.


(** WARNING: this is not correct. *)
Lemma Example3 {X : Type} (A B: 𝒫(𝒫(X))) :
    
        ⋂ (A ∩ B) = (⋂ A) ∩ (⋂ B).

Proof. 
    seteq_killer. 
Abort.

Lemma Example4 {X Y: Type} (F : 𝒫(X -> Y)) (A : 𝒫(𝒫(X))) :

    ⋃(F [>][<] (⋃ A)) = ⋃ (⋃ (F[>][<][<] A)).

Proof.
    seteq_killer.
Qed.

(** 2023/2/6 
    git commit: 48aac14771ce40140937bc45fc2f1aeb8123284e *)