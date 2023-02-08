(** set_killer_test.v *)

From Ranko Require Import TerminalDogma.premises 
                          TerminalDogma.Extensionality.

From Ranko Require Export SetFacility.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Lemma bigI_lb (T : Type) (A : 𝒫(𝒫(T))) :
    forall' X ∈ A, ⋂ A ⊆ X.
Proof. set_killer. Qed.

Lemma bigI_glb (T : Type) (A : 𝒫(𝒫(T))) (X : 𝒫(T)):
    (forall' a ∈ A, X ⊆ a) -> X ⊆ ⋂ A.
Proof. set_killer. Qed.

(** bigU is the least upper bound in the sense of subset order. *)
Lemma bigU_ub (T : Type) (A : 𝒫(𝒫(T))) :
    forall' X ∈ A, X ⊆ ⋃ A.
Proof. set_killer. Qed.

Lemma bigU_lub (T : Type) (A : 𝒫(𝒫(T))) (X : 𝒫(T)):
    (forall' a ∈ A, a ⊆ X) -> ⋃ A ⊆ X.
Proof. set_killer. Qed.



(** subset morphism of ⋃ ◦ (f [<]) set *)
(** Here a more precise description of the relation between f and g is 
    something like 'subfunction' 
    TODO #13 *)
Lemma bigU_mapR_mor_sub {X Y: Type} (f g: X -> 𝒫(Y)) (A B: 𝒫(X)):
    A ⊆ B -> (forall t, f t ⊆ g t) ->

        ⋃ (f [<] A) ⊆ ⋃ (g [<] B).

Proof. set_killer. Qed.

Lemma bigU_sgt {X : Type} (A : 𝒫(X)) :

        ⋃ (singleton A) = A.

Proof. set_killer. Qed.

Lemma bigI_sgt {X : Type} (A : 𝒫(X)) :

        ⋂ (singleton A) = A.

Proof. set_killer. Qed.


(** About big opertor and mappings *)


Lemma bigU_fun_rei {X Y: Type} (A : 𝒫(X)) (f : X -> Y):

        ⋃ { {{ f a }}, a | a ∈ A } = f [<] A.
    
Proof. set_killer. Qed.
    

Lemma bigU_rei {X : Type} (A : 𝒫(X)) :

        ⋃ { {{ a }}, a | a ∈ A } = A.

Proof. set_killer. Qed.



Lemma bigU_union_dist {X : Type} (A B: 𝒫(𝒫(X))) :
    
        ⋃ (A ∪ B) = (⋃ A) ∪ (⋃ B).

Proof. set_killer. Qed.



Lemma bigI_itsct_sgt_dist   {X : Type} (A : 𝒫(X)) (B: 𝒫(𝒫(X))) :
    
        ⋂ (singleton A ∪ B) = A ∩ ⋂ B.

Proof. set_killer. Qed.

(** Note: The following one is also a unique lemma. *)
Lemma union_bigU_mapR_dist {X Y : Type} (A : 𝒫(X)) (f g : X -> 𝒫(Y)) :

        (⋃ (f [<] A) ) ∪ (⋃ (g [<] A)) = ⋃ { f x ∪ g x, x | x ∈ A }.

Proof. set_killer. Qed.


Lemma mapR_in {X Y : Type} (A : 𝒫(X)) (f : X -> Y) :
    forall x : X, 

        x ∈ A -> f x ∈ f [<] A.

Proof. set_killer. Qed.


Lemma mapL_in {X Y : Type} (F : 𝒫(X -> Y)) (x : X) :
    forall f : X -> Y,

        f ∈ F -> f x ∈ F [>] x.

Proof. set_killer. Qed.


(*************************)
(** ESPECIALLY IMPORTANT *)
(*************************)

Lemma mapR_bigU_swap {X Y : Type} (f : X -> Y) (A : 𝒫(𝒫(X))):
    
        f [<] (⋃ A) = ⋃ (f [<] [<] A).

Proof. set_killer. Qed.

Lemma mapR_bigU_swapF {X Y : Type} (f : X -> Y) :

        (f [<]) ◦ ⋃ = ⋃ ◦ ((f [<])[<]).

Proof.
    apply functional_extensionality => A.
    set_killer.
Qed.

Lemma mapL_bigU_swap {X Y : Type} (F : 𝒫(𝒫(X -> Y))) (a : X):

        (⋃ F) [>] a = ⋃ { f [>] a , f | f ∈ F }.
    
Proof. set_killer. Qed.

Lemma mapL_bigU_swapF {X Y : Type} (F : 𝒫(𝒫(X -> Y))) :
    
        (⋃ F) [>] = fun a => ⋃ { f [>] a , f | f ∈ F }.

Proof.
    apply functional_extensionality => x.
    set_killer.
Qed.


(*************************)
(** ESPECIALLY IMPORTANT *)
(*************************)


Lemma double_mapR {X Y Z : Type} (g : X -> Y) (f : Y -> Z) (A : 𝒫(X)) :

        { f b , b | b ∈ g [<] A } = { f (g a), a | a ∈ A }.

Proof. set_killer. Qed.

Lemma double_mapRF {X Y Z : Type} (g : X -> Y) (f : Y -> Z) :
    
        f[<] ◦ g[<] = (f ◦ g)[<].

Proof.
    apply functional_extensionality => x.
    set_killer.
Qed.
    

(*************************)
(** ESPECIALLY IMPORTANT *)
(*************************)

Lemma bigU_swap {X : Type} (A : 𝒫(𝒫(𝒫(X)))) :

        ⋃ { ⋃ a , a | a ∈ A } = ⋃ (⋃ A).

Proof. set_killer. Qed.

Lemma bigU_swapF {X : Type}  :

        (@big_union X) ◦ (⋃[<]) = ⋃ ◦ ⋃.

Proof.
    apply functional_extensionality => x.
    set_killer.
Qed.


Lemma bigU_fun_dist {X Y: Type} (f : X -> 𝒫(𝒫(Y))) (A : 𝒫(X)):

        ⋃ { ⋃ (f a) , a | a ∈ A } = ⋃ (⋃ (f [<] A)).

Proof. set_killer. Qed.

Lemma bigU_fun_distF {X Y: Type} (f : X -> 𝒫(𝒫(Y))):

        ⋃ ◦ (⋃ ◦ f)[<] = ⋃ ◦ ⋃ ◦ f[<].

Proof.
    apply functional_extensionality => x.
    set_killer.
Qed.


(** UmapLR *)
Lemma UmapLR_bigU_swap {X Y: Type} (F : 𝒫(X -> Y)) (A : 𝒫(𝒫(X))) :

        F [><] (⋃ A) = ⋃ (⋃ (F[>][<][<] A)).
    
Proof. set_killer. Qed.

Lemma parlift_mapR {X Y Z : Type} (f : X -> Y -> Z) (A : 𝒫(𝒫(X))) :

    (fun a => f [<] a [><] ) [<] A = UmapLR [<] (f[<][<]A).

Proof. set_killer. Qed.


Lemma bigU_mapLR_swap {X Y : Type} (F : 𝒫(𝒫(X -> Y))) (A : 𝒫(X)): 

    (⋃ F) [><] A = ⋃ ((UmapLR [<] F) [>] A).

Proof. set_killer. Qed.    

Lemma UmapLR_2bigU_swap {X Y : Type} (F : 𝒫(𝒫(X -> Y))) (A : 𝒫(𝒫(X))):

    (⋃ F) [><] (⋃ A) = ⋃ ((UmapLR [<] F) [><] A).

Proof. set_killer. Qed.


Lemma funlift2_bigU_swap {X Y Z: Type} (f : X -> Y -> Z) A B :
    (funlift2 f) (⋃ A) (⋃ B) = ⋃ (funlift2 f [<] A [><] B).
Proof. set_killer. Qed.





(*###########################################################################*)
(** relation morphisms *)
Add Parametric Morphism {X Y : Type} : (@UmapLR X Y)
    with signature (@subset (X -> Y)) ==> 
        (@subset X) ==> (@subset Y) as UmapLR_mor_sub.
Proof. set_killer. Qed.
