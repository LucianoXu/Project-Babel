(** * SetAdvanced.v : Advanced theories about set theory. *)


From Ranko Require Import TerminalDogma.premises 
                          TerminalDogma.Extensionality
                          .

From Ranko Require Export NaiveSet.

From Coq Require Import Classical.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.




(** bigI is the greatest lower bound in the sense of subset order. *)
Lemma bigI_lb (T : Type) (A : 𝒫(𝒫(T))) :
    forall' X ∈ A, ⋂ A ⊆ X.
Proof. 
    rewrite /big_itsct /subset => //= X HX x Hx.
    by apply Hx.
Qed.

Lemma bigI_glb (T : Type) (A : 𝒫(𝒫(T))) (X : 𝒫(T)):
    (forall' a ∈ A, X ⊆ a) -> X ⊆ ⋂ A.
Proof.
    rewrite /big_itsct /subset => //= H x Hxin Y HYin.
    by apply (H Y) => //.
Qed.

(** bigU is the least upper bound in the sense of subset order. *)
Lemma bigU_ub (T : Type) (A : 𝒫(𝒫(T))) :
    forall' X ∈ A, X ⊆ ⋃ A.
Proof. 
    rewrite /big_union /subset => //= X HX x Hx.
    exists X. by split.
Qed.

Lemma bigU_lub (T : Type) (A : 𝒫(𝒫(T))) (X : 𝒫(T)):
    (forall' a ∈ A, a ⊆ X) -> ⋃ A ⊆ X.
Proof.
    rewrite /big_union /subset => //= H a [Y [HYin Hain]].
    by apply (H Y) => //.
Qed.



(** subset morphism of ⋃ ◦ (f [<]) set *)
(** Here a more precise description of the relation between f and g is 
    something like 'subfunction' 
    TODO #13 *)
Lemma bigU_mapR_mor_sub {X Y: Type} (f g: X -> 𝒫(Y)) (A B: 𝒫(X)):
    A ⊆ B -> (forall t, f t ⊆ g t) ->

        ⋃ (f [<] A) ⊆ ⋃ (g [<] B).

Proof.
    rewrite /subset => HAinB Hfleg v [Sv] [[t] [Htin HSveq] Hvin].
    have H := Hfleg t v. rewrite HSveq in H. have H' := H Hvin.
    exists (g t). split => //. exists t. split => //. by apply HAinB.
Qed.

Lemma bigU_sgt {X : Type} (A : 𝒫(X)) :

        ⋃ (singleton A) = A.

Proof. apply seteqP => //= x. split.
    by move => [] X0 [] ->.
    move => Hxin. exists A. by split.
Qed.

Lemma bigI_sgt {X : Type} (A : 𝒫(X)) :

        ⋂ (singleton A) = A.

Proof. apply seteqP => //= x. split.
    by move => /(_ A Logic.eq_refl).
    by move => Hxin X0 ->.
Qed.


(** About big opertor and mappings *)


Lemma bigU_fun_rei {X Y: Type} (A : 𝒫(X)) (f : X -> Y):

        ⋃ { {{ f a }}, a | a ∈ A } = f [<] A.
    
Proof. rewrite /mapR /big_union. apply seteqP => x. split.
    move => [Sy] [[x0 [Hx0in HSyeq]]]. rewrite -{}HSyeq.
    rewrite singletonP => ->. exists x0. by split.
    move => [x0 [Hx0in Hxeq]].
    eexists. split. eexists. split. apply Hx0in. rewrite Hxeq.
    by []. by apply singletonP.
Qed.
    

Lemma bigU_rei {X : Type} (A : 𝒫(X)) :

        ⋃ { {{ a }}, a | a ∈ A } = A.

Proof. rewrite /big_union. apply seteqP => x. split.
    move => [Sx] [[x0 [Hx0in HSxeq]]]. rewrite -{}HSxeq. 
    by rewrite singletonP => ->.
    move => Hx.
    exists ({{x}}). split. exists x. by split. by apply singletonP.
Qed.



Lemma bigU_union_dist {X : Type} (A B: 𝒫(𝒫(X))) :
    
        ⋃ (A ∪ B) = (⋃ A) ∪ (⋃ B).

Proof.
    rewrite /union /big_union. apply seteqP => x. split.
    by move => [SX] [[HSXin|HSXin]] Hxin ; [left|right]; exists SX; split.
    by move => [[SX [HSXin Hxin]]|[SX [HSXin Hxin]]]; exists SX; split => //;
    [left|right] => //.
Qed.

Lemma bigI_itsct_dist {X : Type} (A B: 𝒫(𝒫(X))) :
    
        ⋂ (A ∩ B) = (⋂ A) ∩ (⋂ B).

Proof.
Admitted.

Lemma bigI_itsct_sgt_dist   {X : Type} (A : 𝒫(X)) (B: 𝒫(𝒫(X))) :
    
        ⋂ (singleton A ∪ B) = A ∩ ⋂ B.

Proof.
Admitted.

(** Note: The following one is also a unique lemma. *)
Lemma union_bigU_mapR_dist {X Y : Type} (A : 𝒫(X)) (f g : X -> 𝒫(Y)) :

        (⋃ (f [<] A) ) ∪ (⋃ (g [<] A)) = ⋃ { f x ∪ g x, x | x ∈ A }.

Proof.
    rewrite /union /big_union. apply seteqP => x. split.
    move => [].
    
    { move => [y] [[x0 [Hx0in Hyeq]]] Hxin.
    exists ((f x0)∪(g x0)). split =>//. exists x0. split => //. rewrite Hyeq.
    by apply in_union_l. }
    
    { move => [y] [[x0 [Hx0in Hyeq]]] Hxin.
    exists ((f x0)∪(g x0)). split =>//. exists x0. split => //. rewrite Hyeq.
    by apply in_union_r. }

    move => [y] [[x0] [Hx0in Hyeq]] Hxin. rewrite -{}Hyeq in Hxin.
    destruct Hxin.

    { left. exists (f x0). split => //. exists x0. by split. }
    { right. exists (g x0). split => //. exists x0. by split. }
Qed.


Lemma mapR_in {X Y : Type} (A : 𝒫(X)) (f : X -> Y) :
    forall x : X, 

        x ∈ A -> f x ∈ f [<] A.

Proof. rewrite /mapR => x ? //=. by exists x. Qed.


Lemma mapL_in {X Y : Type} (F : 𝒫(X -> Y)) (x : X) :
    forall f : X -> Y,

        f ∈ F -> f x ∈ F [>] x.

Proof. rewrite /mapL => f ? //=. by exists f. Qed.

(*************************)
(** ESPECIALLY IMPORTANT *)
(*************************)

Lemma mapR_bigU_swap {X Y : Type} (f : X -> Y) (A : 𝒫(𝒫(X))):
    
        { f x, x | x ∈ (⋃ A) } = ⋃ { f [<] a , a | a ∈ A }.

Proof.
    rewrite /big_union /mapR. apply /seteqP => x //=. split.

    move => [x0] [[a [Hain Hx0in]]] Hfeq.
    eexists. split. exists a. split => //.
    exists x0. by split.

    move => [y] [[a [Ha Hyeq]]] Heq.
    rewrite -Hyeq in Heq. destruct Heq as [x0 [Hx01 Hx02]].
    exists x0. split => //. exists a. by split.
Qed.


Lemma mapR_bigU_swapF {X Y : Type} (f : X -> Y) :

        (f [<]) ◦ ⋃ = ⋃ ◦ ((f [<])[<]).

Proof.
    apply functional_extensionality => A.
    by apply mapR_bigU_swap.
Qed.


(*************************)
(** ESPECIALLY IMPORTANT *)
(*************************)


Lemma double_mapR {X Y Z : Type} (g : X -> Y) (f : Y -> Z) (A : 𝒫(X)) :

        { f b , b | b ∈ g [<] A } = { f (g a), a | a ∈ A }.

Proof.
    rewrite /mapR. apply /seteqP => x //=. split.
    move => [v] [[a [Hain Hveq]] Hxeq]. exists a. rewrite Hveq. by split.
    move => [a] [Hain Hxeq]. exists (g a). split => //=. by exists a.
Qed.

Lemma double_mapRF {X Y Z : Type} (g : X -> Y) (f : Y -> Z) :
    
        f[<] ◦ g[<] = (f ◦ g)[<].

Proof.
    apply functional_extensionality => x.
    move : (double_mapR g f x).
    rewrite !mapR_fold. rewrite fun_compP.
    by [].
Qed.
    

(*************************)
(** ESPECIALLY IMPORTANT *)
(*************************)

Lemma bigU_swap {X : Type} (A : 𝒫(𝒫(𝒫(X)))) :

        ⋃ { ⋃ a , a | a ∈ A } = ⋃ (⋃ A).

Proof.
    rewrite /big_union. apply /seteqP => x. split.

    move => [Sx] [[SSx] [HSSxin HSxeq]] Hxin.
    rewrite -HSxeq in Hxin. destruct Hxin as [Sx0 [HSx0in Hxin]].
    exists Sx0. split => //. exists SSx. by split.

    move => [Sx] [[SSx] [HSSxin HSxin]] Hxin.
    eexists. split. eexists. split; last first. eexists. 2: eexists.
    apply HSSxin. split. apply HSxin. by apply Hxin.
Qed.

Lemma bigU_swapF {X : Type}  :

        (@big_union X) ◦ (⋃[<]) = ⋃ ◦ ⋃.

Proof.
    apply functional_extensionality => x.
    by apply bigU_swap.
Qed.


Lemma bigU_fun_dist {X Y: Type} (f : X -> 𝒫(𝒫(Y))) (A : 𝒫(X)):

        ⋃ { ⋃ (f a) , a | a ∈ A } = ⋃ (⋃ (f [<] A)).

Proof.
    
    (** transform into the function equality *)
    rewrite mapR_fold. 
    equal_f_comp A.

    rewrite -[RHS]fun_assoc.
    rewrite -bigU_swapF.
    rewrite fun_assoc.
    by rewrite -double_mapRF.
Qed.

Lemma bigU_fun_distF {X Y: Type} (f : X -> 𝒫(𝒫(Y))):

        ⋃ ◦ (⋃ ◦ f)[<] = ⋃ ◦ ⋃ ◦ f[<].

Proof.
    apply functional_extensionality => x.
    by apply bigU_fun_dist.
Qed.


(*###########################################################################*)
(** relation morphisms *)
Add Parametric Morphism {X Y : Type} : (@UmapRL X Y)
    with signature (@subset (X -> Y)) ==> 
        (@subset X) ==> (@subset Y) as UmapRL_mor_sub.
Proof.
    rewrite /UmapRL => F G HFinG A B HAinB //=.
    apply bigU_mapR_mor_sub => //= x.
    by apply mapR_mor_sub.
Qed.