(** function.v *)

From Ranko Require Import TerminalDogma.premises.

(*　世界の創造のため、魂の共鳴を聴くのだ！ *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Module Export Function.

Module Injective.

Definition injective (X Y : Type) (f : X -> Y) := 
    forall x y, f x = f y -> x = y.

(** There is a slightly different definition *)
Definition injective_alt (X Y : Type) (f : X -> Y) :=
    forall x y, x <> y -> f x <> f y.

Lemma injectiveP (X Y : Type) (f : X -> Y) : 
    injective f -> injective_alt f.
Proof. rewrite /injective => H x y Hneq Heq. by apply /Hneq /H. Qed.

(** The inverse direction requires X to be a [eqType]. *)
Lemma injectivePinv (X : eqType) (Y : Type) (f : X -> Y) : 
    injective_alt f -> injective f.
Proof. rewrite /injective_alt => H x y Heq. apply /eqP.
    case E : (x == y) => //. move /eqP : E => {}/H.
    by move : Heq => ->.
Qed.
        
Record class (X Y : Type) (f : X -> Y):= Class {
    prop : forall x y, x <> y -> f x <> f y;
}.

Structure type := Pack {
    A : Type;
    B : Type;
    obj : A -> B;
    class_of : class A B obj;
}.

Locate injective.

End Injective.



Definition surjective (X Y: Type) (f : X -> Y) :=
    forall y, exists x, f x = y.

Definition bijective (X Y: Type) (f : X -> Y) :=
    injective f /\ surjective f.
    

(** A and B are isomorphic types, if there exists a bijection between A and B *)
Definition isomorphic (A B : Type) :=
    exists f : A -> B, bijective f.

Definition IsomorphicExtensionality := forall A B:Type, isomorphic A B -> A = B.
    
(** Axiom: isomorphic structures are the same. *)
Axiom isomorphic_extensionality : IsomorphicExtensionality.


Definition invertible (X Y : Type) (f : X -> Y) :=
    exists g : Y -> X, (forall x, g (f x) = x) /\ (forall y, f (g y) = y).

(** invertibale functions are bijections *)
Lemma inv_is_bij (X Y : Type) (f : X -> Y) : invertible f -> bijective f.
Proof. move => [g [H1 H2]]. split. 
    apply injectiveP. rewrite /injective => a b Heq. 
    rewrite -(H1 a) Heq. by apply H1.

    rewrite /surjective => y. by exists (g y); apply H2.
Qed.
