(** Isomorphic *)

From Ranko Require Export TerminalDogma.premises.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Module Isomorphic.

Definition injective (X Y : Type) (f : X -> Y) := 
    forall x y, x <> y -> f x <> f y.

Lemma injectiveP (X Y : Type) (f : X -> Y) : 
    (forall x y, f x = f y -> x = y) -> injective f.
Proof. rewrite /injective => H x y Hneq Heq. by apply /Hneq /H. Qed.

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



(** Open Question : Is isomorphic extensionality consistent with Coq and other
    logic assumptions? (I believe the answer is Yes.) *)




Theorem pred_replace : 
    forall (A B : Type) (P : Type -> Prop), A = B -> (P A <-> P B).
Proof.
    move => A B P Heq. by case Heq.
Qed.

(** Open question : if pred_replace has the following form:

        isomorphic A B -> (P A <-> P B) 

    Then the [isomorphic_extensionality] axiom is not necessary for theory
    transport.
    I believe this claim is correct.
*)


(*
Theorem iso_comp_dep (A B: Type) (C : A -> Type) (D : B -> Type):
        isomorphic A B -> isomorphic C D -> 
            isomorphic (fun (a : A) => C a) (fun (b : B) => D b).
*)

Theorem iso_comp (A B C D : Type) : 
    isomorphic A B -> isomorphic C D -> isomorphic (A -> C) (B -> D).
Abort.

Definition transport (A B : Type) : A = B -> A -> B.
Proof. move => H a. by rewrite -H. Defined.
Definition transport_iso (A B : Type) : isomorphic A B -> A -> B.
Proof. move => H. apply isomorphic_extensionality in H. by apply transport.
Qed.

End Isomorphic.