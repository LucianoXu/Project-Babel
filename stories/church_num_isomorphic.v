
(** Church Number ~ nat *)

Require Import Arith.
Require Export FunctionalExtensionality.
Require Export ProofIrrelevance.


Notation cnat_ctt := (forall (X : Type), (X -> X) -> X -> X).

    Inductive valid_cnat : cnat_ctt -> Prop := 
    | Ocnat : valid_cnat (fun (X : Type) (f : X -> X) (x : X) => x)
    | Scnat (c : cnat_ctt) (H : valid_cnat c) : valid_cnat (fun (X : Type) (f : X -> X) (x : X) => f (c X f x)).
    
    (** There is a practical example: Church numbers. *)
    Record cnat := mk_cnat {
        cn :> cnat_ctt;
        cn_proof : valid_cnat cn;
    }.
    
    Lemma cnat_eq : forall c1 c2 : cnat, c1 = c2 <-> (cn c1) = (cn c2).
    Proof.
        move => c1 c2. split. by move => ->.
        destruct c1 as [c1 p1], c2 as [c2 p2] => //= H.
        move : p1 p2. rewrite H => p1 p2. by rewrite (proof_irrelevance _ p1 p2).
    Qed.
    
    Definition cnat2nat (c : cnat) : nat := c nat S O.
    
    Fixpoint nat2cnat_cn (n : nat) : forall X : Type, (X -> X) -> X -> X :=
        fun (X : Type) (f : X -> X) (x : X) =>
            match n with
            | O => x
            | S n' => f (nat2cnat_cn n' f x)
            end.
    
    Definition nat2cnat (n : nat) : cnat.
    Proof.
        refine (@mk_cnat (nat2cnat_cn n) _).
        elim: n. apply Ocnat.
        move => n IHn. apply Scnat. apply IHn.
    Defined.
        
    
    
    
    
    Lemma bijection_nat2cnat : bijective nat2cnat.
    Proof. apply inv_is_bij. rewrite /invertible. exists cnat2nat. split.
    
        elim => //=. move => n. by rewrite /cnat2nat => ->.
    
        move => [y Hy]. apply cnat_eq => //=. 
        apply functional_extensionality_dep => X.
        apply functional_extensionality => f. 
        apply functional_extensionality => x.
        elim : Hy => //=.
        move => c _ IHc.  by rewrite IHc.
    Qed.
    
    Theorem cnat_nat_iso : isomorphic nat cnat.
    Proof. exists nat2cnat. by apply bijection_nat2cnat. Qed.
    
    Theorem cnat_nat_eq : nat:Type = cnat.
    Proof. apply isomorphic_extensionality. by apply cnat_nat_iso. Qed.
    
    
    
    Coercion cnat2nat : cnat >-> nat. 
    
    Coercion nat2cnat : nat >-> cnat. 
    
    
    Compute (10 _ S 0).
    Compute (10 _ (fun x => 2*x + 1) 0).

    
Goal inhabited cnat.
Proof. 
    Fail rewrite -cnat_nat_eq.
    (** M@GIC *)
    case cnat_nat_eq.
    constructor. by exact 1.
Qed.


(** This [theory_functor] can be considered as a `functor', meaning a `theory' about
    T. *)
    Definition theory_functor (T : Type) : Prop :=
        exists add_op : T -> T -> T, (forall a b, add_op a b = add_op b a).
    
    Lemma theory_functor_nat : theory_functor nat.
    Proof. exists Nat.add. apply Nat.add_comm. Qed.
        
    Lemma theory_functor_cnat : theory_functor cnat.
    Proof. case cnat_nat_eq. apply theory_functor_nat. Qed.
    
    (** We have transported the theories from [nat] to [cnat]. *)
    