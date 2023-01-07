From Ranko Require Export FQP.premises.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Ranko Require FieldTheories.
From Ranko Require TerminalDogma.Sequence.





Module Export VectorSpaceTheory.

Export FieldTheories.FieldTheory.
Export TerminalDogma.Sequence.

Declare Scope Vspace_scope.
Open Scope Vspace_scope.

(** Definition 2.1.1 (vector space) *)
Record vspace (F : field) := build_vspace {
    V :> Type;
    Vadd : V -> V -> V;
    Vscal : F -> V -> V;
    
    (** First four axioms states that a vector space is an Abelian group. *)
    (** comminitivity of addition *)
    Vadd_comm : forall u v : V, Vadd u v = Vadd v u;

    (** associativity of addition *)
    Vadd_assoc : forall u v w : V, Vadd u (Vadd v w) = Vadd (Vadd u v) w;

    (** identity element of addition *)
    V0 : V;
    Vadd_0_l : forall u : V, Vadd V0 u = u;

    (** opposite element of addition *)
    Vopp : V -> V;
    Radd_opp : forall u : V, Vadd u (Vopp u) = V0;


    (** scalar multiplication consistent with its definition in field F *)
    Vscal_cst : forall (a b : F) (u : V), 
        Vscal a (Vscal b u) = Vscal (rmul a b) u;

    (** identity element of scalar multiplication *)
    Vscal_1 : forall u : V, Vscal (rI F) u = u;

    (** distribution of scalar multiplication *)
    Vscal_dist : forall (a : F) (u v : V), 
        Vscal a (Vadd u v) = Vadd (Vscal a u) (Vscal a v);
    
    (** distribution of vector addition *)
    Vadd_dist : forall (a b : F) (u : V),
        Vscal (radd a b) u = Vadd (Vscal a u) (Vscal b u);
}.

Notation " a + b " := (Vadd a b) : Vspace_scope.
Notation " - a " := (Vopp a) : Vspace_scope.
(* Note : considering that the level for a + b is 50, the level for a * b is 40, 
    level 30 is appropriate for a ∗ b. *)
Notation " a '∗' b " := (Vscal a b) (at level 30): Vspace_scope.
Notation "𝟎" := ( V0 _ ) : Vspace_scope.

(** [] *)
About sequeN_fun_zip.
(** big sum *)
Definition linear_comb (F : field) (V : vspace F) (n : nat)
    (sf : sequeN F n) (sv : sequeN V n) : sequeN V n :=
    sequeN_fun_zip sf sv (@Vscal _ V).


End VectorSpaceTheory.