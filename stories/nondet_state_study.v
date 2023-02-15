
From Babel Require Import TerminalDogma 
                          ExtraDogma.Extensionality.


From Coq Require Import Classical Reals.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation "[0, 1]" := [0, 1]R.
Local Notation "R+" := {r : R| r > 0}.

(** study of nondeterministic and probabilistic states *)

Inductive nd_state (A : Set) : Set :=
| det_item      (a : A)
| prob_comb     (p : [0, 1]) (s1 s2 : nd_state A)
| nd_comb       (s1 s2 : nd_state A).

Notation "` a" := (det_item a) (at level 30, format "` a").
Notation "a [ p ⊕ ] b" := (prob_comb p a b) 
    (at level 0, format "a  [ p ⊕ ]  b").
Notation "a □ b" := (nd_comb a b) (at level 50).


Parameter minR : R -> R -> R.
Notation " a ⊓ b " := (minR a b) (at level 70).
Axiom minR_le_l : forall a b, a ⊓ b < a.
Axiom minR_le_r : forall a b, a ⊓ b < b.

Fixpoint min_exp (A : Set) (α : A -> R+) (s : nd_state A): R :=
    match s with
    | `a => 
        proj1_sig (α a)
    | a [ p ⊕ ] b => 
        let r := proj1_sig p in 
            r * (min_exp α a) + (1 - r) * (min_exp α b)
    | a □ b =>
        (min_exp α a) ⊓ (min_exp α b)
    end.

(** The definition of canonical seems to need the sequence structure.
    Its too troublesome. *)
