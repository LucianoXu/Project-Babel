(** SetTactic.v : the tactics about sets *)

From Ranko Require Import TerminalDogma.premises 
                          TerminalDogma.Extensionality.

From Ranko Require Export NaiveSet.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



(** seteq_killer

    关于集合证明技术的tactic，我有了一个天大的发现！

    It will try to solve equality propositions on sets.
    (within intuitionism)
    (This could even be a COMPLETE tactic.)

    This is meant to be a 'safe' tactic. That is, it will not turn a provable
    goal into an unprovable one.
*)

(** expand all definitions *)
Ltac set_simpl := 
    (    rewrite /subset
        || rewrite /supset
        || rewrite /union
        || rewrite /itsct
        || rewrite /big_union 
        || rewrite /big_itsct
        || rewrite /UmapLR
        || rewrite /mapL
        || rewrite /mapR); simpl.

(** break the premise into small pieces and move up *)
Ltac set_move_up :=
    multimatch goal with
    | |- (_ ∈ _) -> _ => move => []
    | |- (_ = _) -> _ => let H := fresh "Heq" in move => H; rewrite H
    | |- forall i, _ => intros ?
    end.

(** try to solve the goal 
    It will not turn a provable goal into an unprovable one. *)
Ltac set_move_down :=
    multimatch goal with
    | H : _ ∈ ?A |- _ ∈ ?A => 
        apply H; by repeat (set_simpl || set_move_up || set_move_down)
    | |- ?A = ?B => apply Logic.eq_refl
    
    | |- exists i, _ => eexists
    (** possible goal from big_itsct *)
    | H : forall a, _ -> ?x ∈ _ |- ?x ∈ _ => apply H
    | |- _ ∈ _ => simpl
    end.

Ltac set_step := (set_simpl || set_move_up || set_move_down).

Ltac set_killer :=
    search_framework set_step.

Ltac seteq_killer := 
    apply seteqP; intros ?; split;
    search_framework set_step.