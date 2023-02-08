(** SetTactic.v : the tactics about sets *)

From Ranko Require Import TerminalDogma.premises 
                          TerminalDogma.Extensionality.

From Ranko Require Export NaiveSet.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



(** set_killer

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


Ltac set_step := 
    set_simpl || 

    multimatch goal with
    
    (** break the premise into small pieces and move up *)
    | |- _ => premise_break_step
    | |- (_ ∈ _) -> _ => move => []
    | |- (_ = _) -> _ => let H := fresh "Heq" in move => H; rewrite H
    | |- forall i, _ => intros ?


    (** try to solve the goal *)
    | H : _ ∈ ?A |- _ ∈ ?A => 
        apply H; by search_framework set_step
    | |- ?A = ?B => apply Logic.eq_refl

    | |- exists i, _ => eexists
    (** possible goal from big_itsct *)
    | H : forall a, _ -> ?x ∈ _ |- ?x ∈ _ => eapply H

    (** try to utilize [forall] premises 
        Note that this method is not complete, because we cannot control which
        term to use for instantiating [forall] *)
    | H : forall a : ?A, _, Hterm : ?A |- _ => 
        move: (H Hterm); clear H; by search_framework set_step

    | |- _ ∈ _ => simpl
    
    end

    (** if the goal is a set equality that must be taken apart, just do it *)
    || (apply seteqP; intros ?; split).


Ltac set_killer :=
    search_framework set_step.