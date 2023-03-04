(** SetCharacter.v : the tactics about sets *)

From Babel Require Import TerminalDogma 
                          ExtraDogma.Extensionality.

From Babel.Ranko Require Import CentralCharacter LogicCharacter.

From Babel Require Import NaiveSet.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



(** set_level

    It will try to solve equality propositions on sets.
    (within intuitionism)
    (This could even be a COMPLETE tactic.)

    This is meant to be a 'safe' tactic. That is, it will not turn a provable
    goal into an unprovable one.
*)

(** expand all definitions *)
Ltac set_simpl_branch := 
    (    rewrite /subset
        || rewrite /supset
        || rewrite /singleton
        || rewrite /union
        || rewrite /itsct
        || rewrite /big_union 
        || rewrite /big_itsct
        || rewrite /UmapR
        || rewrite /UmapLR
        || rewrite /mapL
        || rewrite /mapR) => //=.

Ltac set_move_up_branch := 
    match goal with

    | |- _ <> ∅ -> _ =>
        rewrite nonemptyP
    
    (** break NemSet structure *)
    | |- 𝒫( _ )₊ -> _ => 
    let H := fresh "Hnem" in 
        intros [? H] => //=;
        rewrite /NemSet.class_of /NemSet.mixin_of nonemptyP in H; destruct H

    | |- (_ ∈ _) -> _ => move => []

    end.


(** Note: [top_step] is the tactic to do high-level reasonings before fall to
    This low level reasoning. *)
Ltac set_step_PRE
        top_step
        split_mode
        general_apply_depth
        eexists_mode
        := 

    match goal with

    (** [or] goal, complete branch *)
    | |- (_ \/ _) =>
        (left; by repeat top_step split_mode general_apply_depth eexists_mode) 
        || (right; by repeat top_step split_mode general_apply_depth eexists_mode)


    | _ => progress repeat set_simpl_branch
    (** break the premise into small pieces and move up *)
    | _ => progress set_move_up_branch

    (*##################################################*)
    (** try to solve the goal *)

    | H : ?x ∈ _ |- ?x ∈ _ =>
        apply H; 
        by repeat top_step split_mode general_apply_depth eexists_mode

    | H : _ ∈ ?A |- _ ∈ ?A => 
        apply H; 
        by repeat top_step split_mode general_apply_depth eexists_mode

    (** this branch is not safe when the goal is something like
            [?f x = y] *)
    | |- ?A = ?B => 
        is_var A; is_var B;
        apply Logic.eq_refl

    | |- ~ (@eq 𝒫(_) _ _) => rewrite setneqP

    (** possible goal from big_itsct *)
    | H : forall a, _ -> ?x ∈ _ |- ?x ∈ _ => 
        eapply H; by repeat top_step split_mode general_apply_depth eexists_mode
    end.

Ltac set_step_POST
        top_step
        split_mode
        general_apply_depth
        eexists_mode
        := 
    match goal with
    (** if the goal is a set equality that must be taken apart, just do it *)
    | _ => rewrite seteqP; intros ?; split
    end.

Ltac set_step 
        top_step
        split_mode
        general_apply_depth
        eexists_mode
        := 
    set_step_PRE top_step split_mode general_apply_depth eexists_mode 
    || central_step top_step split_mode general_apply_depth eexists_mode
    || set_step_POST top_step split_mode general_apply_depth eexists_mode.


Ltac set_step_sealed 
        split_mode 
        general_apply_depth 
        eexists_mode
        := 
    idtac; let rec top := set_step_sealed in 
        set_step top split_mode general_apply_depth eexists_mode.

Ltac set_level := 
    repeat (set_step_sealed LAZY 100 LAZY).

Ltac set_level_full := 
    repeat (set_step_sealed AGGRESSIVE 100 LAZY).

