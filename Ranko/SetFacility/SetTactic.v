(** SetTactic.v : the tactics about sets *)

From Ranko Require Import TerminalDogma.premises 
                          TerminalDogma.Extensionality.

From Ranko Require Export NaiveSet.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



(** set_killer

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

Ltac set_move_up := 
    multimatch goal with

    (** break NemSet structure *)
    | A : 𝒫( _ )₊ |- _ => 
        let H := fresh "Hnem" in 
            destruct A as [? H]=> //=;
            rewrite /NemSet.class_of /NemSet.mixin_of nonemptyP in H

    | H : _ <> ∅ |- _ =>
        rewrite nonemptyP in H; generalize dependent H

    (** break the premise into small pieces and move up *)
    | |- _ => premise_break_step

    | |- (_ ∈ _) -> _ => move => []
    | |- (_ = _) -> _ => let H := fresh "Heq" in move => H; rewrite H
    | |- forall i, _ => intros ?
    end.


(** Note: [extra_step] is the tactic to do high-level reasonings before fall to
    This low level reasoning. *)
Ltac set_step 
        extra_step      (* [ltac] the step tactic of higher level *)
        complete_split  (* [integer] controls the behaviour of split branch
                                integer:(0) : not complete, but much quicker
                                other value: complete, but may be slower*)
        := 

    multimatch goal with
    (** do the extra step first *)
    | _ => extra_step

    | _ => repeat set_simpl
    (** break the premise into small pieces and move up *)
    | _ => set_move_up

    (*##################################################*)
    (** try to solve the goal *)
    | H : ?x ∈ _ |- ?x ∈ _ =>
        apply H; 
        by search_framework ltac:(set_step extra_step complete_split) complete_split

    | H : _ ∈ ?A |- _ ∈ ?A => 
        apply H; 
        by search_framework ltac:(set_step extra_step complete_split) complete_split

    | |- ?A = ?B => 
        apply Logic.eq_refl

    | |- ~ (@eq 𝒫(_) _ _) => rewrite setneqP

    (** possible goal from big_itsct *)
    | H : forall a, _ -> ?x ∈ _ |- ?x ∈ _ => 
        eapply H; by search_framework ltac:(set_step extra_step complete_split) complete_split

    (** try to utilize [forall] premises 
        Note that this method is not complete, because we cannot control which
        term to use for instantiating [forall] *)
    | H : forall a : ?A, _, Hterm : ?A |- _ => 
        move: (H Hterm); clear H; 
        by search_framework ltac:(set_step extra_step complete_split) complete_split

    | |- _ ∈ _ => simpl

    end

    (** if the goal is a set equality that must be taken apart, just do it *)
    || (rewrite seteqP; intros ?; split).


Ltac set_killer_with complete_split :=
    search_framework ltac:(set_step idtac complete_split) complete_split.

Ltac set_killer := set_killer_with integer:(0).

Ltac set_killer_full := set_killer_with integer:(2).

