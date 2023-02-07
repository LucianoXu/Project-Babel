(** SetTactic.v : the tactics about sets *)

From Ranko Require Import TerminalDogma.premises 
                          TerminalDogma.Extensionality
                          .

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

Ltac set_simpl :=
    repeat (
            rewrite /union
            || rewrite /itsct
            || rewrite /big_union 
            || rewrite /big_itsct
            || rewrite /UmapLR
            || rewrite /mapL
            || rewrite /mapR);
    simpl.

Ltac set_move_up :=
    repeat multimatch goal with
    (** discard absurd cases first *)
    | |- False -> _ => move => []

    (** possible premises from union 
        such premises means multiple trying is need for solving the goal.
    *)
    | |- (_ \/ _) -> _ => move => [|]

    | |- (exists i, _) -> _ => move => []
    | |- (_ /\ _) -> _ => move => []
    | |- (_ = _) -> _ => move ->
    | |- (_ ∈ _) -> _ => move => []
    (*
    | |- (_ ∈ { _ , _ | _}) -> _ => move => []
    | |- (_ ∈ { _ | _}) -> _ => move => []
    *)
    | |- forall i, _ => let x := fresh "H" in move => x
    end.

Ltac set_move_down :=
    repeat multimatch goal with
    | H : _ ∈ ?A |- _ ∈ ?A => apply H
    | |- ?A = ?B => apply Logic.eq_refl
    
    | |- exists i, _ => eexists
    | |- (_ /\ _) => split
    (** possible goal from intersection
        It choices are made, then it must succeed in its path. *)
    | |- (?A \/ ?B) => (left; by set_move_down) || (right; by set_move_down)
    (** possible goal from big_itsct *)
    | H : forall a, _ -> ?x ∈ _ |- ?x ∈ _ => apply H
    | |- True => by []
    | |- _ ∈ _ => simpl
    end.

Ltac set_belonging_killer :=
    repeat (set_move_up || set_move_down).

Ltac seteq_killer := 
    let x := fresh "x" in apply seteqP => x; split;
    set_simpl; set_belonging_killer.