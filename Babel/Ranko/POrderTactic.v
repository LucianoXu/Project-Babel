(** POrderTactic.v : the tactics about partial orders *)

From Babel Require Import TerminalDogma.premises 
                          TerminalDogma.Extensionality.

From Babel.Ranko Require Import CentralTactic 
                                LogicTactic
                                SetTactic.

From Babel Require Export POrder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** expand all definitions *)
Ltac porder_simpl_branch := 
    (    rewrite /upper_bound
        || rewrite /lower_bound
        || rewrite /ub
        || rewrite /lb
        || rewrite /largest
        || rewrite /least
        || rewrite /supremum
        || rewrite /infimum
        ) => //=.

Ltac porder_move_up_branch := 
    match goal with

    | _ => idtac

    end.

(** TODO #22 

    Another problem: searching about infimum and supremum can be very slow.
*)
Ltac POrder_step
        top_step
        split_mode
        :=
    match goal with
    | _ => progress porder_simpl_branch
    | _ => progress porder_move_up_branch
    | _ => set_step top_step split_mode

    (** possible goal from big_itsct *)
    | H : forall a, _ -> ?b ⊑ _ |- ?b ⊑ _ => 
        eapply H; by repeat top_step
    | H : forall a, _ -> _ ⊑ ?c |- _ ⊑ ?c => 
        eapply H; by repeat top_step

    | T : poset |- @eq ?T _ _ => apply poset_antisym
    end.

Ltac POrder_step_sealed split_mode :=
    idtac; let rec top_step := POrder_step_sealed split_mode in
        POrder_step top_step split_mode.

Ltac POrder_level := 
    all_move_down;
    repeat POrder_step_sealed integer:(0).
