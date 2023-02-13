(** POrderCharacter.v : the tactics about partial orders *)

From Babel Require Import TerminalDogma.premises 
                          TerminalDogma.Extensionality.

From Babel.Ranko Require Import CentralCharacter 
                                LogicCharacter
                                SetCharacter.

From Babel Require Export POrder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** expand all definitions *)
Ltac porder_basic_simpl_branch := 
    (    rewrite /upper_bound
        || rewrite /lower_bound
        || rewrite /ub
        || rewrite /lb
        || rewrite /largest
        || rewrite /least
        || rewrite /supremum
        || rewrite /infimum
        ) => //=.

Ltac porder_basic_move_up_branch := 
    match goal with

    | _ => idtac

    end.

(** TODO #22 

    Another problem: searching about infimum and supremum can be very slow.
*)
Ltac porder_basic_step
        top_step
        split_mode
        :=
    match goal with
    | _ => progress porder_basic_simpl_branch
    | _ => progress porder_basic_move_up_branch
    | _ => set_step top_step split_mode

    | H : forall a, _ -> ?b ⊑ _ |- ?b ⊑ _ => 
        eapply H; by repeat top_step
    | H : forall a, _ -> _ ⊑ ?c |- _ ⊑ ?c => 
        eapply H; by repeat top_step

    | T : poset |- @eq ?T _ _ => apply poset_antisym
    end.


(*####################################################################*)
(** partial order structure level, including CPO, Lattice, CLattice *)

(** We don't plan to destruct order structures. *)
Ltac porder_simpl_branch := 
    (    rewrite /CPO.join_op
        || rewrite /MonotonicFun.mixin_of
        || rewrite /ContinuousFun.mixin_of
        ) => //=.

Ltac porder_move_up_branch := 
    match goal with

    | _ => idtac

    end.


Ltac porder_step
        top_step
        split_mode
        :=
    match goal with
    | _ => progress porder_simpl_branch
    | _ => progress porder_move_up_branch

    | C : cpo |- Poset.op (@CPO.base _ (CPO.class ?C)) _ _ => 
        apply (CPO.join_prop (CPO.class C));
        by repeat top_step

    | _ => porder_basic_step top_step split_mode

    end.

Ltac porder_step_sealed split_mode :=
    idtac; let rec top_step := porder_step_sealed split_mode in
        porder_step top_step split_mode.

Ltac porder_level := 
    all_move_down;
    repeat porder_step_sealed integer:(0).
