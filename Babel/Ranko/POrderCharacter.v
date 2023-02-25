(** POrderCharacter.v : the tactics about partial orders *)

From Babel Require Import TerminalDogma 
                          ExtraDogma.Extensionality.

From Babel.Ranko Require Import CentralCharacter 
                                LogicCharacter
                                SetCharacter.

From Babel Require Import POrder.

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
Ltac porder_basic_step_PRE
        top_step
        split_mode
        general_apply_depth
        eexists_mode
        :=
    match goal with
    | _ => progress porder_basic_simpl_branch
    | _ => progress porder_basic_move_up_branch

    (** reflexivity *)
    | |- ?a ⊑ ?a => apply poset_refl
    end.

Ltac porder_basic_step_POST
        top_step
        split_mode
        general_apply_depth
        eexists_mode
        :=
    match goal with
    | H : forall a, _ -> ?b ⊑ _ |- ?b ⊑ _ => 
        eapply H; by repeat top_step split_mode general_apply_depth eexists_mode
    | H : forall a, _ -> _ ⊑ ?c |- _ ⊑ ?c => 
        eapply H; by repeat top_step split_mode general_apply_depth eexists_mode

    (** anti-symmetry *)
    | T : poset |- @eq ?T _ _ => apply poset_antisym
    end.


Ltac porder_basic_step
        top_step
        split_mode
        general_apply_depth
        eexists_mode
        :=
    porder_basic_step_PRE top_step split_mode general_apply_depth eexists_mode
    || set_step top_step split_mode general_apply_depth eexists_mode
    || porder_basic_step_POST top_step split_mode general_apply_depth eexists_mode.


(*####################################################################*)
(** partial order structure level, including CPO, Lattice, CLattice *)

(** We don't plan to destruct order structures. *)
Ltac porder_simpl_branch := 
    (    rewrite /CPO.join_op
        || rewrite /CLattice.join_op
        || rewrite /CLattice.meet_op
        || rewrite /MonotonicFun.mixin_of
        || rewrite /MonotonicFun.class_of
        || rewrite /ContinuousFun.mixin_of
        ) => //=.

Ltac porder_move_up_branch := 
    match goal with

    | _ => idtac

    end.


Ltac porder_step_PRE
        top_step
        split_mode
        general_apply_depth
        eexists_mode
        :=
    match goal with
    | _ => progress porder_simpl_branch
    | _ => progress porder_move_up_branch

    | C : cpo |- @Poset.op (CPO.sort ?C) _ _ _ => 
        apply (CPO.join_prop (CPO.class C));
        by repeat top_step split_mode general_apply_depth eexists_mode

    | L : clattice |- @Poset.op (CLattice.sort ?L) _ _ _ =>
        apply (CLattice.join_prop (CLattice.class L));
        by repeat top_step split_mode general_apply_depth eexists_mode

    | _ => porder_basic_step_PRE top_step split_mode general_apply_depth eexists_mode
    end.

Ltac porder_step_POST
        top_step
        split_mode
        general_apply_depth
        eexists_mode
        :=
    match goal with
    | _ => porder_basic_step_POST top_step split_mode general_apply_depth eexists_mode
    | _ => rewrite monotonicfun_eqP
    end.


Ltac porder_step
        top_step
        split_mode
        general_apply_depth
        eexists_mode
        :=
    porder_step_PRE top_step split_mode general_apply_depth eexists_mode
    || set_step top_step split_mode general_apply_depth eexists_mode
    || porder_step_POST top_step split_mode general_apply_depth eexists_mode.

Ltac porder_step_sealed 
        split_mode 
        general_apply_depth
        eexists_mode
        :=
    idtac; let rec top_step := porder_step_sealed in
        porder_step top_step split_mode general_apply_depth eexists_mode.

Ltac porder_level := 
    repeat porder_step_sealed integer:(0) 100 integer:(0).