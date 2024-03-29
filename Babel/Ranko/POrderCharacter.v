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
        || rewrite /ord_op

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
    (** See #38 *)
    | |- ?a ⊑ ?a => reflexivity
    | |- Poset.op _ ?a ?a => reflexivity
    
    end.

Ltac porder_basic_step_POST
        top_step
        split_mode
        general_apply_depth
        eexists_mode
        :=
    match goal with

    | H : forall a, _ -> @Poset.op _ _ ?b _ |- @Poset.op _ _ ?b _ => 
        eapply H; by repeat top_step split_mode general_apply_depth eexists_mode
    | H : forall a, _ -> @Poset.op _ _ _ ?c |- @Poset.op _ _ _ ?c => 
        eapply H; by repeat top_step split_mode general_apply_depth eexists_mode

    (** anti-symmetry *)
    | _ => apply poset_antisym
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

    | |- @Poset.op (CPO.sort ?C) _ _ _ => 
        apply (CPO.join_prop (CPO.class C));
        by repeat top_step split_mode general_apply_depth eexists_mode

    | |- @Poset.op (CLattice.sort ?L) _ _ _ =>
        apply (CLattice.join_prop (CLattice.class L));
        by repeat top_step split_mode general_apply_depth eexists_mode

    | _ =>
        apply CLattice.join_prop;
        by repeat top_step split_mode general_apply_depth eexists_mode

    end.

Ltac porder_step_POST
        top_step
        split_mode
        general_apply_depth
        eexists_mode
        :=
    match goal with
    | _ => rewrite monotonicfun_eqP
    end.


Ltac porder_step
        top_step
        split_mode
        general_apply_depth
        eexists_mode
        :=
    porder_step_PRE top_step split_mode general_apply_depth eexists_mode
    || porder_basic_step top_step split_mode general_apply_depth eexists_mode
    || porder_step_POST top_step split_mode general_apply_depth eexists_mode.

Ltac porder_step_sealed 
        split_mode 
        general_apply_depth
        eexists_mode
        :=
    idtac; let rec top_step := porder_step_sealed in
        porder_step top_step split_mode general_apply_depth eexists_mode.

Ltac porder_level := 
    repeat porder_step_sealed LAZY 100 LAZY.
