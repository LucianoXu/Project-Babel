(** * Imp: Simple Imperative Programs 
    From software foundation.

    Contents includes:
    Aexp
        - Aexp eval
    Bexp
        - Bexp eval
    cmd
        - operational semantics

*)


(** In this chapter, we take a more serious look at how to use Coq as
    a tool to study other things.  Our case study is a _simple
    imperative programming language_ called Imp, embodying a tiny core
    fragment of conventional mainstream languages such as C and Java.

    Here is a familiar mathematical function written in Imp.

       Z := X;
       Y := 1;
       while Z <> 0 do
         Y := Y * Z;
         Z := Z - 1
       end
*)

From Babel Require Import TerminalDogma.

From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From Babel Require Import Maps.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ################################################################# *)
(** * Expressions With Variables *)

(** Let's return to defining Imp, where the next thing we need to do
    is to enrich our arithmetic and boolean expressions with
    variables. To keep things simple, we'll assume that all variables
    are global and that they only hold numbers. *)

(* ================================================================= *)
(** ** States *)

(** Since we'll want to look variables up to find out their current
    values, we'll use total maps from the [Maps] chapter.

    A _machine state_ (or just _state_) represents the current values
    of all variables at some point in the execution of a program. *)

(** For simplicity, we assume that the state is defined for
    _all_ variables, even though any given program is only able to
    mention a finite number of them.  Because each variable stores a
    natural number, we can represent the state as a total map from
    strings (variable names) to [nat], and will use [0] as default
    value in the store. *)

Definition state := total_map nat.

(* ================================================================= *)
(** ** Syntax  *)

(** We can add variables to the arithmetic expressions we had before
    simply by including one more constructor: *)

Inductive aexp : Type :=
    | ANum (n : nat)
    | AId (x : string)
    | APlus (a1 a2 : aexp)
    | AMinus (a1 a2 : aexp)
    | AMult (a1 a2 : aexp).

(** Defining a few variable names as notational shorthands will make
    examples easier to read: *)
(*
Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".
*)

(** The definition of [bexp]s is unchanged (except that it now refers
    to the new [aexp]s): *)

Inductive bexp : Type :=
    | BTrue
    | BFalse
    | BEq (a1 a2 : aexp)
    | BNeq (a1 a2 : aexp)
    | BLe (a1 a2 : aexp)
    | BGt (a1 a2 : aexp)
    | BNot (b : bexp)
    | BAnd (b1 b2 : bexp).

(* ================================================================= *)
(** ** Notations *)

(** To make Imp programs easier to read and write, we introduce some
    notations and implicit coercions.  You do not need to understand
    exactly what these declarations do.  Briefly, though:
        - The [Coercion] declaration stipulates that a function (or
            constructor) can be implicitly used by the type system to
            coerce a value of the input type to a value of the output
            type.  For instance, the coercion declaration for [AId]
            allows us to use plain strings when an [aexp] is expected;
            the string will implicitly be wrapped with [AId].
        - [Declare Custom Entry com] tells Coq to create a new
            "custom grammar" for parsing Imp expressions and
            programs. The first notation declaration after this tells Coq
            that anything between [<{] and [}>] should be parsed using
            the Imp grammar. Again, it is not necessary to understand the
            details, but it is important to recognize that we are
            defining _new_ interpretations for some familiar operators
            like [+], [-], [*], [=], [<=], etc., when they occur between
            [<{] and [}>]. *)

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.

Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                    (in custom com at level 0, only parsing,
                    f constr at level 0, x constr at level 9,
                    y constr at level 9) : com_scope.
Notation "x + y"   := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y"   := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y"   := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y"  := (BLe x y) (in custom com at level 70, no associativity).
Notation "x > y"   := (BGt x y) (in custom com at level 70, no associativity).
Notation "x = y"   := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y"  := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).

Open Scope com_scope.

(** We can now write [3 + (X * 2)] instead  of [APlus 3 (AMult X 2)],
    and [true && ~(X <= 4)] instead of [BAnd true (BNot (BLe X 4))]. *)

(* 
Definition example_aexp : aexp := <{ 3 + (X * 2) }>.
Definition example_bexp : bexp := <{ true && ~(X <= 4) }>.
*)

(* ================================================================= *)
(** ** Evaluation *)

Fixpoint aeval (st : state) (a : aexp) : nat :=
    match a with
    | ANum n => n
    | AId x => st x
    | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
    | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
    | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
    end.

Fixpoint beval (st : state) (b : bexp) : bool :=
    match b with
    | <{true}>      => true
    | <{false}>     => false
    | <{a1 = a2}>   => (aeval st a1) =? (aeval st a2)
    | <{a1 <> a2}>  => negb ((aeval st a1) =? (aeval st a2))
    | <{a1 <= a2}>  => (aeval st a1) <=? (aeval st a2)
    | <{a1 > a2}>   => negb ((aeval st a1) <=? (aeval st a2))
    | <{~ b1}>      => negb (beval st b1)
    | <{b1 && b2}>  => andb (beval st b1) (beval st b2)
    end.

(** We can use our notation for total maps in the specific case of
    states -- i.e., we write the empty state as [(_ !-> 0)]. *)

Definition empty_st := (_ !-> 0).

(** Also, we can add a notation for a "singleton state" with just one
    variable bound to a value. *)
Notation "x '!->' v" := (x !-> v ; empty_st) (at level 100).

(* ################################################################# *)
(** * Commands *)

(** Now we are ready define the syntax and behavior of Imp
    _commands_ (or _statements_). *)

(* ================================================================= *)
(** ** Syntax *)

(** Informally, commands [c] are described by the following BNF
    grammar.

        c := skip | x := a | c ; c | if b then c else c end
            | while b do c end
*)

(** Here is the formal definition of the abstract syntax of
    commands: *)

Inductive com : Type :=
    | CSkip
    | CAsgn (x : string) (a : aexp)
    | CSeq (c1 c2 : com)
    | CIf (b : bexp) (c1 c2 : com)
    | CWhile (b : bexp) (c : com).

(** As we did for expressions, we can use a few [Notation]
    declarations to make reading and writing Imp programs more
    convenient. *)

Notation "'skip'"  :=
            CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
            (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
                y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
            (CSeq x y)
            (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
            (CIf x y z)
            (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
            (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.

(** For example, here is the factorial function again, written as a
    formal Coq definition.  When this command terminates, the variable
    [Y] will contain the factorial of the initial value of [X]. *)
(*
Definition fact_in_coq : com :=
    <{ Z := X;
        Y := 1;
        while Z <> 0 do
        Y := Y * Z;
        Z := Z - 1
        end }>.
*)

(* ################################################################# *)
(** * Evaluating Commands *)

(** Next we need to define what it means to evaluate an Imp command.
    The fact that [while] loops don't necessarily terminate makes
    defining an evaluation function tricky... *)

(* ================================================================= *)
(** ** Evaluation as a Relation *)

(** Here's a better way: define [ceval] as a _relation_ rather than a
    _function_ -- i.e., make its result a [Prop] rather than a
    [state], similar to what we did for [aevalR] above. *)

(** This is an important change.  Besides freeing us from awkward
    workarounds, it gives us a ton more flexibility in the definition.
    For example, if we add nondeterministic features like [any] to the
    language, we want the definition of evaluation to be
    nondeterministic -- i.e., not only will it not be total, it will
    not even be a function! *)

(** We'll use the notation [st =[ c ]=> st'] for the [ceval] relation:
    [st =[ c ]=> st'] means that executing program [c] in a starting
    state [st] results in an ending state [st'].  This can be
    pronounced "[c] takes state [st] to [st']". *)

(* ----------------------------------------------------------------- *)
(** *** Operational Semantics *)

(** Here is an informal definition of evaluation, presented as inference
    rules for readability:

                            -----------------                            (E_Skip)
                            st =[ skip ]=> st

                            aeval st a = n
                    -------------------------------                      (E_Asgn)
                    st =[ x := a ]=> (x !-> n ; st)

                            st  =[ c1 ]=> st'
                            st' =[ c2 ]=> st''
                            ---------------------                           (E_Seq)
                            st =[ c1;c2 ]=> st''

                            beval st b = true
                            st =[ c1 ]=> st'
                --------------------------------------               (E_IfTrue)
                st =[ if b then c1 else c2 end ]=> st'

                            beval st b = false
                            st =[ c2 ]=> st'
                --------------------------------------              (E_IfFalse)
                st =[ if b then c1 else c2 end ]=> st'

                            beval st b = false
                    -----------------------------                 (E_WhileFalse)
                    st =[ while b do c end ]=> st

                            beval st b = true
                            st =[ c ]=> st'
                    st' =[ while b do c end ]=> st''
                    --------------------------------                 (E_WhileTrue)
                    st  =[ while b do c end ]=> st''
*)

(** Here is the formal definition.  Make sure you understand
    how it corresponds to the inference rules. *)

Reserved Notation
            "st '=[' c ']=>' st'"
            (at level 40, c custom com at level 99,
            st constr, st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
    | E_Skip : forall st,
        st =[ skip ]=> st
    | E_Asgn  : forall st a n x,
        aeval st a = n ->
        st =[ x := a ]=> (x !-> n ; st)
    | E_Seq : forall c1 c2 st st' st'',
        st  =[ c1 ]=> st'  ->
        st' =[ c2 ]=> st'' ->
        st  =[ c1 ; c2 ]=> st''
    | E_IfTrue : forall st st' b c1 c2,
        beval st b = true ->
        st =[ c1 ]=> st' ->
        st =[ if b then c1 else c2 end]=> st'
    | E_IfFalse : forall st st' b c1 c2,
        beval st b = false ->
        st =[ c2 ]=> st' ->
        st =[ if b then c1 else c2 end]=> st'
    | E_WhileFalse : forall b st c,
        beval st b = false ->
        st =[ while b do c end ]=> st
    | E_WhileTrue : forall st st' st'' b c,
        beval st b = true ->
        st  =[ c ]=> st' ->
        st' =[ while b do c end ]=> st'' ->
        st  =[ while b do c end ]=> st''

    where "st =[ c ]=> st'" := (ceval c st st').

(** The cost of defining evaluation as a relation instead of a
    function is that we now need to construct _proofs_ that some
    program evaluates to some result state, rather than just letting
    Coq's computation mechanism do it for us. *)

(* ================================================================= *)
(** ** Determinism of Evaluation *)

(** Changing from a computational to a relational definition of
    evaluation is a good move because it frees us from the artificial
    requirement that evaluation should be a total function.  But it
    also raises a question: Is the second definition of evaluation
    really a partial _function_?  Or is it possible that, beginning from
    the same state [st], we could evaluate some command [c] in
    different ways to reach two different output states [st'] and
    [st'']?

    In fact, this cannot happen: [ceval] _is_ a partial function: *)

Theorem ceval_deterministic: forall c st st1 st2,
        st =[ c ]=> st1  ->
        st =[ c ]=> st2 ->
        st1 = st2.
Proof.
    intros c st st1 st2 E1 E2.
    generalize dependent st2.
    induction E1; intros st2 E2; inversion E2; subst.
    - (* E_Skip *) reflexivity.
    - (* E_Asgn *) reflexivity.
    - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in E1_1, IHE1_2.
    apply IHE1_2. assumption.
    - (* E_IfTrue, b evaluates to true *)
        apply IHE1. assumption.
    - (* E_IfTrue,  b evaluates to false (contradiction) *)
        rewrite H in H5. discriminate.
    - (* E_IfFalse, b evaluates to true (contradiction) *)
        rewrite H in H5. discriminate.
    - (* E_IfFalse, b evaluates to false *)
        apply IHE1. assumption.
    - (* E_WhileFalse, b evaluates to false *)
    reflexivity.
    - (* E_WhileFalse, b evaluates to true (contradiction) *)
    rewrite H in H2. discriminate.
    - (* E_WhileTrue, b evaluates to false (contradiction) *)
    rewrite H in H4. discriminate.
    - (* E_WhileTrue, b evaluates to true *)
    rewrite (IHE1_1 st'0 H3) in E1_1, IHE1_2.
    apply IHE1_2. assumption.  Qed.