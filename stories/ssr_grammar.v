From mathcomp Require Import all_ssreflect all_algebra.

(* Local Open Scope nat_scope. *)
(* Local Open Scope bool_scope. *)

Section sec1.

(* let x := B in x + x + x *)
Compute 
    let n := 33 : nat in 
    let e := n + n + n in 
        e + e + e.

(* about nat *)
Print predn.
Print addn.
Print subn.
Print eqn.
Locate ".+1". (* .+2 .+3 .+4 *)
Compute 2.+1.
Locate "==".
Check 1 == S 0.
Print leq.
Check 1 <= 2.

(* about seq := list *)
Check [::]. (* nil; empty seq *)
Check [:: 1]. (* seq nat *)
Check [:: true; false]. (* seq bool *)
Check [:: 1, 2 & [:: 3; 4; 5]].
Check [:: 1] ++ [::].
Check map.
Locate "seq".
Compute [seq i.+1 | i <- [:: 2; 3]].

(* pair *)
Print pair.
Check (3, false).
Locate ".1".
Locate ".2".
Compute (true, false).1.

(* difference between Record and Inductive *) 
(* Canonical structure *)
Record point_r : Type := Point_r {xr : nat; yr : nat; zr : nat}.
Inductive point_i : Type := Point_i (xi : nat) (yi : nat) (zi : nat).
Check xr.
Fail Check xi.
Compute xr (Point_r 3 0 2).
Compute yr (Point_r 3 0 2).

Definition xi (p : point_i) := match p with Point_i a _ _ => a end.
Compute xi (Point_i 3 0 2).
(* only one constructor; syntactic sugar: let: *)
Definition xi' (p : point_i) := let: Point_i a _ _ := p in a.

(* Section, Variable, Context *)
Section iterators.
Variable (T : Type) (A : Type).
Variables (f : T -> A -> A).

Implicit Type x : T.

Fixpoint iter1 n op x :=
if n is p.+1 then op (iter1 p op x) else x.

Fixpoint foldr1 a s :=
if s is y :: ys then f y (foldr1 a ys) else a.

Check iter1.
End iterators.
Check iter1.

Compute iter1 _ 3 predn 5.
Compute foldr1 _ _ addn 0 [:: 1; 2].

Section iterators.
(* context can be implicit *)
Context {T : Type} {A : Type}.
Variables (f : T -> A -> A).

Implicit Type x : T.

Fixpoint iter2 n op x :=
if n is p.+1 then op (iter2 p op x) else x.

Fixpoint foldr2 a s :=
if s is y :: ys then f y (foldr2 a ys) else a.

Variable (init : A) (x1 x2 : T).

Compute foldr2 init [:: x1; x2].

End iterators.

About iter2.
Compute iter2 3 predn 5.
Compute foldr2 addn 0 [:: 1; 2].

Section simpl_control.

Fixpoint addn' n m := if n is p.+1 then (addn' p m).+1 else m.
Fixpoint add' n m := if n is p.+1 then add' p m.+1 else m.

Variable n : nat.
Eval simpl in predn (add' n.+1 7).
Eval simpl in predn (addn' n.+1 7).
Compute predn (add' n.+1 7).
Compute predn (addn' n.+1 7).

End simpl_control.

Section iterators_notations.

Fixpoint iota' m n := if n is u.+1 then m :: iota' m.+1 u else [::].
Compute iota' 3 5.
Compute map (fun i => i + 2) (iota' 3 5).
Notation "\sum_ ( m <= i < n ) F" :=
    (foldr (fun i a => F + a) 0 (iota' m (n-m))).

Compute \sum_(1 <= j < 5) (j * 2 - 1).
Compute \sum_(1 <= i < 5) i.
(* note that i , j are binder names and they are same in Coq *)

Definition leq' := leq. 
Notation "m '<?' n" := (leq' m.+1 n) (at level 70, no associativity).
Notation "n '>?' m" := (leq' m.+1 n) (at level 70, no associativity, only parsing).
Check 2 <? 3.
Check 2 >? 3.

(* the early one the first *)
(* reserved notation : the order *)
Definition leq'' := leq.
Reserved Notation "m ?>? n" (at level 70, no associativity, only parsing).
Reserved Notation "m ?<? n" (at level 70, no associativity).
Notation "m ?<? n" := (leq'' m.+1 n).
Notation "m ?>? n" := (n ?<? m).
Check 2 ?<? 3.

(* conventions : page 39 *)
End iterators_notations.
End sec1.

Section sec2.

(* // ---- try auto : close trivial goals if possible *)
(* by tactic : close trivial goals after applying tactic *)
(* by [] ---- close trivial goals *)

Lemma example1 (n : nat) : n = n.
Proof. by []. Qed.

Lemma example2 (m n : nat) : m + n = n + m.
Proof.
by rewrite addnC.
Restart.
by rewrite addnC.
Qed.

(* basic tactics related to std lib *)
(* move=> x y ----- intros x y z *)
(* => : whenever => appears, change to the move=> mode *)
(*      that is, tactic => ...  === tactic; move=> ... *)
(*      this is backward *)

Lemma example3 : forall m n : nat, m + n = n + m.
Proof.
move=>m.
Restart.
move=>m n.
by rewrite addnC.
Qed.

Lemma example3' (m n p: nat) (H : m = n) : m = p -> m + p = n + n.
Proof.
rewrite H=>E.
Restart.
by rewrite H=>->.
Qed.

(* -> : after move=> mode, rewrite and clear the hypothesis *)
(* <- : after move=> mode, rewrite <- and clear the hypothesis *)

Lemma example4 : forall m n : nat, m = n -> m + n = m + m.
Proof.
move=>m n.
move=>H; rewrite H; clear H.
Restart.
move=>m n->.
Restart.
move=>m n <-.
Restart.
by move=>??->.
Qed.

(* move: x y ---- generalize dependent y; generalize dependent x *)
(* move: {+}H ---- duplicate H in hypothesis then generalize dependent H *)
(* move: xxx ---- xxx is a proved lemma/constant... *)

Lemma example5 (m n : nat) : m = n -> m + n = m + m.
Proof.
move: m. (* generalize dependent m *)
Restart.
move: n.
Restart.
move: m n. apply example4.
Restart.
move=>H.
move: H.
Restart.
move=>H.
move: {+}H.
Restart.
move: 1.
Undo.
move: addnC.
Undo.
move: (addnC m n).
Restart.
apply: example4.
Qed.

(* move/H=> xxx or move=>/H xxx ---- move=>xxx; apply H in xxx *)
(* move/H: xxx ---- apply H in xxx; move: xxx *)
(*     H can be A -> B or reflect A B *)
(*     /H : after move=> mode, apply H *)
(*     /(_ x ...) : instantiation the parameters *)

Lemma example6 (m n : nat) (H : m.+1 = n.+1 -> m = n) :
    m.+1 = n.+1 -> m + n = m + m.
Proof.
move=>E.
apply H in E.
Restart.
move=>/H E.
Restart.
move/H=>E.
Restart.
move=>E.
move/H: E.
Restart.
by move/H=>->.
Qed.

Print Bool.reflect.
Lemma example7 (m n : nat) (H : reflect (m = n) (m.+1 == n.+1)) :
    m.+1 == n.+1 -> m + n = m + m.
Proof.
move=>/H.
Restart.
by move=>/H->.
Qed.

Lemma example7' (H : forall m n, reflect (m = n) (m.+1 == n.+1)) (m n : nat) :
    m.+1 == n.+1 -> m + n = m + m.
Proof.
move=>/H.
Restart.
move=>/(H m n).
Restart.
move: H=>/(_ m n).
Undo.
by move=>/H->.
Qed.

Lemma example8 (m n : nat) (H : reflect (m.+1 = n.+1) (m == n)) :
    m.+1 = n.+1 -> m + n = m + m.
Proof.
move=>/H.
Check eqP.
move=>/eqP.
Restart.
by move=>/H/eqP->.
Qed.

(* rewrite H ---- rewrite -> H *)
(* rewrite -H ---- rewrite <- H *)
(* rewrite !H ---- rewrite !H : repeat the rewrite (at least one time) *)
(* rewrite ?H ---- rewrite ?H : repeat the rewrite (zero or more times) *)
(* rewrite n ?H / rewrite n !H ---- repear the rewrite for at most n times *)
(* rewrite H1 H2 ---- rewrite H1; H2 : sequentially rewrite the hyps *)
(* rewrite {}H --- rewrite H and clear H from hypothesis *)
(* pattern *)
(* rewrite [pattern]H : rewrite H in the subterm that matchs pattern *)
(* LHS : Left Hand Side   RHS : Right Hand Side *)
(* _ + _ , x * _ : pattern without meta-variable *)
(* X in X == _ : pattern match goals and return the first X as the subterm *)
(* in LHS , in RHS , in X in _ + X    :  rewrite in the subterm *)
(* rewrite [LHS]H ---- rewrite H for LHS, works when LHS matchs H *)
(* rewrite [RHS]H ---- rewrite H for RHS, works when RHS matchs H *)
(* rewrite [in LHS]H ---- rewrite H in LHS *)
(* rewrite [in RHS]H ---- rewrite H in RHS *)

Lemma example9 (m n p q : nat) (H : forall x y z, x + (y + z) = x + y + z) : 
    m + ((n + m) + (p + q)) = m + n + (m + p) + q.
Proof.
rewrite H.
Restart.
rewrite -H.
Restart.
rewrite !H.
Restart.
rewrite -!H.
Restart.
rewrite ?H.
Restart.
rewrite 2?H.
Restart.
rewrite 2!H.
Restart.
rewrite {}H.
Restart.
rewrite [LHS]H.
Restart.
rewrite [in RHS]H.
Restart.
rewrite [_ + (m + p)]H.
Restart.
rewrite [X in _ = X + q]H.
Restart.
rewrite [in X in X = _]H.
Restart.
by rewrite !H.
Qed.

(* /= ---- simpl *)
(* //= ---- // /= : auto simpl *)
(* rewrite /xxx ---- unfold xxx *)
(* rewrite -/xxx ---- fold xxx *)
(* rewrite {1 2}H ---- rewrite H for the 1 and 2 occurrences *)
(* rewrite -[x]/(y) ---- replace x with y where x = y is trivial *)
Lemma example15 : size [:: true] = 1.
Proof.
rewrite /=.
Restart.
move=>/=.
Restart.
rewrite //=.
Qed.

Lemma example16 m n1 n2 :
  (m * n1 <= m * n2) = (m == 0) || (n1 <= n2).
Proof.
rewrite [in LHS]/leq.
Undo.
rewrite /leq.
rewrite -/leq.
rewrite -/(leq _ _).
Undo.
rewrite -!/(leq _ _).
Restart.
rewrite {1}/leq.
Undo.
rewrite {1 2}/leq.
Undo.
rewrite -{1}[n1]/(0 + n1).
Restart.
by rewrite /leq -mulnBr muln_eq0.
Qed.

(* case: x ---- destruct x *)
(* case E: x ---- destruct x eqn: E *)
(* case: x / E ---- if E is a = x, then replace all x with a *)
(* case/spec : x ---- destruct x according to the specification spec *)

Lemma orbT' b : b || true = true.
Proof.
by case: b.
Restart.
case E: b.
Restart.
by case: b.
Qed.

Lemma orbA' b1 b2 b3 : b1 || (b2 || b3) = b1 || b2 || b3.
Proof. by case: b1; case: b2; case: b3. Qed.

Lemma implybE' a b : (a ==> b) = ~~ a || b.
Proof. by case: a; case: b. Qed.

Lemma negb_and' a b : ~~ (a && b) = ~~ a || ~~ b.
Proof. by case: a; case: b. Qed.

Lemma example10 (m n : nat) (H : m = n) : m + n = m + m.
Proof.
case: n / H.
by [].
Qed.

(* remark : case: n / H    sometimes is powerful than rewrite *)
Section castmx_test.

Variables (R : ringType) (m n : nat).
Implicit Type A : 'M[R]_(m, n).

Definition castmx' m' n' (eq_mn : (m = m') * (n = n')) A : 'M_(m', n') :=
  let: erefl in _ = m' := eq_mn.1 return 'M_(m', n') in
  let: erefl in _ = n' := eq_mn.2 return 'M_(m, n') in A.

Lemma example11 t (H : forall A B  : 'M[R]_(m+n), A = B) (E : m + n = t):
    forall (A : 'M[R]_(m+n)) (B : 'M[R]_t), B = castmx (E, E) A.
Proof.
case: t / E. by move=>??.
(* rewrite -E. *)
Qed.

End castmx_test.

Section case_nat.

Variant eqn0_xor_gt0 n : bool -> bool -> Set :=
  | Eq0NotPos of n = 0 : eqn0_xor_gt0 n true false
  | PosNotEq0 of n > 0 : eqn0_xor_gt0 n false true.

Lemma posnP n : eqn0_xor_gt0 n (n == 0) (0 < n).
Proof. by case: n; constructor. Qed.

Lemma example12 n (P : nat -> Prop) : P n.
Proof.
case: (posnP n).
Admitted.

End case_nat.

Section case_seq.

Variable (T : Type) (n : nat).

Variant seq_spec : seq T -> Type :=
    | SeqNil : seq_spec [::]
    | SeqRcons x t : seq_spec (rcons t x).

Lemma seqNP u : seq_spec u.
Proof.
elim: u=>[|x t [|t' a]].
constructor.
have <-: rcons [::] x = [:: x] by [].
constructor.
rewrite -rcons_cons.
constructor.
Qed.

Lemma example13 (u : seq T) (P : seq T -> Prop) : P u.
Proof.
case/seqNP: u.
Admitted.

End case_seq.

(* elim: x ---- induction x *)
(* elim: x y ... ---- move: y ..., induction x *)
(* elim: x => [...|...] ---- induction x as [...|...] *)
(* elim/ind: x ---- induction x using ind *)

Lemma example13' (m n k : nat) : m + (n + k) = m + n + k.
Proof.
move: n k. elim: m=>//.
Restart.
elim: m n k.
Restart.
elim: m n k=>[|m IH n k].
Restart.
by elim: m n k=>[//|m IH n k]; rewrite !addSn IH.
Qed.

(* rearrange the order of subgoals *)
(* first or last tactic : several goals, apply tactic to the first or last *)
(*     subgoal *)
(* last first. rearrange subgoals, last first *)
Lemma example14 (P Q R S: Prop) (H : P -> Q -> R -> S) : P -> Q -> R -> S.
move=>HP HQ HR.
apply: H; first apply HP.
Undo.
apply: H; last apply HR.
Undo.
apply: H; last first.
Undo.
apply: H; assumption.
Qed.

(* have : xxx ---- assert (xxx) *)
(* have E : xxx ---- assert (E : xxx) *)
(* have -> : xxx ---- assert xxx and then rewrite it in the goal *)
(* have one-line tactic : xxx ---- assert xxx and the move=>tactic on the goal *)
(*      note that, have tac ---- tac is in the move=> mode *)
(* have : xxx by tactic ---- solve xxx by the tactic *)
(* suff ... : xxx ---- have ... : xxx *)
(*     but defer the proof after the current goal *)
(* have := xxx ---- move: xxx *)
(* have tac := xxx ---- move: xxx=>tac *)

Lemma example17 m n k : (n + m) * k = (m + n) * k.
Proof.
have: n + m = m + n.
by rewrite addnC.
Restart.
have E: n + m = m + n.
by rewrite addnC.
Restart.
have: n + m = m + n by rewrite addnC.
Restart.
have->: n + m = m + n by rewrite addnC.
Restart.
have: n + m = m + n by rewrite addnC.
move=>->//.
Restart.
have->//: n + m = m + n by rewrite addnC.
Restart.
suff->: n + m = m + n by [].
by rewrite addnC.
Qed.

Lemma example18 m n : m + n = n + m.
Proof.
move: (leqP m n).
Undo.
have:= leqP m n.
Undo.
move: (leqP m n)=>[?|/ltnW ?].
Undo.
have [?|/ltnW ?] := leqP m n.
Restart.
exact: addnC.
Qed.

(* examples from mathcomp book *)
Lemma addnA' (m n k : nat) : m + (n + k) = m + n + k.
Proof. by move: n k; elim: m=>// m IH n k; rewrite !addSn IH. Qed.

(* from bool to proposition *)
Print is_true.
(* Definition is_true b := b = true. *)
(* Coercion is_true : bool >-> Sortclass. *)
Check 2 == 3 : bool.

Lemma leq0n' n : 0 <= n.
Proof. by case: n. Qed.

Lemma eqn_leq' m n : (m == n) = (m <= n) && (n <= m).
Proof. by elim: m n => [|m IHm] []. Qed.

Lemma neq_ltn' m n : (m != n) = (m < n) || (n < m).
Proof. by elim: m n => [|m IHm] []. Qed.

Lemma leqn0' n : (n <= 0) = (n == 0).
Proof. by case: n. Qed.

Lemma dvdn1' d : (d %| 1) = (d == 1).
Proof. by case: d => [|[|d]]. Qed.

Lemma odd_mul' m n : odd (m * n) = odd m && odd n.
Proof.
elim: m => //= m IHm.
rewrite oddD IHm.
rewrite -addTb.
by rewrite andb_addl.
Restart.
by elim: m => //= m IHm; rewrite oddD IHm -addTb andb_addl.
Qed.

Lemma leq_pmull' m n : n > 0 -> m <= n * m.
Proof. move/prednK <-; apply: leq_addr. Qed.

Lemma odd_gt0' n : odd n -> n > 0.
Proof. by case: n. Qed.

Lemma dvdn_mul' d1 d2 m1 m2 : d1 %| m1 -> d2 %| m2 -> d1 * d2 %| m1 * m2.
Proof.
Check dvdnP.
move=>/dvdnP [q1 ->].
move/dvdnP=> [q2 ->].
by rewrite mulnCA -mulnA 2?dvdn_mull.
Restart.
by move=> /dvdnP[q1 ->] /dvdnP[q2 ->]; rewrite mulnCA -mulnA 2?dvdn_mull.
Qed.

Lemma negbK' (b : bool) : ~~ (~~ b) = b.
Proof. by case: b. Qed.

Lemma muln_eq0' m n : (m * n == 0) = (m == 0) || (n == 0).
Proof. by case: m=>[|m]//; case: n; rewrite //muln0. Qed.

Lemma leqE' m n : (m <= n) = (m - n == 0).
Proof. by []. Qed.

Lemma leq_mul2l' m n1 n2 : (m * n1 <= m * n2) = (m == 0) || (n1 <= n2).
Proof. by rewrite !leqE' -mulnBr muln_eq0. Qed.

Section StandardPredicates.
Variable T rT aT: Type.

Implicit Types (op add : T -> T -> T) (f : aT -> rT).

Definition associative' op := forall x y z, op x (op y z) = op (op x y) z.
Definition commutative' op := forall x y, op x y = op y x.
Definition left_distributive' op add :=
    forall x y z, op (add x y) z = add (op x z) (op y z).
Definition right_distributive' op add :=
    forall x y z, op x (add y z) = add (op x y) (op x z).
Definition left_id' e op := forall x, op e x = x.
Definition right_id' e op := forall x, op x e = x.

Definition injective' f := forall x1 x2, f x1 = f x2 -> x1 = x2.
Definition cancel' f g := forall x, g (f x) = x.
Definition pcancel' f g := forall x, g (f x) = Some x.

End StandardPredicates.

Section Chinese.

Variables m1 m2 : nat.
Hypothesis co_m12 : coprime m1 m2.

Lemma chinese_remainder x y :
  (x == y %[mod m1 * m2]) = (x == y %[mod m1]) && (x == y %[mod m2]).
Proof.
wlog le_yx : x y / y <= x; last by rewrite !eqn_mod_dvd // Gauss_dvd.
by have [?|/ltnW ?] := leqP y x; last rewrite !(eq_sym (x %% _)); apply.
Qed.

End Chinese.

(* name convention : see page 66 *)
