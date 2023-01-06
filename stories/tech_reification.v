Require Import Arith.

Section LargeProofTerm.

Inductive is_even : nat -> Prop :=
| even_O : is_even 0
| even_SS : forall n, is_even n -> is_even (S (S n)).

Goal is_even 10.
Proof.
    repeat (apply even_SS || apply even_O).
    Show Proof.
Qed.

Goal is_even (10 * 10 * 10 * 10).
Proof.
    Time (repeat (apply even_SS || apply even_O)).
    Show Proof.
Abort.

(* Proof by Reflection *)
Fixpoint dec_even (n : nat) :=
    match n with
    | 0 => true
    | 1 => false
    | S (S n') => dec_even n'
    end.

Lemma strong_induction (P : nat -> Prop) :
    (forall m, (forall k, k < m -> P k) -> P m)
    -> (forall n, P n).
Proof.
    intros sIH n.
    enough (G : forall p, p <= n -> P p).
    - apply G. constructor.
    - induction n.
        + intros p H. inversion H. apply sIH. intros k HH. inversion HH.
        + intros p H. apply sIH. intros k Hk. apply IHn.
          enough (HH : k < S n) by (apply (Nat.lt_succ_r); assumption).
          apply (Nat.lt_le_trans k p (S n)); assumption.
Qed.

Lemma dec_even_sound (n : nat): 
    dec_even n = true -> is_even n.
Proof.
    induction n as [n IH] using strong_induction.
    destruct n. constructor. destruct n. discriminate.
    simpl. intros Hn. apply even_SS. auto.
Qed.

Goal is_even (10 * 10 * 10 * 10).
Proof.
    apply dec_even_sound. 
    (* dec_even (10 * 10 * 10 * 10) == dec_even 10000 == true *)
    (* vm_compute is faster than simpl, but produces less readable result *)
    vm_compute.
    reflexivity.
    Show Proof. 
    (* !!!!!!!! The key part of the proof term is just some eq_refl !!!!!!!! *)
Qed.

Goal is_even (100 * 100 * 100 * 100).
Proof.
    apply dec_even_sound.
Abort.

Inductive mexp : Set :=
| Num (n : nat)
| Mul (e1 e2 : mexp).

Fixpoint meval (e : mexp) :=
    match e with
    | Num n => n
    | Mul e1 e2 => (meval e1) * (meval e2)
    end.

Check (eq_refl : meval (Mul (Num 10) (Num 10)) = 10 * 10).

Fixpoint dec_even_mexp (e : mexp) :=
    match e with
    | Num n => dec_even n
    | Mul e1 e2 => orb (dec_even_mexp e1) (dec_even_mexp e2)
    end.

Lemma is_even_add x y :
    is_even x -> is_even y -> is_even (x + y).
Proof.
    revert y.
    induction x as [x IH] using strong_induction. intros y Hx. 
    destruct x. intros; assumption. destruct x; inversion Hx.
    intros Hy. simpl. constructor. auto.
Qed.
    
Lemma is_even_mul x y :
    is_even x \/ is_even y -> is_even (x * y).
Proof.
    intros H. case H.
    - intros Hx. rewrite Nat.mul_comm. induction y.
      + constructor.
      + simpl. apply is_even_add; auto.
    - intros Hy. induction x.
      + constructor.
      + simpl. apply is_even_add; auto.
Qed.


Lemma dec_even_mexp_sound e :
    dec_even_mexp e = true -> is_even (meval e).
Proof.
    induction e.
    - simpl. apply dec_even_sound.
    - simpl. intros H. apply Bool.orb_prop in H. apply is_even_mul. case H.
      + intros H1. left. auto.
      + intros H2. right. auto.
Qed.

Goal is_even (100 * 100 * 100 * 100).
Proof.
    (* change P replace the current goal with P, 
       when P and the current goal are judgementally equal (convertible) *)
    Fail change (true = true).
    change (is_even (meval (Mul (Mul (Mul (Num 100) (Num 100)) (Num 100)) (Num 100)))).
    apply dec_even_mexp_sound.
    simpl.
    reflexivity.
Qed.

(*  How to obtain (meval (Mul (Mul (Mul (Num 100) (Num 100)) (Num 100)) (Num 100)))
    from 100 * 100 * 100 * 100 ?

    Reification
*)

Ltac rf_mul x := 
    match x with
    | ?n * ?m =>
        let n' := rf_mul n in
        let m' := rf_mul m in
            constr:(Mul n' m')
    | _ => constr:(Num x)
    end.

(* For Ltac, see Section 7.6 in CoqArt and Chapter 14 in Certified Programming with Dependent Types *)

Goal is_even (123 * 100 * 100 * 100).
Proof.
    match goal with
    | [|- is_even ?x] => 
        let x' := rf_mul x in
            change (is_even (meval x'))
    end.
    apply dec_even_mexp_sound.
    simpl.
    reflexivity.
    Show Proof.
Qed.

End LargeProofTerm.

Section PlusExp.

Fixpoint plusn0 (n x : nat) :=
    match n with
    | 0 => x
    | S n => plusn0 n (x + 0)
    end.

Variable n : nat.
Goal plusn0 10 n = n.
Proof.
    simpl. rewrite <- !plus_n_O. reflexivity.
    Show Proof.
Qed.

Goal plusn0 100 n = n.
Proof.
    Time (vm_compute; rewrite <- !plus_n_O; reflexivity).
Qed.

Inductive aexp : Set :=
| AZero
| ANum (n : nat)
| APlus (a1 a2 : aexp).

Fixpoint aeval (a : aexp) : nat :=
    match a with
    | AZero => 0
    | ANum n => n
    | APlus a1 a2 => (aeval a1) + (aeval a2)
    end.

Fixpoint opt0 (a : aexp) : aexp :=
    match a with
    | APlus AZero a => opt0 a
    | APlus a AZero => opt0 a
    | APlus a1 a2 => APlus (opt0 a1) (opt0 a2)
    | _ => a
    end.

Lemma opt0_sound (a : aexp) :
    aeval a = aeval (opt0 a).
Proof.
    induction a as [ | | a1 IHa1 a2 IHa2]; try reflexivity.
    destruct a1 eqn:Ea1.
    - simpl. rewrite IHa2. reflexivity.
    - simpl. destruct a2; try reflexivity.
        + simpl. rewrite <- plus_n_O. reflexivity.
        + simpl. simpl in IHa2. rewrite IHa2. reflexivity.
    - destruct a2 eqn:Ea2.
        + simpl. simpl in IHa1. rewrite IHa1. rewrite <- plus_n_O. reflexivity.
        + simpl. simpl in IHa1. rewrite IHa1. reflexivity.
        + simpl. simpl in IHa1. simpl in IHa2. rewrite IHa1. rewrite IHa2. reflexivity.
Qed.


Fixpoint plusn0_aexp (n x : nat) :=
    match n with
    | 0 => ANum x
    | S n => APlus (plusn0_aexp n x) AZero
    end.

Eval simpl in (plusn0_aexp 10 n).
Eval simpl in aeval (plusn0_aexp 10 n).


Goal plusn0 10 n = n.
Proof.
    (* plusn0 10 n == aeval (plusn0_aexp 10 n) *)
    change (aeval (plusn0_aexp 10 n) = n).
    rewrite opt0_sound.
    simpl.
    reflexivity.
    Show Proof.
Qed.

Goal plusn0 20 n = n.
Proof.
    Time (simpl; rewrite <- !plus_n_O; reflexivity).
    Restart.
    Time (change (aeval (plusn0_aexp 20 n) = n);
    rewrite opt0_sound;
    simpl;
    reflexivity).
Qed.

(* how to obtain (APlus (ANum a) AZero) from (a + 0)? *)

Ltac rf_plus a :=
    match a with
    | (?x + ?y) => 
        let x' := rf_plus x in
        let y' := rf_plus y in
        constr:(APlus x' y')
    | 0 => constr:(AZero)
    | _ => constr:(ANum a)
    end.

Goal False.
let x := rf_plus (n + (n + 0) + 0) in pose x as a.
Abort.

Goal plusn0 10 n = n.
Proof.
    simpl.
    match goal with
    | [|- ?x = ?y] => 
        let x' := rf_plus x in 
        change (aeval x' = y)
    end.
    rewrite opt0_sound.
    simpl.
    reflexivity.
Defined.

(* association *)

(* h + (t1 + t2 + t3 + ...) -> (((h + t1) + t2) + t3) + ... *)
Fixpoint norm_asc_tail (h t : aexp) :=
    match t with
    | APlus t1 t2 => norm_asc_tail (norm_asc_tail h t1) t2
    | _ => APlus h t
    end.

Fixpoint norm_asc (a : aexp) :=
    match a with
    | APlus a1 a2 => norm_asc_tail (norm_asc a1) a2
    | _ => a
    end.

Eval simpl in (norm_asc (APlus (APlus AZero AZero) (APlus AZero AZero))).

Lemma norm_asc_tail_sound (h t : aexp):
    aeval (APlus h t) = aeval (norm_asc_tail h t).
Proof.
    generalize dependent h.
    induction t as [| | t1 IHt1 t2 IHt2]; try reflexivity.
    intros h. simpl. rewrite <- IHt2. simpl. rewrite <- IHt1.
    simpl. rewrite Nat.add_assoc. reflexivity.
Qed.
    
Lemma norm_asc_sound : forall t,
    aeval t = aeval (norm_asc t).
Proof.
    induction t as [| | t1 IHt1 t2 IHt2]; try reflexivity.
    simpl. rewrite <- norm_asc_tail_sound. simpl. rewrite <- IHt1. reflexivity.
Qed.

Goal forall (x y z m n : nat),
    x + ((y + (z + m)) + n) = x + (y + (z + (m + n))).
Proof.
    intros.
    rewrite !Nat.add_assoc.
    reflexivity.
    Show Proof.
Qed.

Goal forall (x y z m n : nat),
    x + ((y + (z + m)) + n) = x + (y + (z + (m + n))).
Proof.
    intros.
    match goal with
    | [|- ?l = ?r] => 
        let l' := rf_plus l in
        let r' := rf_plus r in
        refine (_ : aeval l' = aeval r');
        rewrite (norm_asc_sound l');
        rewrite (norm_asc_sound r')
    end.
    simpl.
    reflexivity.
    Show Proof.
Qed.

End PlusExp.

(* For more on reification, see
   http://adam.chlipala.net/papers/ReificationITP18/
   https://github.com/LPCIC/coq-elpi
*)