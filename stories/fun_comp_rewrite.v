(** * fun_comp_rewrite.v : describing parallel quantum programs *)
From mathcomp Require Export all_ssreflect.


Notation " g '◦' f " := (fun x => g (f x)) (at level 40).
Notation "[ 'eta' f ]" := (fun x => f x) : fun_scope.

From Coq Require Import Classical Arith Relations Reals
                        FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** Problem *)
Lemma problem {X Y Z : Type} (f f': X -> Y) (g g': Y -> Z) (x : X)
    (Heq : g ◦ f = g' ◦ f') : g (f x) = g' (f' x).
Proof.
    (** We cannot rewrite Heq directly. *)
    Fail rewrite Heq.
Abort.


(** Even we can fold the form on the left to that on the right, it will still
    apear in the form on the left. *)
Lemma f_fold {X Y Z: Type} (f : X -> Y) (g : Y -> Z) (x : X) :
    g (f x) = (g ◦ f) x.
Proof. reflexivity. Qed.


(** This means that functional extensionality implies the equality of a
    funciton and it's beta reduction. *)
Lemma eta_eq {X Y : Type} (f : X -> Y) : [ eta f ] = f.
Proof. by apply functional_extensionality => x. Qed.

Lemma eta_x_eq {X Y : Type} (f : X -> Y) (x : X): [ eta f ] x = f x.
Proof. by []. Qed.

(** We need this function to transform the equality of functions. *)
Lemma fIns {X Y : Type} (f g: X -> Y) : 
    f = g -> forall x, f x = g x.
Proof. by move => ->. Qed.

(** This one is already defined in Coq. *)
About equal_f.
About equal_f_dep.

Lemma test1 {X Y : Type} (f f': X -> Y) (x : X)
    (Heq :  [eta f]  = [eta f']) : f x = f' x.
Proof. Set Printing All. 
    (** direct rewrite of eta expansion is not allowed. *)
    Fail rewrite Heq. 

    (** In the single function case, the folloing rewrite can do. *)
    rewrite !eta_eq in Heq. by rewrite Heq.
    
    Restart.
    (** The more general approach is like this. *)
    by apply (fIns Heq).
Qed. 



(** but we cannot rewrite the function composition, even they are equal. *)
Lemma test2 {X Y Z : Type} (f f': X -> Y) (g g': Y -> Z) (x : X)
    (Heq : g ◦ f = g' ◦ f') : g (f x) = g' (f' x).
Proof.
    (** still, a direct rewrite is not allowed *)
    Fail rewrite Heq.
    (** it turen out that such special type hint is needed. *)
    Fail apply f_ins.
    apply (fIns Heq).
Qed.
    
(** It turns out to be relevant to something called eta expansion and 
    reduction. We find that terms like (f ◦ g) x will always appear as f (g x) 
    in Coq, and the later is not convertiable to the former. *)

(** In one word, [(f ◦ g) x] is convertible to [f (g x)], but the inverse
    direction is not convertible. To rewrite using premises like 
    [(f ◦ g) = h], we can transform the premise into the instantiated version. *)

Lemma test3 {X Y Z W: Type} (f f': X -> Y) (g g': Y -> Z) (h h' : Z -> W)
    (Heq : f = f') : h ◦ g ◦ f = h ◦ g ◦ f'.
Proof. 
    (** look how this goal is automaticall changed. *)
    have t : True.
    Undo.
    (** It's obvious that the rewrite will not work as expected. *)
    rewrite Heq.
Abort.



(** But if we use the new definition ... *)
Reset Initial.

From Babel Require Import TerminalDogma.premises
                          TerminalDogma.Extensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** We may still need this function. *)
Lemma fIns {X Y : Type} (f g: X -> Y) : 
    f = g -> forall x, f x = g x.
Proof. by move => ->. Qed.

Lemma testa {X Y Z : Type} (f f': X -> Y) (g g': Y -> Z) (x : X)
    (Heq : g ◦ f = g' ◦ f') : (g ◦ f) x = (g' ◦ f') x.
Proof.
    (** We can directly rewrite this equality. *)
    rewrite Heq. by [].
Qed.

Lemma test2 {X Y Z : Type} (f f': X -> Y) (g g': Y -> Z) (x : X)
    (Heq : g ◦ f = g' ◦ f') : g (f x) = g' (f' x).
Proof.
    (** This trick still works. *)
    apply (fIns Heq).
Qed.

Lemma test3 {X Y Z W: Type} (f f': X -> Y) (g g': Y -> Z) (h h' : Z -> W)
    (Heq : f = f') : h ◦ g ◦ f = h ◦ g ◦ f'.
Proof.
    (** This time the rewrite works as expected in maths. *)
    rewrite Heq. by [].
Qed.

(** Let's consider the two different *)
Notation " g '\◦' f " := (fun x => g (f x)) (at level 40).

Lemma fun_compP {X Y Z : Type} (g : Y -> Z) (f : X -> Y) :
    g \◦ f = g ◦ f.
Proof. by []. Qed.

Lemma test2B {X Y Z : Type} (f f': X -> Y) (g g': Y -> Z) (x : X)
    (Heq : g \◦ f = g' \◦ f') : g (f x) = g' (f' x).
Proof.
    (** somehow we cannot fold the definition *)
    Fail fold fun_comp in Heq.

    (** the SSR rewrite also gives an identical result... *)
    rewrite -/fun_comp in Heq.

    (** using an extra lemma will do *)
    rewrite !fun_compP in Heq.

    (** but this [fun_compP] still cannot rewrite the goal *)
    Fail rewrite fun_compP.
    apply (fIns Heq).
Qed.

(** 2023/1/18 *)

