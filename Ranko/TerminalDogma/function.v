(** Function.v *)

From mathcomp Require Export all_ssreflect.
Require Export Coq.Unicode.Utf8_core.

(*　世界の創造のため、魂の共鳴を聴くのだ！ *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** injection *)

Definition injective (X Y : Type) (f : X -> Y) := 
    forall x y, f x = f y -> x = y.

(** There is a slightly different definition *)
Definition injective_alt (X Y : Type) (f : X -> Y) :=
    forall x y, x <> y -> f x <> f y.


Record injection (X Y : Type) := build_injection {
    inj_f :> X -> Y;
    inj_proof : injective inj_f;
}.

Lemma injectiveP (X Y : Type) (f : X -> Y) : 
    injective f -> injective_alt f.
Proof. rewrite /injective => H x y Hneq Heq. by apply /Hneq /H. Qed.

(** The inverse direction requires X to be a [eqType]. *)
Lemma injectivePinv (X : eqType) (Y : Type) (f : X -> Y) : 
    injective_alt f -> injective f.
Proof. rewrite /injective_alt => H x y Heq. apply /eqP.
    case E : (x == y) => //. move /eqP : E => {}/H.
    by move : Heq => ->.
Qed.


(** surjection *)
Definition surjective (X Y: Type) (f : X -> Y) :=
    forall y, exists x, f x = y.

Record surjection (X Y : Type) := build_surjection {
    surj_f :> X -> Y;
    surj_proof : surjective surj_f;
}.


(** bijection *)

Definition bijective (X Y: Type) (f : X -> Y) :=
    injective f /\ surjective f.

Record bijection (X Y : Type) := build_bijection {
    bij_f :> X -> Y;
    bij_proof : bijective bij_f;
}.

Lemma id_bijective : forall X, bijective (fun x : X => x).
Proof. split. by move => x y. by move => x; exists x. Qed.


(** inversions *)
(** g is the left inverse of f *)
Definition left_inverse (X Y : Type) (g : Y -> X) (f : X -> Y) :=
    forall x, g (f x) = x.

(** g is the right inverse of f *)
Definition right_inverse (X Y : Type) (g : Y -> X) (f : X -> Y) :=
    forall y, f (g y) = y.

(** g is the inverse of f *)
Definition inverse (X Y : Type) (g : Y -> X) (f : X -> Y) :=
    left_inverse g f /\ right_inverse g f.


Definition invertible (X Y : Type) (f : X -> Y) :=
    exists g : Y -> X, inverse g f.

(** invertibale functions are bijections *)
Lemma inv_is_bij (X Y : Type) (f : X -> Y) : invertible f -> bijective f.
Proof. move => [g [H1 H2]]. split.
    rewrite /injective => a b Heq. 
    rewrite -(H1 a) Heq. by apply H1.
    rewrite /surjective => y. by exists (g y); apply H2.
Qed.


Lemma bij_has_inv (X Y : Type) (f : X -> Y) : 
    bijective f -> exists g : bijection Y X, inverse g f.
Admitted.




(** function Composition *)
Definition fun_comp (X Y Z : Type) (f : X -> Y) (g : Y -> Z) : X -> Z :=
    fun x => g (f x).

Notation " g '◦' f " := (fun_comp f g) (at level 40).



(** Composition is associative *)
Lemma fun_comp_assoc (X Y Z W : Type) (f : X -> Y) (g : Y -> Z) (h : Z -> W) :
    h ◦ (g ◦ f) = (h ◦ g) ◦ f.
Proof. by []. Qed.


Lemma comp_injective (X Y Z : Type) (f : X -> Y) (g : Y -> Z) :
    injective f -> injective g -> injective (g ◦ f).
Proof. rewrite /fun_comp => Hf Hg.
    move => x y Hxy. by apply /Hf /Hg.
Qed.

Lemma comp_surjective (X Y Z : Type) (f : X -> Y) (g : Y -> Z) :
    surjective f -> surjective g -> surjective (g ◦ f).
Proof. rewrite /surjective /fun_comp => Hf Hg z.
    destruct (Hg z) as [y Hy]. destruct (Hf y) as [x Hx].
    exists x. by rewrite Hx.
Qed.

Lemma comp_bijective (X Y Z : Type) (f : X -> Y) (g : Y -> Z) :
    bijective f -> bijective g -> bijective (g ◦ f).
Proof. move => [Hfi Hfs] [Hgi Hgs]. split.
    by apply /comp_injective. by apply /comp_surjective.
Qed.
