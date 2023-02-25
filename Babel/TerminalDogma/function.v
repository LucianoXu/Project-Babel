(** function.v *)
(* 想要改名为大写首字母，但在Windows系统下还是不行啊。将就一下吧！*)
From mathcomp Require Export all_ssreflect.
Require Export Coq.Unicode.Utf8_core.

From Babel Require Import CanonicalInfrastructure.

(*　世界の創造のため、魂の共鳴を聴くのだ！ *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Declare Scope TerminalDogma_scope.
Open Scope TerminalDogma_scope.


(*####################################################################*)
(** injection *)

Module Injection.
Section ClassDef.

Definition mixin_of (X Y : Type) (f : X -> Y) := 
    forall x y, f x = f y -> x = y.
Definition class_of := mixin_of.



Structure type X Y := Pack { obj : X -> Y; _ : class_of obj }.

Variable (X Y : Type) (cT : type X Y).

Definition class := let: Pack _ c := cT return class_of (obj cT) in c.

Definition pack := Pack.

End ClassDef.

Module Exports.
#[reversible] Coercion obj : type >-> Funclass.
Arguments class {X Y} cT.

Notation injection := type.
Notation Injection T m := (@pack _ _ T m).
Notation "[ 'injection' 'of' T ]" := (T : type _ _)
  (at level 0, format "[ 'injection'  'of'  T ]").
End Exports.

End Injection.
Export Injection.Exports.


(** There is a slightly different definition *)
Definition injective_alt (X Y : Type) (f : X -> Y) :=
    forall x y, x <> y -> f x <> f y.


Lemma injectiveP (X Y : Type) (f : injection X Y) : injective_alt f.
Proof. 
    move => x y Hneq Heq. apply /Hneq. move : Heq. 
    by apply Injection.class. 
Qed.

(** The inverse direction requires X to be a [eqType]. *)
Lemma injectivePinv (X : eqType) (Y : Type) (f : X -> Y) : 
    injective_alt f -> Injection.class_of f.
Proof. rewrite /injective_alt => H x y Heq. apply /eqP.
    case E : (x == y) => //. move /eqP : E => {}/H.
    by move : Heq => ->.
Qed.


(*####################################################################*)
(** surjection *)

Module Surjection.
Section ClassDef.

Definition mixin_of (X Y : Type) (f : X -> Y) := forall y, exists x, f x = y.
Definition class_of := mixin_of.


Structure type X Y := Pack { obj : X -> Y; _ : class_of obj }.

Variable (X Y : Type) (cT : type X Y).

Definition class := let: Pack _ c := cT return class_of (obj cT) in c.

Definition pack := Pack.

End ClassDef.

Module Exports.
#[reversible] Coercion obj : type >-> Funclass.
Arguments class {X Y} cT.

Notation surjection := type.
Notation Surjection T m := (@pack _ _ T m).
Notation "[ 'surjection' 'of' T ]" := (T : type _ _)
  (at level 0, format "[ 'surjection'  'of'  T ]").
End Exports.

End Surjection.
Export Surjection.Exports.



(*####################################################################*)
(** bijection
    note that this class has no mixin *)

Module Bijection.
Section ClassDef.

#[projections(primitive)]
Record class_of (X Y: Type) (f : X -> Y) := Class {
    Inj_class : Injection.class_of f;    
    Surj_class : Surjection.class_of f;
}.


Structure type (X Y : Type) := Pack {
    obj : X -> Y;
    _ : class_of obj;
}.

Variable (X Y : Type) (cT : type X Y).

Definition class := let: Pack _ c := cT return class_of (obj cT) in c.

Definition pack := Pack.

Definition injection := Injection (obj cT) (Inj_class class).

Definition surjection := Surjection (obj cT) (Surj_class class).

End ClassDef.

Module Exports.
#[reversible] Coercion injection : type >-> Injection.type.
Canonical injection.
#[reversible] Coercion surjection : type >-> Surjection.type.
Canonical surjection.

Arguments class {X Y} cT.

Notation bijection := type.
Notation Bijection T m := (@pack _ _ T m).
Notation "[ 'bijection' 'of' T ]" := (T : type _ _)
    (at level 0, format "[ 'bijection'  'of'  T ]").
End Exports.

End Bijection.
Export Bijection.Exports.


(*
Lemma id_bijective : forall X, bijective (fun x : X => x).
Proof. split. by move => x y. by move => x; exists x. Qed.
*)

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

(*
(** invertibale functions are bijections *)
Lemma inv_is_bij (X Y : Type) (f : X -> Y) : invertible f -> bijective f.
Proof. move => [g [H1 H2]]. split.
    rewrite /injective => a b Heq. 
    rewrite -(H1 a) Heq. by apply H1.
    rewrite /surjective => y. by exists (g y); apply H2.
Qed.
*)

Definition inv_bij (X Y : Type) : bijection X Y -> bijection Y X.
Admitted.

Lemma inv_bij_inv (X Y : Type) (f : bijection X Y) :
    inverse f (inv_bij f).
Admitted.




(** function Composition 
    [fun_comp g f] : Apply [f] first, and then apply [g].
    We use a definition encapsulation to avoid the automatic simplification of
    [ g ◦ f ] *)
Definition fun_comp {X Y Z : Type} (g : Y -> Z) (f : X -> Y) : X -> Z :=
    fun x => g (f x).

(** Note : This notation is right associate. *)
Notation " g ◦ f " := (fun_comp g f) (at level 15, right associativity)
    : TerminalDogma_scope.

(** The equivalence between the function compostion defined here and that in
    Coq. *)
Lemma fun_compP {X Y Z : Type} (g : Y -> Z) (f : X -> Y) :
    (fun x => g (f x)) = g ◦ f.
Proof. by []. Qed.

(** Composition is associative *)
Lemma fun_assoc (X Y Z W : Type) (f : X -> Y) (g : Y -> Z) (h : Z -> W) :
    (h ◦ g) ◦ f = h ◦ g ◦ f.
Proof. by []. Qed.

(** This definition can be used togher with [equal_f] and [equal_f_dep] in 
    [Coq.Logic.FunctionalExtensionality]. 
    
    Here are the identical definitions. 
*)
Lemma equal_f : forall {A B : Type} {f g : A -> B},
    f = g -> forall x, f x = g x.
Proof.
    intros A B f g H x.
    rewrite H.
    auto.
Qed.

Lemma equal_f_dep : forall {A B} {f g : forall (x : A), B x},
    f = g -> forall x, f x = g x.
Proof.
    intros A B f g <- H; reflexivity.
Qed.
      
(** This tactic transforms an equality [f x = g x] into [f = g]. *)
Ltac equal_f_comp A := 
    generalize dependent A; 
    apply equal_f;
    repeat rewrite fun_compP.

(*
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
*)
