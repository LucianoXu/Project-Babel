
From mathcomp Require Import all_ssreflect.
Require Import Coq.Unicode.Utf8_core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*#############################################################################*)
(** The logic of canonical structure for class system. 

    We can use canonical structures to simulate a class system in the
    object-oriented programming style. Here is a construction template.    
*)


(** The Construction of a class. Here we assume the parameter for the class is
    [T : Type], which can be changed. *)
Module ClassName.
Section ClassDef.

(** The current class may be inherited from multiple classes. Type [mixin_of]
    contains all extra constructions or properties for this class. 
    
    Note that information about base classes should be type of [class_of], not
    [mixin_of].
    *)
Structure mixin_of (T : Type) (** <extra parameters> *) := Mixin {

    (** <some definition here> *)

}.

(** The class information for this type, including the class information 
    [class_of] for base classes and the extra mixin. *)
#[projections(primitive)]
Structure class_of (T : Type) := Class {

    (** <some definition here> *)

    mixin : mixin_of T (** <extra parameters> *);
}.

(** If the current class has no base classes, then [class_of] is identical with
    [mixin_of], and can be defined as an abbreviation: 

Definition class_of := mixin_of.
*)

(** <some local coercions from [class_of] to base classes> *)

Structure type (** <template parameter> *) := Pack { obj; _ : class_of obj }.

Local Coercion obj : type >-> Sortclass.

Variables (T : Type) (cT : type).

(** This definition is meant to take out the class information of an instance. *)
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

(** This definition is for convenient construction of instances. The method
    takes in a [mixin_of] instance and outputs a class instance. *)
Definition pack (m : mixin_of T) : type := Pack (@Class T m).

(** If [class_of] is defined as an abbreviation, then so should pack be: 

Definition pack := Pack.
*)

(** Here we should define some transformation to base class instances. *)

End ClassDef.

(** We can give some extra definition about this class here. *)

Module Exports.
(** <Coercion of class information> *)
#[reversible]
Coercion mixin : class_of >-> mixin_of.
(** Coercion to parameter [T] 
    IMPORTANT : most of the time we want Coq to go through all of its base
    classes one by one. In such cases this direct coercion should be removed.
*)
#[reversible]
Coercion obj : type >-> Sortclass.
(** <Coercion and Canonical to base type instances> *)

(** Some renaming *)
Notation classType := type.
Notation ClassType T m := (@pack T m).

(** Here we can define some descriptive notations like [[ classType of T ]],
    but they are not necessary because reversible coercions can act the same.*)
End Exports.

End ClassName.
Export ClassName.Exports.

(** The procedure of constructing an instance is as follows: 
    1. Construct a [mixin_of] term.
    2. Construct the canonical structure using [ClassName] method.
*)
