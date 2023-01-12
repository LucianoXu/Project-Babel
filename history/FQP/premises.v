From Ranko Require Export TerminalDogma.premises.

(** We use classical logic. *)
Require Export Classical.

(** We use a broader criteria of equivalence. *)
(** We consider functions only on its output. *)
Require Export FunctionalExtensionality.
(** We consider propositions only on its provability. *)
Require Export PropExtensionality.
(** We don't distinguish between the proofs of the same proposition. *)
Require Export ProofIrrelevance.

(** We allow definite description. In other words, when we know that there
    exists a unique item satisfying some proposition, we can construct that
    element. 
    
    Note : There are two kind of 'description', namely the definite one and the
    indefinite one. In analysis we require that a function exists only if there
    exists a 'unique' item, not 'some' item, satisfying the property. Therefore
    definite description is assumed. *)
Require Export Description.
Require Import ChoiceFacts.
    