

Declare Scope MetaLan_Scope.
Open Scope MetaLan_Scope.

Reserved Notation " P ∙ s " (at level 20).
Reserved Notation " ⌈ P ⇒ Q ⌉ ".
Reserved Notation " P '=asn' Q " (at level 70).
Reserved Notation " x '=stt' y " (at level 70).


Reserved Notation " ⊨ { P } f { Q } " (at level 10, P, f, Q at next level).
Reserved Notation " ⊨ [ x ] g [ y ] " (at level 10, x, g, y at next level).

(** Note that the following two only talks in the syntax level. *)
Reserved Notation " ⊢ { P } s { Q } " (at level 10, P, s, Q at next level).
Reserved Notation " ⊢ < ax > { P } s { Q } " (at level 10, ax, P, s, Q at next level).
Reserved Notation " ⊢ [ x ] s [ y ] " (at level 10, x, s, y at next level).

Reserved Notation " 'wp' < bwd > " (at level 50, bwd at next level).


Reserved Notation " f ^← " (at level 90). 
Reserved Notation " g ^→ " (at level 90).