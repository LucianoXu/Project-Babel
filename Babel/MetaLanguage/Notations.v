

Declare Scope MetaLan_scope.
Open Scope MetaLan_scope.

Reserved Notation " P ∙ s " (at level 20).
Reserved Notation " P ∙ s :> mT" (at level 20, s at next level).
Reserved Notation " ⌈ P ⇒ Q ⌉ ".
Reserved Notation " ⌈ P ⇒ Q ⌉ :> mT " (at level 20, Q at next level).

Reserved Notation " P '=FD' Q " (at level 70).
Reserved Notation " x '=BD' y " (at level 70).


Reserved Notation " ⊨ { P } f { Q } " (at level 10, P, f, Q at next level).
Reserved Notation " ⊨ [ x ] g [ y ] " (at level 10, x, g, y at next level).

(** Note that the following two only talks in the syntax level. *)
Reserved Notation " ax ⊢ P ⇒ Q " (at level 10, P, Q at next level).


Reserved Notation " ⊢ { P } s { Q } " (at level 10, P, s, Q at next level).
Reserved Notation " ⊢ < ax > { P } s { Q } " (at level 10, ax, P, s, Q at next level).
Reserved Notation " ⊢ [ x ] s [ y ] " (at level 10, x, s, y at next level).

Reserved Notation " ⟦ s ⟧ < de > " (at level 50, de at next level).

Reserved Notation " x ⊕[ Hj ] y " (at level 50, Hj, y at next level).

Reserved Notation " f ^← " (at level 90). 
Reserved Notation " g ^→ " (at level 90).

Reserved Notation "s0 ⨾ s1" (at level 10).
Reserved Notation "'If' M 'Then' s0 'Else' s1 'End'".
Reserved Notation "'While' M 'Do' s0 'End'".

Reserved Notation " P ‖ Q " (at level 10).
