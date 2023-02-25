
(*
Theorem fin_inf_neq : forall n : nat, {x | 1 <= x <= n} <> nat.
Proof. move => n H. 
    have Hcontra : {x | 1 <= x <= n} ≅ nat. { rewrite H. apply isomorphic_refl. }
Admitted.
*)