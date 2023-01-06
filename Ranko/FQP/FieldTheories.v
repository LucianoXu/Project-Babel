Require Export premises.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Field.

Module Export FieldTheory.

Export Field.

Record field := build_field {
    R_field :> Type;
    rO : R_field;
    rI : R_field;
    radd : R_field -> R_field -> R_field;
    rmul : R_field -> R_field -> R_field;
    rsub : R_field -> R_field -> R_field;
    ropp : R_field -> R_field;
    rdiv : R_field -> R_field -> R_field;
    rinv : R_field -> R_field;
    req : R_field -> R_field -> Prop;
    field_proof :> @field_theory R_field rO rI radd rmul rsub ropp rdiv rinv req;
}.

End FieldTheory.