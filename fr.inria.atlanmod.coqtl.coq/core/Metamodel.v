(** * Metamodel **)
Require Import core.Model.
Require Import core.EqDec.

Class Metamodel :=
{
    ModelElement: Type;
    
    elements_eqdec: EqDec ModelElement;

    (* Decidable Equality*)
    elements_eqb := eq_b;

    InstanceModel := Model ModelElement;
}.
