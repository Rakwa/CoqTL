(** * Metamodel **)
Require Import core.Model.
Require Import core.EqDec.

Class Metamodel :=
{
    ModelElement: Type;
    elements_eqdec: EqDec ModelElement;
    elements_eqb := eq_b;

    ModelLink: Type;
    source: ModelLink -> ModelElement;
    target: ModelLink -> list ModelElement;

    InstanceModel := Model ModelElement ModelLink;
}.
