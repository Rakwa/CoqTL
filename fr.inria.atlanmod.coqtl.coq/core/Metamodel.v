(** * Metamodel **)
Require Import core.Model.
Require Import core.EqDec.

Class Metamodel :=
{
    Node: Type;
    elements_eqdec: EqDec Node;
    elements_eqb := eq_b;

    Edge: Type;
    source: Edge -> Node;
    target: Edge -> list Node;

    InstanceModel := Model Node Edge;
}.
