(** * Schema **)
Require Import core.Graph.
Require Import core.EqDec.

Class Schema :=
{
    Node: Type;
    elements_eqdec: EqDec Node;
    elements_eqb := eq_b;

    Edge: Type;
    source: Edge -> Node;
    target: Edge -> list Node;

    InstanceModel := Graph Node Edge;
}.
