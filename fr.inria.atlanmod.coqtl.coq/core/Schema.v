(** * Schema **)
Require Import core.Graph.
Require Import core.EqDec.
Require Import List.

Class Schema :=
{
    Node: Type;
    nodes_eqdec: EqDec Node;
    nodes_eqb := eq_b;

    Edge: Type;

    InstanceGraph := Graph Node Edge;

    source: Edge -> Node;
    source_in: forall (g: Graph Node Edge) (e: Edge), In e (allEdges g) -> In (source e) (allNodes g);

    target: Edge -> list Node;
    target_in: forall (g: Graph Node Edge) (e: Edge), In e (allEdges g) -> incl (target e) (allNodes g);

}.
