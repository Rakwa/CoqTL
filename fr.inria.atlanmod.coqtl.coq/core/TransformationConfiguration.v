Require Import core.Graph.
Require Import core.Schema.

Class TransformationConfiguration := {
  SourceSchema: Schema;
  TargetSchema: Schema;

  SourceNode:= @Node SourceSchema;
  SourceEdge:= @Edge SourceSchema;

  TargetNode:= @Node TargetSchema;
  TargetEdge:= @Edge TargetSchema;

  SourceGraph := @InstanceGraph SourceSchema;
  TargetGraph := @InstanceGraph TargetSchema;

  SourceNode_eqdec := @nodes_eqdec SourceSchema;
  TargetNode_eqdec := @nodes_eqdec TargetSchema;

  SourceNode_eqb := @nodes_eqb SourceSchema;
  TargetNode_eqb := @nodes_eqb TargetSchema;
}.