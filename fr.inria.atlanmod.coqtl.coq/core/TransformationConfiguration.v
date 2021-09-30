Require Import core.Graph.
Require Import core.Schema.

Class TransformationConfiguration := {
  SourceSchema: Schema;
  TargetSchema: Schema;

  SourceNode:= @Node SourceSchema;
  SourceEdge:= @Edge SourceSchema;

  TargetNode:= @Node TargetSchema;
  TargetEdge:= @Edge TargetSchema;

  SourceModel := @InstanceModel SourceSchema;
  TargetModel := @InstanceModel TargetSchema;

  SourceNode_eqdec := @elements_eqdec SourceSchema;
  TargetNode_eqdec := @elements_eqdec TargetSchema;

  SourceNode_eqb := @elements_eqb SourceSchema;
  TargetNode_eqb := @elements_eqb TargetSchema;
}.