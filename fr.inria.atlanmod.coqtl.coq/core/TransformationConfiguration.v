Require Import core.Model.
Require Import core.Metamodel.

Class TransformationConfiguration := {
  SourceMetamodel: Metamodel;
  TargetMetamodel: Metamodel;

  SourceNode:= @Node SourceMetamodel;
  SourceEdge:= @Edge SourceMetamodel;

  TargetNode:= @Node TargetMetamodel;
  TargetEdge:= @Edge TargetMetamodel;

  SourceModel := @InstanceModel SourceMetamodel;
  TargetModel := @InstanceModel TargetMetamodel;

  SourceNode_eqdec := @elements_eqdec SourceMetamodel;
  TargetNode_eqdec := @elements_eqdec TargetMetamodel;

  SourceNode_eqb := @elements_eqb SourceMetamodel;
  TargetNode_eqb := @elements_eqb TargetMetamodel;
}.