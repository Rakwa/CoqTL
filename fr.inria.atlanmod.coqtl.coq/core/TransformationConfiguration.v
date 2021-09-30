Require Import core.Model.
Require Import core.Metamodel.

Class TransformationConfiguration := {
  SourceMetamodel: Metamodel;
  TargetMetamodel: Metamodel;

  SourceModelElement:= @ModelElement SourceMetamodel;
  TargetModelElement:= @ModelElement TargetMetamodel;

  SourceModel := @InstanceModel SourceMetamodel;
  TargetModel := @InstanceModel TargetMetamodel;

  SourceElement_eqdec := @elements_eqdec SourceMetamodel;
  TargetElement_eqdec := @elements_eqdec TargetMetamodel;

  SourceElement_eqb := @elements_eqb SourceMetamodel;
  TargetElement_eqb := @elements_eqb TargetMetamodel;
}.