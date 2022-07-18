Require Import String.
Require Import EqNat.
Require Import List.
Require Import PeanoNat.
Require Import Lia.
Require Import FunctionalExtensionality.

Require Import core.Semantics.
Require Import core.Syntax.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Import core.Certification.
Require Import core.utils.Utils.

Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ModelingMetamodel.
Require Import core.modeling.ConcreteExpressions.
Require Import core.modeling.Parser.

Require Import transformations.Moore2Mealy.Moore.
Require Import transformations.Moore2Mealy.Moore2Mealy.
Require Import transformations.Moore2Mealy.tests.sampleMoore_injective.


(*************************************************************)
(** * Surjectivity of CoqTL                                  *)
(*************************************************************)

Theorem Surjectivity :
forall (tr: Transformation) (sm : SourceModel) (te : TargetModelElement),
      In te (allModelElements (execute tr sm)) ->
      (exists (sp : list SourceModelElement),
          In sp (allTuples tr sm) /\
          In te (instantiatePattern tr sm sp)).
Proof.
    apply tr_execute_in_elements.
Qed.