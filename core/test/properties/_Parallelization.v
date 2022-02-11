
Require Import String.
Require Import List.
Require Import PeanoNat.
Require Import EqNat.
Require Import Lia.
Require Import FunctionalExtensionality.

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.TransformationConfiguration.

Require Import core.test.iSyntax.
Require Import core.test.iExpressions.
Require Import core.test.iSemantics.

Theorem Parallelization_instantiate:
forall (tc: TransformationConfiguration) (tr: Transformation) (sm: SourceModel) l l1 l2,
 l = l1 ++ l2 ->
  (flat_map (instantiatePattern tr sm) l) = 
    flat_map (instantiatePattern tr sm) l1 ++ flat_map (instantiatePattern tr sm) l2.
Proof.
 intros.
 rewrite H.
 apply flat_map_app.
Qed.


Theorem Parallelization_apply:
forall (tc: TransformationConfiguration) (tr: Transformation) (sm: SourceModel) l l1 l2,
 l = l1 ++ l2 ->
  flat_map (applyPattern tr sm) l = 
    flat_map (applyPattern tr sm) l1 ++ flat_map (applyPattern tr sm) l2.
Proof.
 intros.
 rewrite H.
 apply flat_map_app.
Qed.

