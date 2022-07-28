
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
Require Import core.utils.Utils.

Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ModelingMetamodel.
Require Import core.modeling.ConcreteExpressions.
Require Import core.modeling.Parser.

Require Import core.properties.monotonicity.Moore2Mealy_monotonicity_witness.
Require Import core.properties.distributivity.sampleMoore_distributivity.

(*************************************************************)
(** * Distributivity of CoqTL                                *)
(*************************************************************)

Theorem Not_Distributivity:
exists (tr: Transformation) (m1 m2: SourceModel),
  execute tr (Model_app m1 m2) = 
    Model_app (execute tr m1) (execute tr m2) -> False.
Proof.
  eexists Moore2Mealy.
  eexists Moore_m1.
  eexists Moore_m2.
  unfold execute.
  simpl.
  intro.
  unfold Model_app in H.
  simpl in H.
  inversion H.
Qed.