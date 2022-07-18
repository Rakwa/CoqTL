
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

Require Import transformations.Moore2Mealy.Moore2Mealy_monotonicity_witness.
Require Import transformations.Moore2Mealy.tests.sampleMoore_mono.

(*************************************************************)
(** * Monotonicity of CoqTL                                  *)
(*************************************************************)


Definition SourceModel_elem_incl {tc: TransformationConfiguration}  (m1 m2: SourceModel) : Prop := 
  incl (allModelElements m1) (allModelElements m2). 

Definition TargetModel_elem_incl {tc: TransformationConfiguration}  (m1 m2: TargetModel) : Prop := 
  incl (allModelElements m1) (allModelElements m2). 

Definition Monotonicity 
   (tr: Transformation) :=
forall sm1 sm2,
    SourceModel_elem_incl sm1 sm2 ->
    TargetModel_elem_incl (execute tr sm1) (execute tr sm2).  

Lemma Moore2Mealy_non_mono_contrapos:
exists sm1 sm2 : SourceModel,
 SourceModel_elem_incl sm1 sm2 /\
 ~ TargetModel_elem_incl (execute Moore2Mealy sm1) (execute Moore2Mealy sm2).
Proof.
eexists Moore_m1.
eexists Moore_m2.
split.
- unfold SourceModel_elem_incl.
  simpl.
  remember (Moore.Build_MooreMetamodel_Object Moore.StateClass
  (Moore.BuildState "S0" "1")) as elem.
  unfold incl.
  intros.
  destruct H.
  crush.
  destruct H.
- unfold TargetModel_elem_incl.
  simpl.
  crush.
  apply incl_l_nil in H.
  crush.
Qed.

Theorem Moore2Mealy_non_mono:
    exists tr, Monotonicity tr -> False.
Proof.
eexists Moore2Mealy.
unfold Monotonicity.
intro mono.
specialize (Moore2Mealy_non_mono_contrapos) as mono_contrapos.
crush.
Qed.