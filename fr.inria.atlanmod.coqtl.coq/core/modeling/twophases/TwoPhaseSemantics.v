Require Import String.

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.Syntax.
Require Import Bool.
Require Import Arith.
Require Import Semantics.
Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.
Require Import core.Expressions.
Scheme Equality for list.
 

Section TwoPhaseSemantics.

Context {tc: TransformationConfiguration} {mtc: ModelingTransformationConfiguration tc}.  

(** * Apply **)

Definition applyLinkOnPatternTraces
            (oper: OutputPatternLink)
            (tr: Transformation)
            (sm: SourceModel)
            (sp: list SourceNode) (iter: nat) (te: TargetNode) (tls: list TraceLink): option TargetEdge :=
  evalOutputPatternLinkExpr sm sp te iter tls oper.

Definition applyNodeOnPatternTraces
            (ope: OutputPatternNode)
            (tr: Transformation)
            (sm: SourceModel)
            (sp: list SourceNode) (iter: nat) (tls: list TraceLink): list TargetEdge :=
  flat_map (fun oper => 
    match (evalOutputPatternNodeExpr sm sp iter ope) with 
    | Some l => optionToList (applyLinkOnPatternTraces oper tr sm sp iter l tls)
    | None => nil
    end) (OutputPatternNode_getOutputLinks ope).

Definition applyIterationOnPatternTraces (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceNode) (iter: nat) (tls: list TraceLink): list TargetEdge :=
  flat_map (fun o => applyNodeOnPatternTraces o tr sm sp iter tls)
    (Rule_getOutputPatternNodes r).

Definition applyRuleOnPatternTraces (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceNode) (tls: list TraceLink): list TargetEdge :=
  flat_map (fun i => applyIterationOnPatternTraces r tr sm sp i tls)
    (seq 0 (evalIteratorExpr r sm sp)).

Definition applyPatternTraces (tr: Transformation) (sm : SourceModel) (sp: list SourceNode) (tls: list TraceLink): list TargetEdge :=
  flat_map (fun r => applyRuleOnPatternTraces r tr sm sp tls) (matchPattern tr sm sp).

(** * Execute **)

Definition instantiateTraces (tr: Transformation) (sm : SourceModel) :=
  let tls := trace tr sm in
    ( map (TraceLink_getTargetNode) tls, tls ).

Definition applyTraces (tr: Transformation) (sm : SourceModel) (tls: list TraceLink): list TargetEdge :=
  flat_map (fun sp => applyPatternTraces tr sm sp tls) (allTuples tr sm).

Definition executeTraces (tr: Transformation) (sm : SourceModel) : TargetModel :=
  let (elements, tls) := instantiateTraces tr sm in
  let links := applyTraces tr sm tls in
  Build_Model elements links.

End TwoPhaseSemantics.
