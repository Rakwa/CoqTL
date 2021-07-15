Require Import String.

Require Import core.utils.Utils.
Require Import core.Metamodel.
Require Import core.Model.
Require Import core.Syntax.
Require Import Bool.
Require Import Arith.
Require Import Semantics.
Require Import core.EqDec.
Scheme Equality for list.
 

Section IterateTracesByRuleSemantics.

  Context {SourceModelElement SourceModelLink SourceModelClass SourceModelReference: Type}.
  Context {smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference}.
  Context {TargetModelElement TargetModelLink TargetModelClass TargetModelReference: Type}.
  Context {tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference}.
  Context (SourceModel := Model SourceModelElement SourceModelLink).
  Context (TargetModel := Model TargetModelElement TargetModelLink).
  Context (Transformation := @Transformation SourceModelElement SourceModelLink SourceModelClass TargetModelElement TargetModelLink).

  Definition allModelElementsOfType (t: SourceModelClass) (sm: SourceModel) : list SourceModelElement :=
    filter (hasType t) (allModelElements sm).

  Definition allModelElementsOfTypes (l: list SourceModelClass) (sm: SourceModel): list (list SourceModelElement) :=
    map (fun t:SourceModelClass => allModelElementsOfType t sm) l.

  Definition allTuplesOfTypes (l: list SourceModelClass) (sm: SourceModel): list (list SourceModelElement) := 
    fold_right prod_cons [nil] (allModelElementsOfTypes l sm).

  Definition allTuplesByRule (tr: Transformation) (sm : SourceModel) :list (list SourceModelElement) :=
    (flat_map (fun (r:Rule) => allTuplesOfTypes (Rule_getInTypes r) sm) (Transformation_getRules tr)).

  (** * Apply **)

  Definition applyReferenceOnPatternTraces
             (oper: OutputPatternElementReference)
             (tr: Transformation)
             (sm: SourceModel)
             (sp: list SourceModelElement) (iter: nat) (te: TargetModelElement) (tls: list TraceLink): option TargetModelLink :=
    evalOutputPatternLinkExpr sm sp te iter tls oper.

  Definition applyElementOnPatternTraces
             (ope: OutputPatternElement)
             (tr: Transformation)
             (sm: SourceModel)
             (sp: list SourceModelElement) (iter: nat) (tls: list TraceLink): list TargetModelLink :=
    flat_map (fun oper => 
      match (evalOutputPatternElementExpr sm sp iter ope) with 
      | Some l => optionToList (applyReferenceOnPatternTraces oper tr sm sp iter l tls)
      | None => nil
      end) (OutputPatternElement_getOutputElementReferences ope).

  Definition applyIterationOnPatternTraces (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) (tls: list TraceLink): list TargetModelLink :=
    flat_map (fun o => applyElementOnPatternTraces o tr sm sp iter tls)
      (Rule_getOutputPatternElements (SourceModelClass:=SourceModelClass) r).

  Definition applyRuleOnPatternTraces (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceModelElement) (tls: list (@TraceLink SourceModelElement TargetModelElement)): list TargetModelLink :=
    flat_map (fun i => applyIterationOnPatternTraces r tr sm sp i tls)
      (indexes (evalIteratorExpr r sm sp)).

  Definition applyPatternTraces (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (tls: list TraceLink): list TargetModelLink :=
    flat_map (fun r => applyRuleOnPatternTraces r tr sm sp tls) (matchPattern tr sm sp).

  Definition instantiateTraces (tr: Transformation) (sm : SourceModel) :=
    let tls := flat_map (tracePattern tr sm) (allTuplesByRule tr sm) in
      ( map (TraceLink_getTargetElement) tls, tls ).

  (** * Execute **)

  Definition applyTraces (tr: Transformation) (sm : SourceModel) (tls: list (@TraceLink SourceModelElement TargetModelElement)): list TargetModelLink :=
    flat_map (fun sp => applyPatternTraces tr sm sp tls) (map (TraceLink_getSourcePattern) tls).
    
  Definition executeTraces (tr: Transformation) (sm : SourceModel) : TargetModel :=
    let (elements, tls) := instantiateTraces tr sm in
    let links := applyTraces tr sm tls in
    Build_Model elements links.

End IterateTracesByRuleSemantics.