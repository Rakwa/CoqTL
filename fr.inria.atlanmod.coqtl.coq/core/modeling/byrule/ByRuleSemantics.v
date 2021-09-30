Require Import String.

Require Import core.utils.Utils.
Require Import core.modeling.Schema.
Require Import core.Graph.
Require Import Bool.
Require Import core.Syntax.
Require Import Arith.
Require Import Semantics.

Scheme Equality for list.

Section ByRuleSemantics.

Context {tc: TransformationConfiguration} {mtc: ModelingTransformationConfiguration tc}. 

Definition allNodesOfType (t: SourceModelClass) (sm: SourceModel) : list SourceNode :=
  filter (hasType t) (allNodes sm).

Definition allNodesOfTypes (l: list SourceModelClass) (sm: SourceModel): list (list SourceNode) :=
  map (fun t:SourceModelClass => allNodesOfType t sm) l.

Definition allTuplesOfTypes (l: list SourceModelClass) (sm: SourceModel): list (list SourceNode) := 
  fold_right prod_cons [nil] (allNodesOfTypes l sm).

Definition allTuplesByRule (tr: Transformation) (sm : SourceModel) :list (list SourceNode) :=
  (flat_map (fun (r:Rule) => allTuplesOfTypes (Rule_getInTypes r) sm) (Transformation_getRules tr)).

Definition execute (tr: Transformation) (sm : SourceModel) : TargetModel :=
  Build_Model
    (* elements *) (flat_map (instantiatePattern tr sm) (allTuplesByRule tr sm))
    (* links *) (flat_map (applyPattern tr sm) (allTuplesByRule tr sm)).

End ByRuleSemantics.
