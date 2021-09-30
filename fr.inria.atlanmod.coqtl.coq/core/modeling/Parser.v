Require Import String.

Require Import core.utils.Utils.
Require Import core.modeling.ModelingSchema.
Require Import core.Graph.
Require Import core.Syntax.
Require Import core.modeling.ConcreteExpressions.
Require Import core.modeling.ConcreteSyntax.
Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.

(* parse Concrete syntax into abstract syntax. *)

Section Parser.

Context {tc: TransformationConfiguration} {mtc: ModelingTransformationConfiguration tc}.

Definition parseOutputPatternEdge (intypes: list SourceGraphClass) (outtype: TargetGraphClass)
  (cr: ConcreteOutputPatternEdge intypes outtype): OutputPatternEdge :=
  buildOutputPatternEdge 
    (makeLink intypes outtype (ConcreteOutputPatternEdge_getRefType cr) (ConcreteOutputPatternEdge_getOutputPatternEdge cr)).

Definition parseOutputPatternNode (intypes: list SourceGraphClass) (co: ConcreteOutputPatternNode intypes) : OutputPatternNode :=
  buildOutputPatternNode
    (ConcreteOutputPatternNode_getName co)
    (makeNode intypes (ConcreteOutputPatternNode_getOutType co) (ConcreteOutputPatternNode_getOutPatternNode co))
    (map (parseOutputPatternEdge intypes (ConcreteOutputPatternNode_getOutType co)) (ConcreteOutputPatternNode_getOutputEdges co)).

Definition parseRule(cr: ConcreteRule) : Rule :=
  buildRule
    (ConcreteRule_getName cr)
    (match ConcreteRule_getGuard cr with
    | Some g => (makeGuard (ConcreteRule_getInTypes cr) g)
    | None => (makeEmptyGuard (ConcreteRule_getInTypes cr))
    end)
    (match ConcreteRule_getIteratedList cr with
    | Some i => (makeIterator (ConcreteRule_getInTypes cr) i)
    | None => (fun _ _ => Some 1)
    end)
    (map (parseOutputPatternNode (ConcreteRule_getInTypes cr)) (ConcreteRule_getConcreteOutputPattern cr)).

Definition parse(ct: ConcreteTransformation) : Transformation :=
  buildTransformation 
    (max (map (length (A:=SourceGraphClass)) (map ConcreteRule_getInTypes (ConcreteTransformation_getConcreteRules ct))   ))
    (map parseRule (ConcreteTransformation_getConcreteRules ct)).

End Parser.

