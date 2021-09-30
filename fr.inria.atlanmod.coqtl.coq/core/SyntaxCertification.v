Require Import core.Engine.
Require Import core.Syntax.
Require Import core.TransformationConfiguration.
Require Import core.Expressions.

Section SyntaxCertification.

Context {tc: TransformationConfiguration}.

Instance CoqTLSyntax :
  TransformationSyntax tc :=
  {
      (* syntax and accessors *)

      Transformation := Transformation;
      Rule := Rule;
      OutputPatternNode := OutputPatternNode;
      OutputPatternLink := OutputPatternLink;

      TraceLink := TraceLink;

      Transformation_getArity := Transformation_getArity;
      Transformation_getRules := Transformation_getRules;

      Rule_getOutputPatternNodes := Rule_getOutputPatternNodes;

      OutputPatternNode_getOutputLinks := OutputPatternNode_getOutputLinks;

      TraceLink_getSourcePattern := TraceLink_getSourcePattern;
      TraceLink_getIterator := TraceLink_getIterator;
      TraceLink_getName := TraceLink_getName;
      TraceLink_getTargetNode := TraceLink_getTargetNode;    
      
      evalOutputPatternNodeExpr := evalOutputPatternNodeExpr;
      evalIteratorExpr := evalIteratorExpr;
      evalOutputPatternLinkExpr := evalOutputPatternLinkExpr;
      evalGuardExpr := evalGuardExpr;
  }.

End SyntaxCertification.