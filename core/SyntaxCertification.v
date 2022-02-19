Require Import core.Engine.
Require Import core.Syntax.
Require Import core.Semantics.
Require Import core.TransformationConfiguration.
Require Import core.Expressions.

Section SyntaxCertification.

Context {tc: TransformationConfiguration}.

Definition evalOutputPatternLinkExpr_wrapper 
  (sm: SourceModel) 
  (sp: list SourceModelElement) 
  (te: TargetModelElement) 
  (iter: nat)
  (l: list TraceLink) 
  (ope: OutputPatternElement)
  : option (list TargetModelLink) :=
(evalOutputPatternLinkExpr ope (resolveIter l) sm sp iter te).

Instance CoqTLSyntax :
  TransformationSyntax tc :=
  {
      (* syntax and accessors *)

      Transformation := Transformation;
      Rule := Rule;
      OutputPatternElement := OutputPatternElement;

      TraceLink := TraceLink;

      Transformation_getArity := Transformation_getArity;
      Transformation_getRules := Transformation_getRules;

      Rule_getOutputPatternElements := Rule_getOutputPatternElements;

      TraceLink_getSourcePattern := TraceLink_getSourcePattern;
      TraceLink_getIterator := TraceLink_getIterator;
      TraceLink_getName := TraceLink_getName;
      TraceLink_getTargetElement := TraceLink_getTargetElement;    
      
      evalOutputPatternElementExpr := evalOutputPatternElementExpr;
      evalIteratorExpr := evalIteratorExpr;
      evalOutputPatternLinkExpr := evalOutputPatternLinkExpr_wrapper;
      evalGuardExpr := evalGuardExpr;
  }.

End SyntaxCertification.